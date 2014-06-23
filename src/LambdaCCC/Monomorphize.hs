{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Monomorphize
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Transform away all non-standard types
----------------------------------------------------------------------

module LambdaCCC.Monomorphize where

-- TODO: explicit exports

import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.),(>>>))
import Control.Arrow (arr,second)
import Control.Monad ((<=<),unless)
import Data.Functor ((<$),(<$>))
import Control.Applicative (liftA2)
import Data.Monoid (mempty)
import Data.List (intercalate,isPrefixOf)
import qualified Data.Set as S

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Core (CoreDef(..))
import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External,ExternalName,external,(.+),CmdTag(Loop))
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad (saveDef,newIdH,Label)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT)
import qualified HERMIT.Extras as Ex

import LambdaCCC.Misc ((<~))

import qualified LambdaCCC.CoreEncode as CE

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False

#define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error

#else
-- watchR :: String -> Unop ReExpr
-- watchR lab r = labeled observing (lab,r) >>> lintExprR  -- Fail softly on core lint error.
watchR, nowatchR :: Injection a CoreTC => String -> RewriteH a -> RewriteH a
watchR lab r = labeled observing (lab,r)  -- don't lint

#endif

nowatchR = watchR
-- nowatchR _ = id

skipT :: Monad m => Transform c m a b
skipT = fail "untried"

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

-- Tighten the type of (>>). (Alternatively, choose a different operator.)
infixl 1 >>
(>>) :: Monad m => m () -> m b -> m b
(>>) = (Prelude.>>)

-- Turn filters into conditional identities and vice versa.
-- Is this functionality already in HERMIT?

passT :: Monad m => Transform c m a () -> Rewrite c m a
passT t = t >> id

unpassT :: Functor m => Rewrite c m a -> Transform c m a ()
unpassT r = fmap (const ()) r

-- | case e of { Con -> rhs }  ==>  rhs
-- Warning: can gain definedness when e == _|_.
caseNoVarR :: ReExpr
caseNoVarR =
  do Case _ _ _ [(DataAlt _,[],rhs)] <- id
     return rhs

#if 0
bragMemo :: Bool
bragMemo = True -- observing

-- Memoize a transformation. Don't introduce a let binding (for later floating),
-- which would interfere with additional simplification.
memoR :: Outputable a => Unop (TransformH a CoreExpr)
memoR r = do lab <- stashLabel
             findDefT bragMemo lab
               <+ do e' <- r
                     saveDefNoFloatT bragMemo lab $* e'
                     return e'

memoFloatR :: Outputable a => Label -> Unop (TransformH a CoreExpr)
memoFloatR lab r = do findDefT bragMemo lab
                        <+ do e' <- r
                              v <- newIdT lab' $* exprType' e'
                              saveDefT bragMemo lab $* Def v e'
                              letIntroR lab' $* e'
 where
   lab' = tweak lab
   tweak = -- fst . break (== '$')
           ("s:" ++) . fst . break (== '_')
           -- const "x"
           -- id
#endif

memoFloatLabelR :: Outputable a => Unop (TransformH a CoreExpr)
memoFloatLabelR r = do lab <- stashLabel
                       CE.memoFloatR lab r

-- Build a dictionary for a given PredType, memoizing in the stash.
memoDict :: TransformH PredType CoreExpr
memoDict = CE.memoR buildDictionaryT'

{--------------------------------------------------------------------
    Monomorphization
--------------------------------------------------------------------}

-- Unfold a name applied to some type and/or dictionary arguments
specializeTyDict :: ReExpr
specializeTyDict = tryR simplifyAll .
                   unfoldPredR (const (liftA2 (&&) (not.null) (all isTyOrDict)))

isTyOrDict :: CoreExpr -> Bool
isTyOrDict e = isType e || isDictTy (exprType e)

monomorphize :: ReExpr
monomorphize = memoFloatLabelR (repeatR specializeTyDict)

{--------------------------------------------------------------------
    Simplification
--------------------------------------------------------------------}

mySimplifiers :: [ReExpr]
mySimplifiers = [ castFloatAppR    -- or castFloatAppR'
                , CE.letElimTrivialR  -- instead of letNonRecSubstSafeR
                ]

#define ReplaceBash

simplifyAll :: ReExpr

simplifiers :: [ReExpr]
simplifiers =
  mySimplifiers
#ifdef ReplaceBash
  ++ bashSimplifiers

-- From bashComponents.
bashSimplifiers :: [ReExpr]
bashSimplifiers =
  [ nowatchR "betaReduceR" betaReduceR
  , nowatchR "(caseReduceR True)" (caseReduceR True)
  , nowatchR "(caseReduceUnfoldR True)" (caseReduceUnfoldR True)
  , nowatchR "caseElimSeqR" caseElimSeqR
  , nowatchR "unfoldBasicCombinatorR" unfoldBasicCombinatorR
  , nowatchR "inlineCaseAlternativeR" inlineCaseAlternativeR
  , nowatchR "etaReduceR" etaReduceR
  -- letNonRecSubstSafeR was replicating some monomorphic method
  -- specializations.
  -- , nowatchR "letNonRecSubstSafeR" letNonRecSubstSafeR
  , nowatchR "caseFloatAppR" caseFloatAppR
  , nowatchR "caseFloatCaseR" caseFloatCaseR
  , nowatchR "caseFloatLetR" caseFloatLetR
  -- , nowatchR "caseFloatCastR" caseFloatCastR  -- Watch this one
  , nowatchR "letFloatAppR" letFloatAppR
  , nowatchR "letFloatArgR" letFloatArgR
  , nowatchR "letFloatLamR" letFloatLamR
  , nowatchR "letFloatLetR" letFloatLetR
  , nowatchR "letFloatCaseR" letFloatCaseR
  , nowatchR "letFloatCastR" letFloatCastR
  , nowatchR "castElimReflR" castElimReflR
  , nowatchR "castElimSymR" castElimSymR
  ]

simplifyAll = watchR "simplifyAll" $
              bashUsingE (promoteR <$> simplifiers)

#else

simplifyAll = watchR "simplifyAll" $
              bashExtendedWithE (promoteR <$> simplifiers)

#endif

simplifyAllRhs :: ReProg
simplifyAllRhs = progRhsAnyR simplifyAll

letFloatR :: ReCore
letFloatR = promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR)

pass :: ReCore
pass = tryR unshadowR
     . tryR (promoteR simplifyAllRhs)
     . tryR (anybuR letFloatR)
     . tryR (anybuR (promoteR bindUnLetIntroR))
     . onetdR (promoteR monomorphize)

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "simplifyAll" simplifyAll "Bash with normalization simplifiers (no inlining)"
    , externC "simplifyAllRhs" simplifyAllRhs "simplify-all on all top-level RHSs"
    , externC "specializeTyDict" specializeTyDict "..."
    , externC "bindUnLetIntroR" bindUnLetIntroR "..."
    , externC "letFloatCaseAltR" letFloatCaseAltR "..."
    , externC "monomorphize" monomorphize "..."
    , external "let-float'"
        (promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR)
         :: RewriteH Core)
        ["let-float with letFloatCaseAltR"]
    , external "pass" pass ["..."]
    ]
    ++ CE.externals
