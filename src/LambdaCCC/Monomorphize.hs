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

bragMemo :: Bool
bragMemo = observing

-- Memoize a transformation. Don't introduce a let binding (for later floating),
-- which would interfere with additional simplification.
memoR :: Outputable a => Unop (TransformH a CoreExpr)
memoR r = do lab <- stashLabel
             findDefT bragMemo lab
               <+ do e' <- r
                     saveDefNoFloatT bragMemo lab $* e'
                     return e'

-- Memoize and float if non-trivial
memoFloatR :: Outputable a => Label -> Unop (TransformH a CoreExpr)
memoFloatR lab r = do findDefT bragMemo lab
                        <+ do e' <- r
                              if exprIsTrivial e' then
                                do saveDefNoFloatT bragMemo lab $* e'
                                   return e'
                               else
                                do v <- newIdT lab' $* exprType' e'
                                   saveDefT bragMemo lab $* Def v e'
                                   letIntroR lab' $* e'
 where
   lab' = tweak lab
   tweak = -- fst . break (== '$')
           -- ("s:" ++) . fst . break (== '_')
           fst . break (== '_')
           -- const "x"
           -- id

-- TODO: Refactor

memoFloatLabelR :: Outputable a => Unop (TransformH a CoreExpr)
memoFloatLabelR r = do lab <- stashLabel
                       memoFloatR lab r

filterToBool :: MonadCatch m => Transform c m a () -> Transform c m a Bool
filterToBool t = (t >> return True) <+ return False

-- Build a dictionary for a given PredType.
memoDict :: TransformH PredType CoreExpr
memoDict = memoR buildDictionaryT'

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
                , letElimTrivialR  -- instead of letNonRecSubstSafeR
                ]

#define ReplaceBash

simplifyAll  :: ReExpr
simplifyAll' :: ReExpr

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

simplifyAll' = watchR "simplifyAll" $
               bashUsingE (promoteR <$> (letSubstOneOccR : simplifiers))

#else

simplifyAll = watchR "simplifyAll" $
              bashExtendedWithE (promoteR <$> simplifiers)

simplifyAll' = watchR "simplifyAll" $
               bashExtendedWithE (promoteR <$> (letSubstOneOccR : simplifiers))

#endif

simplifyAllRhs :: ReProg
simplifyAllRhs = progRhsAnyR simplifyAll

letFloatR :: ReCore
letFloatR = promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR)

pruneAltsProg :: ReProg
pruneAltsProg = progRhsAnyR ({-bracketR "pruneAltsR"-} pruneAltsR)

passCore :: ReCore
passCore = tryR (promoteR simplifyAllRhs)
         . tryR (anybuR letFloatR)
         . tryR (anybuR (promoteR bindUnLetIntroR))
         . tryR (promoteR pruneAltsProg)
         . tryR unshadowR
         . onetdR (promoteR monomorphize)

-- NOTE: if unshadowR is moved to later than pruneAltsProg, we can prune too
-- many alternatives. TODO: investigate.

passE :: ReExpr
passE = id
      . tryR simplifyAll'  -- after let floating
      . tryR (anybuE (letFloatExprR <+ letFloatCaseAltR))
      . tryR (anybuE (letAllR bindUnLetIntroR id))
      . tryR pruneAltsR
      . tryR (extractR unshadowR)
      . onetdE monomorphize

-- | 'letSubstR' in non-recursive let if only one occurrence.
letSubstOneOccR :: ReExpr
letSubstOneOccR = oneOccT >> letNonRecSubstR

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "simplifyAll" simplifyAll "Bash with normalization simplifiers (no inlining)"
    , externC "simplifyAll'" simplifyAll' "simplifyAll plus letSubstOneOccR"
    , externC "simplifyAllRhs" simplifyAllRhs "simplify-all on all top-level RHSs"
    , externC "specializeTyDict" specializeTyDict "..."
    , externC "bindUnLetIntroR" bindUnLetIntroR "..."
    , externC "letFloatCaseAltR" letFloatCaseAltR "..."
    , externC "monomorphize" monomorphize "..."
    , external "passCore" passCore ["..."]
    , externC "passE" passE "..."
    , externC "letSubstOneOccR" letSubstOneOccR "..."
    -- 
    , external "let-float'"
        (promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR)
         :: RewriteH Core)
        ["let-float with letFloatCaseAltR"]
    , externC "pruneAltsR" pruneAltsR "..."
    , externC "pruneAltsProg" pruneAltsProg "..."
    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    ]
