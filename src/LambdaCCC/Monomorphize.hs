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

import HERMIT.Core (CoreDef(..),freeVarsExpr)
import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
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
   tweak = const "x"
           -- id

memoFloatLabelR :: Outputable a => Unop (TransformH a CoreExpr)
memoFloatLabelR r = do lab <- stashLabel
                       memoFloatR lab r

-- Build a dictionary for a given PredType, memoizing in the stash.
memoDict :: TransformH PredType CoreExpr
memoDict = memoR buildDictionaryT'

{--------------------------------------------------------------------
    Monomorphization
--------------------------------------------------------------------}

-- Unfold a name applied to some type and/or dictionary arguments
specializeTyDict :: ReExpr
specializeTyDict = tryR simplifyAll .
                   unfoldPredR (const (liftA2 (&&) (not.null) (all isTyOrDict)))

monomorphize :: ReExpr
monomorphize = memoFloatLabelR (repeatR specializeTyDict)

isTyOrDict :: CoreExpr -> Bool
isTyOrDict e = isType e || isDictTy (exprType e)

mySimplifiers :: [ReExpr]
mySimplifiers = [ castFloatAppR    -- or castFloatAppR'
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
  , nowatchR "(caseReduceIdR True)" (caseReduceIdR True)
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

-- x = (let y = e in y)  ==>  x = e
bindUnLetIntroR :: ReBind
bindUnLetIntroR =
  do NonRec x (Let (NonRec y e) (Var ((== y) -> True))) <- id
     return (NonRec x e)

-- | Float a let out of a case alternative:
-- 
--   case foo of { ... ; p -> let x = u in v ; ... }  ==>
--   let x = u in case foo of { ... ; p -> v ; ... }
-- 
-- where no variable in `p` occurs freely in `u`, and where `x` is not one of
-- the variables in `p`.
letFloatCaseAltR :: ReExpr
letFloatCaseAltR =
  do Case scrut w ty alts <- id
     (b,alts') <- letFloatOneAltR alts
     return $ Let b (Case scrut w ty alts')

-- Perform the first safe let-floating out of a case alternative
letFloatOneAltR :: [CoreAlt] -> TransformH x (CoreBind,[CoreAlt])
letFloatOneAltR [] = fail "no alternatives safe to let-float"
letFloatOneAltR (alt:rest) =
  (do (bind,alt') <- letFloatAltR alt
      return (bind,alt':rest))
  <+
  (second (alt :) <$> letFloatOneAltR rest)

-- (p -> let bind in e) ==>  (bind, p -> e)
letFloatAltR :: CoreAlt -> TransformH x (CoreBind,CoreAlt)
letFloatAltR (con,vs,Let bind@(NonRec x a) body)
  | isEmptyVarSet (vset `intersectVarSet` freeVarsExpr a)
    && not (x `elemVarSet` vset)
  = return (bind,(con,vs,body))
 where
   vset = mkVarSet vs
letFloatAltR _ = fail "letFloatAltR: not applicable"

-- TODO: consider variable occurrence conditions more carefully

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
    -- 
    , externC "cast-float-app'" castFloatAppR' "cast-float-app with transitivity"
    ]
