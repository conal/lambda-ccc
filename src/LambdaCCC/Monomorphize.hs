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
-- Monomorphization plugin
----------------------------------------------------------------------

module LambdaCCC.Monomorphize where

-- TODO: explicit exports

import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.),(>>>))
import Control.Arrow (arr,second)
import Control.Monad ((<=<),unless)
import Data.Functor ((<$),(<$>),void)
import Control.Applicative (liftA2)
import Data.Monoid (mempty)
import Data.List (intercalate,isPrefixOf)

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Core (CoreDef(..))
import HERMIT.Context (HermitC)
import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External,ExternalName,external,(.+),CmdTag(Loop))
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad (saveDef,RememberedName(..))
import HERMIT.Name (newIdH)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT)
import qualified HERMIT.Extras as Ex

import LambdaCCC.Misc ((<~))
import LambdaCCC.CoerceEncode
import LambdaCCC.ReifySimple

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False

-- #define LintDie

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
bragMemo = False

-- Memoize a transformation. Don't introduce a let binding (for later floating),
-- which would interfere with additional simplification.
memoR :: Outputable a => Unop (TransformH a CoreExpr)
memoR r = do lab <- stashLabel
             findDefT bragMemo lab
               <+ do e' <- r
                     saveDefNoFloatT bragMemo lab $* e'
                     return e'

-- Memoize and float if non-trivial
memoFloatR :: Outputable a => String -> Unop (TransformH a CoreExpr)
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

-- -- Build a dictionary for a given PredType.
-- memoDict :: TransformH PredType CoreExpr
-- memoDict = memoR buildDictionaryT'

{--------------------------------------------------------------------
    Monomorphization
--------------------------------------------------------------------}

-- Unfold a name applied to some type and/or dictionary arguments
specializeTyDict :: ReExpr
specializeTyDict = tryR simplifyAll . unfoldPredR okay
 where
   okay = -- const $ liftA2 (&&) (not.null) (all isTyOrDict)
          -- (\ v args -> isGlobalId v && not (isPrimitive v) && all isTyOrDict args)
          (\ v args -> not (isPrimitive v) && all isTyOrDict args
                    && (isGlobalId v || not (null args)))
          -- const $ all isTyOrDict

isTyOrDict :: CoreExpr -> Bool
isTyOrDict e = isType e || isDictTy (exprType e)

monomorphize :: ReExpr
monomorphize = memoFloatLabelR (repeatR specializeTyDict)

{--------------------------------------------------------------------
    Simplification
--------------------------------------------------------------------}

replaceBash :: Bool
replaceBash = True

bashWith :: [ReExpr] -> ReExpr
bashWith
  | replaceBash = \ rs -> bashUsingE (promoteR <$> (rs ++ bashSimplifiers))
  | otherwise   = \ rs -> bashExtendedWithE (promoteR <$> rs)

simplifyAll :: ReExpr
simplifyAll = watchR "simplifyAll" $
              bashWith mySimplifiers

simplifyAll' :: ReExpr
simplifyAll' = watchR "simplifyAll'" $
               bashWith (letSubstOneOccR : mySimplifiers)


mySimplifiers :: [ReExpr]
mySimplifiers = [ castFloatAppUnivR    -- or castFloatAppR'
                , castCastR
                , castTransitiveUnivR
                , letSubstTrivialR  -- instead of letNonRecSubstSafeR
             -- , letSubstOneOccR -- delay
                -- Experiment
--                 , standardizeCase
--                 , standardizeCon
                -- Previous two lead to nontermination. Investigate.
                ]

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
  , nowatchR "caseFloatCastR" caseFloatCastR  -- Watch this one
  , nowatchR "letFloatAppR" letFloatAppR
  , nowatchR "letFloatArgR" letFloatArgR
  , nowatchR "letFloatLamR" letFloatLamR
  , nowatchR "letFloatLetR" letFloatLetR
  , nowatchR "letFloatCaseR" letFloatCaseR
  , nowatchR "letFloatCastR" letFloatCastR
  , nowatchR "castElimReflR" castElimReflR
  , nowatchR "castElimSymR" castElimSymR
  ]

-- TODO: Trim redundant let floating. See passCore and passE.

simplifyAllRhs :: ReProg
simplifyAllRhs = progRhsAnyR simplifyAll

simplifyAllRhs' :: ReProg
simplifyAllRhs' = progRhsAnyR simplifyAll'

simplifyAllBind' :: ReBind
simplifyAllBind' = nonRecAllR id simplifyAll'

letFloatCaseAltR' :: ReExpr
letFloatCaseAltR' = letFloatCaseAltR Nothing

letFloatR :: ReCore
letFloatR = promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR')

pruneAltsProg :: ReProg
pruneAltsProg = progRhsAnyR ({-bracketR "pruneAltsR"-} pruneAltsR)

retypeProgR :: ReProg
retypeProgR = progRhsAnyR ({-bracketR "retypeExprR"-} retypeExprR)

passCore :: ReCore
passCore = tryR (promoteR simplifyAllRhs)  -- after let-floating
         . tryR (anybuR letFloatR)
         . tryR (anybuR (promoteR bindUnLetIntroR))
         . tryR (promoteR retypeProgR) -- pruneAltsProg
         . tryR unshadowR
         . onetdR (promoteR monomorphize)

-- NOTE: if unshadowR is moved to later than pruneAltsProg, we can prune too
-- many alternatives. TODO: investigate.

passE :: ReExpr
passE = id
      . tryR simplifyAll  -- after let floating
      . tryR (anybuE (letFloatExprR <+ letFloatCaseAltR'))
      . tryR (anybuE (letAllR bindUnLetIntroR id))
      . tryR (watchR "retypeExprR" retypeExprR)
      . tryR (extractR unshadowR)
      . onetdE monomorphize

-- TODO: Find a much more efficient strategy. I think repeated onetdE is very
-- expensive. I went this way to help memoization. Revisit!

-- | 'letSubstR' in non-recursive let if only one occurrence.
letSubstOneOccR :: ReExpr
letSubstOneOccR = oneOccT >> letNonRecSubstR

standardizeR' :: (Standardizable a, SyntaxEq a, Injection a CoreTC) => RewriteH a
standardizeR' = watchR "standardizeR" $
                standardizeR

{--------------------------------------------------------------------
    Yet another go at standardizing types
--------------------------------------------------------------------}

isStandardTy :: Type -> Bool
isStandardTy t = any ($ t) [isUnitTy,isBoolTy,isIntTy,isPairTy]

-- | e ==> abst (repr e).  In Core, abst is
-- abst ty $hasRepTy ty' (Eq# * ty' (Rep ty) (sym (co :: Rep ty ~ ty'))),
-- where e :: ty, and co normalizes Rep ty to ty'.
abstReprR :: ReExpr
abstReprR =
  do e <- id
     let ty = exprType e
     hasRepTc <- findTyConT (repName "HasRep")
     dict <- buildDictionaryT' $* TyConApp hasRepTc [ty]
     repTc <- findTyConT (repName "Rep")
     (co,ty') <- normaliseTypeT Nominal $* TyConApp repTc [ty]
     let eqBox = mkEqBox (mkSymCo co)
         meth str ex = apps' (repName str) [ty] [dict,Type ty',eqBox,ex]
     (meth "abst" <=< meth "repr") e

-- Do one unfolding, and then a second one only if the function name starts with
-- "$", as in the case of a method lifted to the top level.
unfoldMethodR :: ReExpr
unfoldMethodR =
    tryR (tryR simplifyAll . unfoldPredR (\ v _ -> isPrefixOf "$" (uqVarName v)))
  . (tryR simplifyAll . unfoldR)

-- unfoldMethodR = repeatR (tryR simplifyAll . unfoldR)

standardizeCase :: ReExpr
standardizeCase =
     caseReduceR True
  <+ caseFloatCaseR
  <+ onScrutineeR (unfoldMethodR . abstReprR)

onScrutineeR :: Unop ReExpr
onScrutineeR r = caseAllR r id id (const id)

standardizeCon :: ReExpr
standardizeCon =
  -- Handle both saturated and unsaturated constructors
     (appAllR id unfoldMethodR . (void callDataConT >> abstReprR))
  <+ (lamAllR id standardizeCon . etaExpandR "eta")

{--------------------------------------------------------------------
    Combine steps
--------------------------------------------------------------------}

-- TODO: Move elsewhere

reifyPrep :: ReExpr
reifyPrep = inReify (
                id
              . tryR unshadowE
              . tryR simplifyAll'
              . tryR (anytdE (repeatR (standardizeCase <+ standardizeCon)))
              . tryR simplifyAll'
              . tryR (repeatR passE)
              )
        -- . tryR (unfoldNameR "LambdaCCC.Run.go")

-- I tried moving standardizeCase and standardizeCon into mySimplifiers (used by
-- simplifyAll'), and it appears to loop. To do: investigate. Meanwhile, do it here.

-- TODO: The initial inlineR is probably inadequate. Instead, fix the inlining
-- criterion in specializeTyDict.

doReify :: ReExpr
doReify = tryR unshadowE
        . tryR bashE
        . repeatR (anytdE (repeatR reifyMisc))

compileGo :: ReExpr
compileGo = doReify . reifyPrep


-- Move to HERMIT.Extras
unshadowE :: ReExpr
unshadowE = extractR unshadowR

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
    , externC "simplifyAllRhs'" simplifyAllRhs' "simplify-all' on all top-level RHSs"
    , externC "simplifyAllBind'" simplifyAllBind' "simplify-all' on all binding RHS"
    , externC "specializeTyDict" specializeTyDict "..."
    , externC "bindUnLetIntroR" bindUnLetIntroR "..."
    , externC "letFloatCaseAltR'" letFloatCaseAltR' "..."
    , externC "monomorphize" monomorphize "..."
    , external "passCore" passCore ["..."]
    , externC "passE" passE "..."
    , externC "letSubstOneOccR" letSubstOneOccR "..."
    , externC "standardizeExpr" (standardizeR' :: ReExpr) "..."
    , externC "standardizeProg" (standardizeR' :: ReProg) "..."
    , externC "standardizeBind" (standardizeR' :: ReBind) "..."
    -- Put it together
    , externC "reify-prep" reifyPrep "..."
    , externC "do-reify" doReify "..."
    , externC "compile-go" compileGo "..."
    -- TEMP:
    , externC "abstReprR" abstReprR "..."
    , externC "standardizeCase" standardizeCase "..."
    , externC "standardizeCon" standardizeCon "..."
    -- From Reify.
    , externC "reify-misc" reifyMisc "Simplify 'reify e'"
    , externC "reifyRepMeth" reifyRepMeth "..."
    -- 
    , external "let-float'"
        (promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR')
         :: RewriteH Core)
        ["let-float with letFloatCaseAltR"]
    , externC "pruneAltsR" pruneAltsR "..."
    , externC "pruneAltsProg" pruneAltsProg "..."
    , externC "retypeExprR" retypeExprR "..."
    , externC "retypeProgR" retypeProgR "..."
    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    , externC "cast-float-app'" castFloatAppR' "cast-float-app with transitivity"
    , externC "castFloatAppUnivR" castFloatAppUnivR "cast-float-app with coercion cheating"
    , externC "case-wild" caseWildR "case of wild ==> let (doesn't preserve evaluation)"
    , externC "cast-cast" castCastR "..."
    , externC "cast-transitive-univ" castTransitiveUnivR "..."
    ]
