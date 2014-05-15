{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

-- TODO: Cull pragmas

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Standard
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Transform away all non-standard types
----------------------------------------------------------------------

module LambdaCCC.Standard where

-- TODO: explicit exports
import Prelude hiding (id,(.))

import Control.Category (id,(.),(>>>))
import Data.Functor ((<$>))
import Control.Monad ((=<<))

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
import HERMIT.External (External,external,ExternalName)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad (newIdH)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import LambdaCCC.Misc ((<~))

import HERMIT.Extras hiding (findTyConT, labeled)
import qualified HERMIT.Extras as Ex

import LambdaCCC.Reify (unCallE1, caseSizedR)

-- TODO: Cull imports

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

#if 0
-- From hermit-syb. (Changed comment.)

-- | Apply a 'Rewrite' in a top-down manner, succeeding if any succeed.
smarttdR :: RewriteH Core -> RewriteH Core
smarttdR r = modFailMsg ("smarttdR failed: " ++) $ go where
  go = r <+ go'
  go' = do
    ExprCore e <- idR
    case e of
      Var _ -> fail "smarttdR Var"
      Lit _ -> fail "smarttdR Let"
      App _ _ -> pathR [App_Fun] go <+ pathR [App_Arg] go
      Lam _ _ -> pathR [Lam_Body] go
      Let (NonRec _ _) _ -> pathR [Let_Body] go <+ pathR [Let_Bind,NonRec_RHS] go
      Let (Rec bs) _ -> pathR [Let_Body] go <+ foldr (<+) (fail "smarttdR Let Rec") [ pathR [Let_Bind, Rec_Def i, Def_RHS] go
                                                                                    | (i, _) <- zip [0..] bs]
      Case _ _ _ as -> pathR [Case_Scrutinee] go <+ foldr (<+) (fail "smarttdR Case") [pathR [Case_Alt i, Alt_RHS] go | (i, _) <- zip [0..] as]
      Cast _ _ -> pathR [Cast_Expr] go
      Tick _ _ -> pathR [Tick_Expr] go
      Type _ -> fail "smarttdR Type"
      Coercion _ -> fail "smarttdR Coercion"

#endif

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False

-- observeR' :: InCoreTC t => String -> RewriteH t
-- observeR' = Ex.observeR' observing

-- triesL :: InCoreTC t => [(String,RewriteH t)] -> RewriteH t
-- triesL = Ex.triesL observing

labelR :: InCoreTC t => String -> RewriteH t -> RewriteH t
labelR = curry (Ex.labeled observing)

{--------------------------------------------------------------------
    Standard types
--------------------------------------------------------------------}

-- A "standard type" is built up from `Unit`, `Bool`, `Int` (for now), pairs (of
-- standard types), sums, and functions, or Encode

standardTyT :: Type -> TransformU ()
standardTyT (tcView -> Just ty) = standardTyT ty
standardTyT (TyConApp tc args) | standardTC tc
                               = mapM_ standardTyT args
#if 0
standardTyT ty@(TyConApp tc _) =
  -- Treat Encode applications as standard.
  do encodeTC <- findTyConT "LambdaCCC.Encode.Encode"
     if tc == encodeTC then successT else nonStandardFail ty
#endif
standardTyT (FunTy arg res) =
  standardTyT arg >> standardTyT res
standardTyT ty = nonStandardFail ty

nonStandardFail :: Type -> TransformU ()
nonStandardFail ty =
  do s <- showPprT ty
     fail ("non-standard type:\n" ++ s)

-- TODO: Maybe use coreView instead of tcView? I think it's tcView we want,
-- since it just looks through type synonyms and not newtypes.

-- TODO: Since I removed Encode, standardTy can be Type -> Bool

standardTC :: TyCon -> Bool
standardTC tc =
     (tc `elem` [unitTyCon, boolTyCon, intTyCon])
  || isPairTC tc
  || tyConName tc == eitherTyConName    -- no eitherTyCon

isPairTC :: TyCon -> Bool
isPairTC tc = isBoxedTupleTyCon tc && tupleTyConArity tc == 2

-- TODO: Parametrize the rest of the module by 'standardTyT'.

-- TODO: Consider how to eliminate Encode as well. Then simplify to
-- standardTy :: Type -> Bool

type FilterE = TransformH CoreExpr ()

nonTypeE :: FilterE
nonTypeE = notM (typeT idR)

nonStandardE :: FilterE
nonStandardE = nonTypeE >> notM ((standardTyT . exprType') =<< idR)

isVarT :: TransformH CoreExpr ()
isVarT = do Var _ <- idR
            successT

-- Inline names with non-standard types
inlineNon :: ReExpr
inlineNon = labelR "inlineNon" $
            isVarT >> nonStandardE >> inlineR

-- I added isVarT to reduce the calls to nonStandardE.
-- TODO: Try without as well, and compare times.

-- Beta reduce if doing so removes a non-standard type.
betaReduceNon :: ReExpr
betaReduceNon = labelR "betaReduceNon" $
                appT id nonStandardE (const id) >>
                betaReduceR

-- Let-substitute if doing so removes a non-standard type.
letSubstNon :: ReExpr
letSubstNon = labelR "letSubstNon" $
  letT (nonRecT id nonStandardE (const id)) successT (const id) >>
  letSubstR

bashExtendedWithE :: [ReExpr] -> ReExpr
bashExtendedWithE rs = extractR (bashExtendedWithR (promoteR <$> rs))

caseSized :: ReExpr
caseSized = labelR "caseSized" $
            caseSizedR >>> tryR (caseReduceR True)

stdRuleNames :: [String]
stdRuleNames = ["unTreeZ'/L","unTreeS'/B"]

stdRules :: ReExpr
stdRules = rulesR stdRuleNames >>> cleanupUnfoldR

-- "unTreeZ'/L" forall a . unTreeZ' (L a) = a
-- "unTreeS'/B" forall p . unTreeS' (B p) = p

-- These rules don't fire, perhaps due to wrapper loss.
-- For now, code them directly.
-- Perhaps for the same reason, I can't unCallE1 "L".

unL :: ReExpr
unL = do (Var f,[_sn,Type _a,_co, a]) <- callT
         guardMsg (uqVarName f == "L") "Not an L"
         return a

unB :: ReExpr
unB = do (Var f,[_sn,Type _a,_sm,_co, p]) <- callT
         guardMsg (uqVarName f == "B") "Not a B"
         return p

unPair :: ReExpr
unPair = do (Var f,[Type _a,p,q]) <- callT
            guardMsg (uqVarName f == ":#") "Not a (:#)"
            return (mkCoreTup [p,q])

-- TODO: Refactor
-- TODO: Get the GHC rules working

unUnTreeZL :: ReExpr
unUnTreeZL = labelR "unUnTreeZL" $
             unL . unCallE1 "unTreeZ'"

unUnTreeSB :: ReExpr
unUnTreeSB = labelR "unUnTreeSB" $
             unB . unCallE1 "unTreeS'"

unUnPairPair :: ReExpr
unUnPairPair = labelR "unUnPairPair" $
               unPair . unCallE1 "unPair'"

unRanCo :: Coercion -> Maybe Coercion
unRanCo (TyConAppCo _role tc [Refl Representational _,ranCo])
  | isFunTyCon tc = Just ranCo
unRanCo _ = Nothing

-- TODO: Should I check the role?

-- cast (\ v -> e) (<t>_R -> co) ==> (\ v -> cast e co)
lamFloatCastR :: ReExpr
lamFloatCastR = do Cast (Lam v e) (unRanCo -> Just co) <- idR
                   return (Lam v (Cast e co))

-- cast (cast e co) co' ==> cast e (mkTransCo co co')
castCastR :: ReExpr
castCastR = do (Cast (Cast e co) co') <- idR
               return (Cast e (mkTransCo co co'))

rewrites :: [ReExpr]
rewrites = [ betaReduceNon
           , letSubstNon
           , inlineNon
           , labelR "castFloatAppR"  castFloatAppR
           , labelR "castCastR"  castCastR
           , labelR "lamFloatCastR"  lamFloatCastR
           , labelR "caseReduceR" (caseReduceR True)
           , labelR "caseFloatR" caseFloatR
           , labelR "caseFloatArgR" (caseFloatArgR Nothing Nothing) -- ignore strictness
           , caseSized  -- after caseFloatCaseR & caseReduceR
           , unUnTreeZL, unUnTreeSB, unUnPairPair
           -- , stdRules   -- they don't match
           ]

-- standardize :: ReExpr
-- standardize = foldr (<+) (fail "standardize: nothing to do here") rewrites

-- deepS :: ReExpr
-- deepS = anytdE (repeatR standardize)

bashStandardize :: ReExpr
bashStandardize = bashExtendedWithE rewrites

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "inline-non" inlineNon "Inline var of non-standard type"
    , externC "beta-reduce-non" betaReduceNon "Beta reduce if doing so removes a non-standard type"
    , externC "let-subst-non" letSubstNon "let-subst if doing so removes a non-standard type"
    , externC "case-sized" caseSized "Case with type-sized scrutinee"
    , externC "standard-rules" stdRules "Apply some rules"
    , externC "bash-standardize" bashStandardize "bash with non-standard type removal"
    , externC "untreezl" unUnTreeZL "unTreeZ'/L"
    , externC "untreesb" unUnTreeSB "unTreeS'/B"
    , externC "ununpairpair" unUnPairPair "unPair'/(:#)"
    , externC "simplify-expr" simplifyExprT "Invoke GHC's simplifyExpr"
    , externC "lam-float-cast" lamFloatCastR "Float lambda through case"
    , externC "cast-cast" castCastR "Coalesce nested casts"
    ]

--     , externC "standardize" standardize "Transform away non-standard types"
--     , externC "deep-standardize" deepS "Top-down standardize"
--     , external "smart-td" smarttdR ["..."]
--     , externC "unL" unL "drop an L"
