{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

-- #define SizedTypes

module LambdaCCC.Standard where

-- TODO: explicit exports
import Prelude hiding (id,(.))

import Control.Category (id,(.))
import Control.Arrow (arr)
import Data.Functor ((<$>))

-- GHC
import PrelNames (eitherTyConName)

-- import HERMIT.Context
-- import HERMIT.Core
import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
import HERMIT.External (External)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT, labeled)
import qualified HERMIT.Extras as Ex

#ifdef SizedTypes
import LambdaCCC.Reify (unCallE1, caseSizedR)
#endif

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

-- Move to HERMIT.Extras

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = True

labelR :: InCoreTC t => String -> RewriteH t -> RewriteH t
labelR = curry (Ex.labeled observing)

{--------------------------------------------------------------------
    Standard types
--------------------------------------------------------------------}

-- TODO: Parametrize the rest of the module by 'standardTyT'.

-- TODO: Consider how to eliminate Encode as well. Then simplify to
-- standardTy :: Type -> Bool

-- A "standard type" is built up from `Unit`, `Bool`, `Int` (for now), pairs (of
-- standard types), sums, and functions, or Encode

standardTyT :: Type -> TransformU ()
standardTyT _ | trace "standardTyT" False = undefined
standardTyT (tcView -> Just ty) = standardTyT ty
standardTyT (TyConApp tc args) | standardTC tc
                               = mapM_ standardTyT args
#if 1
standardTyT ty@(TyConApp tc _) =
  -- Treat Encode applications as standard.
  do encodeTC <- findTyConT "LambdaCCC.Encode.Encode"
     if tc == encodeTC then successT else nonStandardFail ty
#endif
standardTyT (FunTy arg res) =
  standardTyT arg >> standardTyT res
standardTyT ty = nonStandardFail ty

nonStandardFail :: Type -> TransformU a
nonStandardFail ty =
  do s <- showPprT ty
     fail ("non-standard type:\n" ++ s)

-- TODO: Maybe I just want a standard outer shell.

-- TODO: Maybe use coreView instead of tcView? I think it's tcView we want,
-- since it just looks through type synonyms and not newtypes.

-- TODO: If I remove Encode, standardTy can be Type -> Bool

nonStandardTyT :: TransformH Type ()
nonStandardTyT = catchesM [reView,tcApp,fun]
 where
   reView = nonStandardTyT . tcViewT
   tcApp = do TyConApp tc _args <- idR      -- use tyConAppT
              encodeTC <- findTyConT "LambdaCCC.Encode.Encode"
              guardMsg (not (tc == encodeTC || standardTC tc)) "standard tycon"
              -- Could alternatively check nonStandardTyT for args
              successT
   fun = funTyT successT successT (const (const ()))
   -- Alternatively, probe into domain and range:
   -- fun = funTyT nonStandardTyT successT (const (const ()))
   --    <+ funTyT successT nonStandardTyT (const (const ()))

standardTC :: TyCon -> Bool
standardTC tc =
     (tc `elem` [unitTyCon, boolTyCon, intTyCon])
  || isPairTC tc
  || tyConName tc == eitherTyConName    -- no eitherTyCon

isTypeE :: FilterE
isTypeE = typeT successT

-- nonStandardE :: FilterE
-- nonStandardE = traceR "nonStandardE" >>
--                ((traceR "is-type" . isTypeE) <+ notM (((traceR "is-standard" .) . standardTyT . exprType') =<< idR))

-- nonStandardE = traceR "nonStandardE" >>
--                (isTypeE <+ notM ((standardTyT . exprType') =<< idR))

nonStandardE :: FilterE
nonStandardE = -- traceR "nonStandardE" >>
               (isTypeE <+ (nonStandardTyT . arr exprType'))

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
                -- traceR "betaReduceNon: passed non-standard test." >>
                betaReduceR

-- Let-substitute if doing so removes a non-standard type.
letSubstNon :: ReExpr
letSubstNon = labelR "letSubstNon" $
  letT (nonRecT id nonStandardE (const id)) successT (const id) >>
  letSubstR

#ifdef SizedTypes
caseSized :: ReExpr
caseSized = labelR "caseSized" $
            tryR (caseReduceR True) . caseSizedR

stdRuleNames :: [String]
stdRuleNames = ["unTreeZ'/L","unTreeS'/B"]

stdRules :: ReExpr
stdRules = cleanupUnfoldR . rulesR stdRuleNames

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

#endif

rewrites :: [ReExpr]
rewrites = [ betaReduceNon
           , letSubstNon
           , inlineNon
           , castCastR
           , lamFloatCastR
           , labelR "castFloatAppR"  castFloatAppR
           , labelR "caseReduceR" (caseReduceR True)
           , labelR "caseFloatR" caseFloatR
           , labelR "caseFloatArgR" (caseFloatArgR Nothing Nothing) -- ignore strictness
           -- , caseSized  -- after caseFloatCaseR & caseReduceR
           -- , unUnTreeZL, unUnTreeSB, unUnPairPair
           -- , stdRules   -- they don't match
           ]

standardize :: ReExpr
standardize = foldr (<+) (fail "standardize: nothing to do here") rewrites

deepS :: ReExpr
deepS = anytdE (repeatR standardize)

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
    , externC "bash-standardize" bashStandardize "bash with non-standard type removal"
    , externC "simplify-expr" simplifyExprT "Invoke GHC's simplifyExpr"
    , externC "lam-float-cast" lamFloatCastR "Float lambda through case"
    , externC "cast-cast" castCastR "Coalesce nested casts"
    , externC "standardize" standardize "Transform away non-standard types"
    , externC "deep-standardize" deepS "Top-down standardize"
#ifdef SizedTypes
    , externC "case-sized" caseSized "Case with type-sized scrutinee"
    , externC "standard-rules" stdRules "Apply some rules"
    , externC "untreezl" unUnTreeZL "unTreeZ'/L"
    , externC "untreesb" unUnTreeSB "unTreeS'/B"
    , externC "ununpairpair" unUnPairPair "unPair'/(:#)"
#endif
    ]

--     , external "smart-td" smarttdR ["..."]
--     , externC "unL" unL "drop an L"
