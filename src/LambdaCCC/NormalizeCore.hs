{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.NormalizeCore
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Transform away all non-standard types
----------------------------------------------------------------------

module LambdaCCC.NormalizeCore where

-- TODO: explicit exports
import Prelude hiding (id,(.))

import Control.Category (id,(.),(>>>))
import Control.Arrow (arr)
import Data.Functor ((<$),(<$>))

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
import HERMIT.External (External,ExternalName)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT, labeled, externC)
import qualified HERMIT.Extras as Ex

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

-- Move to HERMIT.Extras

-- Handy for filtering with congruence transforms

okay1 :: a -> ()
okay1 = const ()

okay2 :: a -> b -> ()
okay2 = const okay1

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = True

-- labelR :: InCoreTC t => String -> RewriteC t -> RewriteC t
-- labelR = curry (Ex.labeled observing)

externC :: (Injection a Core) =>
           ExternalName -> RewriteC a -> String -> External
externC = externC' observing 

{--------------------------------------------------------------------
    Standard types
--------------------------------------------------------------------}

-- TODO: Parametrize the rest of the module by 'standardTyT'.

-- TODO: Consider how to eliminate Encode as well. Then simplify to
-- standardTy :: Type -> Bool

-- A "standard type" is built up from `Unit`, `Bool`, `Int` (for now), pairs (of
-- standard types), sums, and functions, or Encode

standardTyT :: Type -> TransformU ()
standardTyT (tcView -> Just ty) = standardTyT ty
standardTyT (TyConApp tc args) | standardTC tc
                               = mapM_ standardTyT args
standardTyT ty@(TyConApp tc _) =
  -- Treat Encode applications as standard.
  do encodeTC <- findTyConT "LambdaCCC.Encode.Encode"
     if tc == encodeTC then successT else nonStandardFail ty
standardTyT (FunTy arg res) =
  standardTyT arg >> standardTyT res
standardTyT ty = nonStandardFail ty

standardTC :: TyCon -> Bool
standardTC tc =
     (tc `elem` [unitTyCon, boolTyCon, intTyCon])
  || isPairTC tc
  || tyConName tc == eitherTyConName    -- no eitherTyCon

nonStandardFail :: Type -> TransformU a
nonStandardFail ty =
  do s <- showPprT ty
     fail ("non-standard type:\n" ++ s)

nonStandardTyT :: TransformC Type ()
nonStandardTyT = notM (standardTyT =<< idR)

nonStandardE :: FilterE
nonStandardE = (isTypeE <+ (nonStandardTyT . arr exprType'))

-- TODO: Maybe I just want a standard outer shell.

-- TODO: Maybe use coreView instead of tcView? I think it's tcView we want,
-- since it just looks through type synonyms and not newtypes.

-- TODO: If I remove Encode, standardTy can be Type -> Bool

{--------------------------------------------------------------------
    Normalization
--------------------------------------------------------------------}

-- | Inline names with non-standard types or trivial bindings.
inlineIt :: ReExpr
inlineIt = labeledR "inlineIt" $
           isVarT >> (inlineNonStandard <+ inlineTrivial)
 where
   inlineNonStandard = nonStandardE >> inlineR
   inlineTrivial = inlineR >> accepterR (True <$ trivialExpr)

#if 0
-- Neater:
inlineIt = labeledR "inlineIt" $
           inlineR >> accepterR' (trivialExpr <+ nonStandardE)

accepterR' = accepterR . fmap (True <$)
#endif

-- One step toward application normalization.
appStep :: ReExpr
appStep = labeledR "appStep" $
          appT successT nonStandardE okay2 >>
          letFloatAppR <+ castFloatAppR <+ betaReduceR -- <+ ...

-- | Trivial expression: for now, literals, variables, casts of trivial.
trivialExpr :: FilterE
trivialExpr = isVarT <+ isLitT <+ castT trivialExpr id okay2

-- | Trivial binding
trivialBind :: FilterC CoreBind
trivialBind = nonRecT successT trivialExpr okay2

-- | Trivial binding
trivialLet :: FilterE
trivialLet = letT trivialBind successT okay2

-- These filters could instead be predicates. Then use acceptR.

#if 0
-- letElimTrivialR sometimes wedges while trying to print the result.

letElimTrivialR :: ReExpr
letElimTrivialR = labeledR "trivialLet" $
                  trivialLet >> letSubstR
#endif

{--------------------------------------------------------------------
    Put it together
--------------------------------------------------------------------}

simplifiers :: [ReCore]
simplifiers =
  promoteR <$>
  [ appStep
  , labeledR "letElimR" letElimR   -- removed unused bindings after inlining
  , labeledR "castCastR" castCastR
  , labeledR "lamFloatCastR" lamFloatCastR
  , labeledR "caseReduceR" (caseReduceR False)  -- let rather than subst
  , labeledR "caseFloatR" caseFloatR
  , labeledR "caseFloatArgR" (caseFloatArgR Nothing Nothing) -- ignore strictness
--   , letElimTrivialR
  ]

simplify1 :: ReCore
simplify1 = foldr (<+) (fail "standardize: nothing to do here") simplifiers

inlinePassAll :: ReCore
inlinePassAll = anybuR (promoteR inlineIt)

inlinePass1 :: ReCore
inlinePass1 = onetdR (promoteR inlineIt)

simplifyTD :: ReCore
simplifyTD = anytdR (repeatR simplify1)

deepPass :: ReCore
deepPass = inlinePass1 >>> tryR simplifyTD

bashSimplifiers :: ReCore
bashSimplifiers = bashExtendedWithR (promoteR <$> simplifiers)

normalizeCore1 :: ReCore
normalizeCore1 = tryR bashSimplifiers >>>
                 repeatR (inlinePass1 >>> tryR bashSimplifiers)

normalizeCore2 :: ReCore
normalizeCore2 = tryR simplifyTD >>>
                 repeatR (inlinePass1 >>> tryR simplifyTD)

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "simplify-expr" simplifyExprT "Invoke GHC's simplifyExpr"
    , externC "lam-float-cast" lamFloatCastR "Float lambda through case"
    , externC "cast-cast" castCastR "Coalesce nested casts"
    , externC "simplify1" simplify1 "Locally simplify for normalization, without inlining"
    , externC "inline-pass-all" inlinePass1 "Bottom-up inlining pass for normalization"
    , externC "inline-pass-1" inlinePass1 "Single inlining found top-down"
    , externC "bash-simplifiers" bashSimplifiers "Bash with normalization simplifiers (no inlining)"
    , externC "normalize-core-1" normalizeCore1 "Normalize via bash"
    , externC "normalize-core-2" normalizeCore2 "Normalize not via bash"
    ]
