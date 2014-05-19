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
import Data.Functor ((<$>))

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
import HERMIT.External (External)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT, labeled)
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

nonStandardTyT :: TransformH Type ()
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

-- Inline names with non-standard types
inlineNon :: ReExpr
inlineNon = labelR "inlineNon" $
            isVarT >> nonStandardE >> inlineR

-- One step toward application normalization.
appStep :: ReExpr
appStep = labelR "appStep" $
          appT successT nonStandardE okay2 >>
          letFloatAppR <+ castFloatAppR <+ betaReduceR -- <+ ...

-- | Trivial expression: for now, literals, variables, casts of trivial.
trivialExpr :: FilterE
trivialExpr = isVarT <+ isLitT <+ castT trivialExpr id okay2

-- | Trivial binding
trivialBind :: FilterH CoreBind
trivialBind = nonRecT successT trivialExpr okay2

letElimTrivialR :: ReExpr
letElimTrivialR = labelR "trivialLet" $
                  letT trivialBind successT okay2 >> letSubstR
   
{--------------------------------------------------------------------
    Put it together
--------------------------------------------------------------------}

simplifiers :: [ReCore]
simplifiers =
  promoteR <$>
  [ appStep
  , letElimR   -- removed unused bindings after inlining
  , castCastR
  , lamFloatCastR
  , labelR "caseReduceR" (caseReduceR False)  -- let rather than subst
  , labelR "caseFloatR" caseFloatR
  , labelR "caseFloatArgR" (caseFloatArgR Nothing Nothing) -- ignore strictness
  , letElimTrivialR
  ]

simplify1 :: ReCore
simplify1 = foldr (<+) (fail "standardize: nothing to do here") simplifiers

inlinePassAll :: ReCore
inlinePassAll = anybuR (promoteR inlineNon)

inlinePass1 :: ReCore
inlinePass1 = onetdR (promoteR inlineNon)

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
