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
import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.),(>>>))
import Control.Arrow (arr)
import Data.Functor ((<$),(<$>))
import Data.Monoid (mempty)

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
import HERMIT.External (External,ExternalName,external,(.+),CmdTag(Loop))
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT)
import qualified HERMIT.Extras as Ex

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

#if 0

-- Move to HERMIT.Extras

-- Handy for filtering with congruence transforms

okay1 :: a -> ()
okay1 = const ()

okay2 :: a -> b -> ()
okay2 = const okay1

#else
-- Use mempty instead okayN

-- Tighten the type of (>>). (Alternatively, choose a different operator.)
infixl 1 >>
(>>) :: Monad m => m () -> m b -> m b
(>>) = (Prelude.>>)
#endif


{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False

-- labelR :: InCoreTC t => String -> RewriteH t -> RewriteH t
-- labelR = curry (Ex.labeled observing)

-- watchR :: InCoreTC a => String -> Unop (RewriteH a)
-- watchR = labeledR

-- There's a HERMIT bug (I'm pretty sure) that introduces core-lint errors. Here
-- we can either turn them into a soft or hard error (rewrite failure or error).
-- See <https://github.com/ku-fpg/hermit/issues/103>

#define LintDie

watchR :: String -> Unop ReExpr
#ifdef LintDie
watchR lab r = -- lintExprT >> -- TEMP
               lintingExprR lab (labeled observing (lab,r)) -- hard error
#else
watchR lab r = labeled observing (lab,r) >>> lintExprR  -- fail on core lint error.
#endif

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
  do s <- showPprT . return ty
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
    Specialized traversal
--------------------------------------------------------------------}

-- For inlining, I want to stay out of recursive bindings.

oneNoRecRhs :: Unop ReExpr
oneNoRecRhs r = go
 where
   go = foldr (<+) (fail "oneNoRecRhs: nothing to do here")
          [ r
          , appOneR go go
          , lamOneR skipT go
          , letNonRecOneR skipT go go   -- or not?
          , caseOneR go skipT skipT (const (altOneR skipT (const skipT) go))
          , castOneR go skipT
          , tickOneR skipT go
          -- No type or coercion
          ]

-- TODO: Handle recursive let but not in RHS.

skipT :: Monad m => Transform c m a b
skipT = fail "untried"

{--------------------------------------------------------------------
    Normalization
--------------------------------------------------------------------}

inlineFilt :: FilterE -> ReExpr
inlineFilt filt = inlineR >>> accepterR' filt

-- -- | Inline names with non-standard types or trivial bindings.
-- inlineIt :: ReExpr
-- inlineIt = watchR "inlineIt" $
--            isVarT >> (inlineNonStandard <+ inlineTrivial)
--  where
--    inlineNonStandard = nonStandardE >> inlineR
--    inlineTrivial = inlineR >> accepterR (True <$ trivialExpr)

-- inlineIt :: ReExpr
-- inlineIt = watchR "inlineIt" $
--            inlineR >>> accepterR' (trivialExpr <+ nonStandardE)

inlineTrivial :: ReExpr
inlineTrivial = watchR "inlineTrivial" $
                inlineFilt trivialExpr

-- Maybe drop inlineTrivial in favor of letElimTrivialR

inlineNon :: ReExpr
inlineNon = watchR "inlineNon" $
            inlineFilt nonStandardE

-- TODO: Maybe re-implement inlineNon to check type *first*.

-- inlineIt :: ReExpr
-- inlineIt = watchR "inlineIt" $
--            inlineFilt (trivialExpr <+ nonStandardE)

accepterR' :: (Functor m, Monad m) => Transform c m a () -> Rewrite c m a
accepterR' = accepterR . (True <$)

-- One step toward application normalization.
appStep :: ReExpr
appStep = appT successT nonStandardE mempty >>
          (  watchR "letFloatAppR" letFloatAppR
          <+ watchR "betaReduceR"  betaReduceR
          )

-- appStep = watchR "appStep" $
--           appT successT nonStandardE mempty >>
--           (letFloatAppR <+ betaReduceR)

-- | Trivial expression: for now, literals, variables, casts of trivial.
trivialExpr :: FilterE
trivialExpr = setFailMsg "Non-trivial" $
              isTypeE <+ isVarT <+ isLitT
           <+ trivialLam
           <+ castT trivialExpr id mempty

trivialBind :: FilterH CoreBind
trivialBind = nonRecT successT trivialExpr mempty

trivialLet :: FilterE
trivialLet = letT trivialBind successT mempty

trivialLam :: FilterE
trivialLam = lamT id trivialExpr mempty

trivialBetaRedex :: FilterE
trivialBetaRedex = appT trivialLam successT mempty

-- These filters could instead be predicates. Then use acceptR.

letElimTrivialR :: ReExpr
letElimTrivialR = watchR "trivialLet" $
                  trivialLet >> letSubstR

betaReduceTrivial :: ReExpr
betaReduceTrivial = watchR "betaReduceTrivial" $
                    trivialBetaRedex >> betaReduceR

#if 0
simplifyCastR :: ReExpr
simplifyCastR = watchR "simplifyCastR" $
                castT id id mempty >>
                simplifyExprR

-- ACK! simplifyExprR reports false positives, causing rewrite loop.
#endif

{--------------------------------------------------------------------
    Put it together
--------------------------------------------------------------------}

simplifiers :: [ReCore]
simplifiers =
  promoteR <$>
  [ appStep
  , betaReduceTrivial
  , watchR "letElimR" letElimR   -- removed unused bindings after inlining
  , watchR "castFloatAppR'" castFloatAppR'
  , watchR "castCastR" castCastR
  , watchR "lamFloatCastR" lamFloatCastR
  , watchR "caseReduceR" (caseReduceR False)  -- let rather than subst
  , watchR "caseFloatR" caseFloatR
  -- , watchR "caseWildR" caseWildR
  -- Wedging:
  -- , watchR "caseFloatArgR" (caseFloatArgR Nothing Nothing) -- ignore strictness
  , inlineTrivial
  , letElimTrivialR
  ]

simplifyOne :: ReCore
simplifyOne = foldr (<+) (fail "standardize: nothing to do here") simplifiers

-- inlinePassAll :: ReCore
-- inlinePassAll = anybuR (promoteR inlineNon)

inlinePassOne :: ReCore
inlinePassOne = promoteR (oneNoRecRhs inlineNon)

-- inlinePassOne = onetdR (promoteR inlineNon)

bashE' :: ReExpr
bashE' = watchR "bashR" (extractR bashR)

-- bashE' = watchR "bashR" (extractR bashR >>> lintExprR)

-- Without this lintExprR, I sometimes get bad Core. Hm!

bashR' :: ReCore
bashR' = promoteR bashE'

simplifyTD :: ReCore
simplifyTD = repeatR (anytdR (repeatR simplifyOne) >>> tryR bashR')

-- deepPass :: ReCore
-- deepPass = inlinePassOne >>> tryR simplifyTD

bashSimplifiers :: ReCore
bashSimplifiers = bashExtendedWithR (promoteR <$> simplifiers)

normalizeCoreBash :: ReCore
normalizeCoreBash = tryR bashSimplifiers >>>
                    repeatR (inlinePassOne >>> tryR bashSimplifiers)

normalizeCore' :: ReCore
normalizeCore' = tryR simplifyTD >>>
                 repeatR (inlinePassOne >>> tryR simplifyTD)

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "simplify-one" simplifyOne "Locally simplify for normalization, without inlining"
    , externC "app-step" appStep "Normalize an application"
    , externC "inline-trivial" inlineTrivial "Inline trivial definition"
    , externC "let-elim-trivial" letElimTrivialR "Eliminate trivial binding"
    , externC "inline-non" inlineNon "Inline if non-standard type"
    , externC "inline-pass-one" inlinePassOne "Inlining pass for normalization"
    , externC "bash-simplifiers" bashSimplifiers "Bash with normalization simplifiers (no inlining)"
    , externC "simplify-td" simplifyTD "top-down normalize simplification"
    , externC "normalize-core-bash" normalizeCoreBash "Normalize via bash"
    , externC "normalize-core'" normalizeCore' "Normalize not via bash"
    -- Move to HERMIT.Extras:
    , externC "cast-float-app'" castFloatAppR' "cast-float-app with transitivity"
    , externC "cast-cast" castCastR "Coalesce nested casts"
    , externC "un-cast-cast" unCastCastR "Uncoalesce to nested casts"
    , externC "lam-float-cast" lamFloatCastR "Float lambda through case"
    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    , externC "case-wild" caseWildR "case of wild ==> let (doesn't preserve evaluation)"
    , external "repeat" (repeatN :: Int -> Unop (RewriteH Core))
       [ "Repeat a rewrite n times." ] .+ Loop
    ]
