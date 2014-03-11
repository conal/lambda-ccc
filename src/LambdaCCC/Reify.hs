{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

-- TODO: Restore the following pragmas

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Reify
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Reify a Core expression into GADT
----------------------------------------------------------------------

module LambdaCCC.Reify (plugin) where

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Control.Monad ((<=<),guard)
import Control.Arrow (arr,(>>>))
import Data.List (intercalate)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Text.Printf (printf)

-- import qualified Language.Haskell.TH as TH (Name) -- ,mkName
-- import qualified Language.Haskell.TH.Syntax as TH (showName)

-- GHC API
-- import PrelNames (unitTyConKey,boolTyConKey,intTyConKey)

import qualified Language.KURE.Translate as Kure
import HERMIT.Monad (HermitM,newIdH)
import HERMIT.Context
  (HermitC,ReadBindings(..),hermitBindings,HermitBinding(..),HermitBindingSite(..)
  ,lookupHermitBinding,boundIn,BoundVars,HasGlobalRdrEnv(..)) -- ,AddBindings
import HERMIT.Core (Crumb(..),localFreeIdsExpr,CoreProg)
import HERMIT.External
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure hiding (apply)
import HERMIT.Plugin

-- Note: All of the Dictionary submodules are now re-exported by HERMIT.Dictionary,
--       so if you prefer you could import all these via that module, rather than seperately.
import HERMIT.Dictionary.AlphaConversion (unshadowR)
import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Composite (simplifyR)
import HERMIT.Dictionary.Debug (observeR)
import HERMIT.Dictionary.Rules (rulesR) -- ruleR,
import HERMIT.Dictionary.Inline (inlineR,inlineNameR) -- , inlineNamesR
import HERMIT.Dictionary.Local (letIntroR,letFloatArgR,letFloatTopR)
import HERMIT.Dictionary.Navigation (rhsOfT,parentOfT,bindingGroupOfT)
-- import HERMIT.Dictionary.Composite (simplifyR)
import HERMIT.Dictionary.Unfold (cleanupUnfoldR) -- unfoldNameR,

import LambdaCCC.Misc (Unop,(<~)) -- ,Binop
-- import qualified LambdaCCC.Ty as T
-- import qualified LambdaCCC.Prim as P
-- import qualified LambdaCCC.Lambda as E
-- import LambdaCCC.MkStringExpr (mkStringExpr)

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d type arguments but got %d."
                     (var2String f) arity ntys
  | otherwise = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)
 where
   arity = tyArity f
   ntys  = length ts

tyArity :: Id -> Int
tyArity = length . fst . splitForAllTys . varType

-- | Variant of GHC's 'collectArgs'
collectTypeArgs :: CoreExpr -> ([Type], CoreExpr)
collectTypeArgs expr = go [] expr
  where
    go ts (App f (Type t)) = go (t:ts) f
    go ts                e = (reverse ts, e)

collectForalls :: Type -> ([Var], Type)
collectForalls ty = go [] ty
  where
    go vs (ForAllTy v t') = go (v:vs) t'
    go vs t               = (reverse vs, t)

-- TODO: Rewrite collectTypeArgs and collectForalls as unfolds and refactor.

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> CoreExpr -> CoreExpr
subst ps = substExpr (error "subst: no SDoc") (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new

{--------------------------------------------------------------------
    KURE utilities
--------------------------------------------------------------------}

-- | Transformation while focused on a snoc path
snocPathIn :: ( Eq crumb, Functor m, ReadPath c crumb
              , MonadCatch m, Walker c b ) =>
              Translate c m b (SnocPath crumb) -> Unop (Rewrite c m b)
snocPathIn mkP r = mkP >>= flip localPathR r

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

-- Next two from Andy G:

-- | Lookup the name in the context first, then, failing that, in GHC's global
-- reader environment.
findTyConT :: ( BoundVars c, HasGlobalRdrEnv c, HasDynFlags m
              , MonadThings m, MonadCatch m) =>
              String -> Translate c m a TyCon
findTyConT nm = prefixFailMsg ("Cannot resolve name " ++ nm ++ ", ") $
                contextonlyT (findTyConMG nm)

findTyConMG :: (BoundVars c, HasGlobalRdrEnv c, HasDynFlags m, MonadThings m) => String -> c -> m TyCon
findTyConMG nm c =
    case filter isTyConName $ findNamesFromString (hermitGlobalRdrEnv c) nm of
      [n] -> lookupTyCon n
      ns  -> do dynFlags <- getDynFlags
                fail $ "multiple matches found:\n" ++ intercalate ", " (map (showPpr dynFlags) ns)

-- apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr

apps' :: ( Functor m, HasDynFlags m, MonadThings m, MonadCatch m
         , BoundVars c, HasGlobalRdrEnv c ) =>
         String -> [Type] -> [CoreExpr] -> Translate c m a CoreExpr
apps' s ts es = (\ i -> apps i ts es) <$> findIdT s

-- defR :: RewriteH Id -> RewriteH CoreExpr -> RewriteH Core
-- defR rewI rewE = prunetdR (  promoteDefR (defAllR rewI rewE)
--                           <+ promoteBindR (nonRecAllR rewI rewE) )

-- rhsR :: RewriteH CoreExpr -> RewriteH Core
-- rhsR = defR idR

-- The set of variables in a HERMIT context
isLocal :: ReadBindings c => c -> (Var -> Bool)
isLocal = flip boundIn

-- | Extract just the lambda-bound variables in a HERMIT context
isLocalT :: (ReadBindings c, Applicative m) => Translate c m a (Var -> Bool)
isLocalT = contextonlyT (pure . isLocal)

type InCoreTC t = Injection t CoreTC

observing :: Bool
observing = False

observeR' :: InCoreTC t => String -> RewriteH t
observeR' | observing = observeR
          | otherwise = const idR

tries :: (InCoreTC a, InCoreTC t) => [(String,TranslateH a t)] -> TranslateH a t
tries = foldr (<+) (observeR' "Unhandled" >>> fail "unhandled")
      . map (uncurry labeled)

labeled :: InCoreTC t => String -> Unop (TranslateH a t)
labeled label = (>>> observeR' label)

-- mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
-- mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqVarName

uqVarName :: Var -> String
uqVarName = uqName . varName

anybuER :: (MonadCatch m, Walker c g, ExtendPath c Crumb, Injection CoreExpr g) =>
           Rewrite c m CoreExpr -> Rewrite c m g
anybuER r = anybuR (promoteExprR r)

anytdER :: (MonadCatch m, Walker c g, ExtendPath c Crumb, Injection CoreExpr g) =>
           Rewrite c m CoreExpr -> Rewrite c m g
anytdER r = anytdR (promoteExprR r)

tryRulesBU :: [String] -> RewriteH Core
tryRulesBU = tryR . anybuER . rulesR

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

type ReExpr = RewriteH CoreExpr

lamName :: Unop String
lamName = ("LambdaCCC.Lambda." ++)

findIdE :: String -> TranslateH a Id
findIdE = findIdT . lamName

findTyConE :: String -> TranslateH a TyCon
findTyConE = findTyConT . lamName

type OkCM c m =
  ( Functor m, HasDynFlags m, MonadThings m, MonadCatch m
  , BoundVars c, HasGlobalRdrEnv c )

type TranslateU b = forall c m a. OkCM c m => Translate c m a b

appsE :: String -> [Type] -> [CoreExpr] -> TranslateU CoreExpr
appsE = apps' . lamName

-- A handy form for composition via <=<
appsE1 :: String -> [Type] -> CoreExpr -> TranslateU CoreExpr
appsE1 str ts e = appsE str ts [e]

epOf :: Type -> TranslateH a Type
epOf t = do epTC <- findTyConE "EP"
            return (TyConApp epTC [t])

evalS, reifyS :: String
evalS = "evalEP"
reifyS = "reifyEP"

varPS, letS, varPatS :: String
varPS   = "varP#"
letS    = "lettP"
varPatS = "varPat#"

-- reify u --> u
unReify :: ReExpr
unReify = do (_reifyE, [Type _, arg]) <- callNameLam reifyS
             return arg
-- eval e --> e
unEval :: ReExpr
unEval  = do (_evalE, [Type _, body]) <- callNameLam evalS
             return body

-- reify (eval e) --> e
reifyEval :: ReExpr
reifyEval = unReify >>> unEval

-- reifyOf :: (Functor m, HasGlobalRdrEnv c, BoundVars c, MonadCatch m, MonadThings m, HasDynFlags m) =>
--            CoreExpr -> Translate c m a CoreExpr

reifyOf :: CoreExpr -> TranslateU CoreExpr
reifyOf e = appsE reifyS [exprType e] [e]

evalOf :: CoreExpr -> TranslateU CoreExpr
evalOf e = appsE evalS [dropEP (exprType e)] [e]

dropEP :: Type -> Type
dropEP (TyConApp (uqName . tyConName -> name) [t]) =
  if name == "EP" then t
  else error ("dropEP: not an EP: " ++ show name)
dropEP _ = error "dropEP: not a TyConApp"

reifyR :: ReExpr
reifyR = idR >>= reifyOf

evalR :: ReExpr
evalR = idR >>= evalOf

-- reify (u v) --> reify u `appP` reify v
reifyApp :: ReExpr
reifyApp = do App u v <- unReify
              FunTy a b <- constT (return (exprType u)) -- or fail
              u' <- reifyOf u
              v' <- reifyOf v
              appsE "appP" [b,a] [u', v'] -- note b,a

-- TODO: refactor so we unReify once and then try variations

varEval :: Var -> TranslateU CoreExpr
varEval v = (evalOf <=< appsE1 varPS [varType v]) (varLitE v)

varSubst :: [Var] -> TranslateU (Unop CoreExpr)
varSubst vs = do vs' <- mapM varEval vs
                 return (subst (vs `zip` vs'))

reifyLam :: ReExpr
reifyLam = do Lam v e <- unReify
              sub     <- varSubst [v]
              e'      <- reifyOf (sub e)
              appsE "lamvP#" [varType v, exprType e] [varLitE v,e']

-- Pass through unless an IO
unlessIO :: ReExpr
unlessIO = filterR (not . isIO . exprType)

-- Pass through unless an eval application
unlessEval :: ReExpr
unlessEval = filterR (not . isEval)

isIO :: Type -> Bool
isIO (TyConApp (uqName . tyConName -> "IO") [_]) = True
isIO _                                           = False

isEval :: CoreExpr -> Bool
isEval (App (App (Var v) (Type _)) _) = uqVarName v == evalS
isEval _                              = False

-- Pass through if condition satisfied
filterR :: (a -> Bool) -> RewriteH a
filterR p = do a <- idR
               if p a then return a else fail "filterR: condition failed"

-- e --> eval (reify e) in preparation for rewriting reify e.
-- Fail if e is already an eval or if it has IO type.
reifyRhs :: ReExpr
reifyRhs = unlessIO >>> unlessEval >>> reifyR >>> evalR

reifyDef :: RewriteH CoreBind
reifyDef = nonRecAllR idR reifyRhs

reifyModGuts :: RewriteH ModGuts
reifyModGuts = modGutsR (progBindsAnyR (const reifyDef))

progTest :: RewriteH CoreProg
progTest = progBindsAnyR (const idR)

inlineLocal :: ReExpr
inlineLocal = do Var v <- idR
                 True  <- contextonlyT (return . boundIn v)
                 inlineR

inReify :: Unop ReExpr
inReify = reifyR <~ unReify

reifyInline :: ReExpr
reifyInline = inReify inlineLocal

-- TODO: apply reifyInline only when eval arises.

reifyLetToRedex :: ReExpr
reifyLetToRedex = inReify toRedex
 where
   toRedex = do Let (NonRec v rhs) body <- idR
                return (Lam v body `App` rhs)

-- TODO: restrict to monomorphic bindings, leaving polymorphic bindings to
-- another treatment. Or maybe convert anyway, and deal with the resulting type
-- abstractions and applications.

reifyCase :: ReExpr
reifyCase = do Case scrut@(exprType -> scrutT) wild bodyT [branch] <- unReify
               _ <- observeR' "Reifying case"
               (patE,rhs) <- reifyBranch wild branch
               scrut'     <- reifyOf scrut
               appsE letS [scrutT,bodyT] [patE,scrut',rhs]

-- Reify a case alternative, yielding a reified pattern and a reified
-- alternative body (RHS).
-- Only pair patterns for now.
reifyBranch :: Var -> CoreAlt -> TranslateU (CoreExpr,CoreExpr)
reifyBranch wild (DataAlt (isTupleTyCon.dataConTyCon -> True), vars@[_,_], rhs) =
  do vPats <- mapM varPatT# vars
     sub   <- varSubst (wild : vars)
     pat   <- appsE ":#" (varType <$> vars) vPats
     pat'  <- if wild `elemVarSet` localFreeIdsExpr rhs
                then -- WARNING: untested as of 2014-03-11
                  appsE "asPat#" [varType wild] [varLitE wild,pat]
                else
                  return pat
     rhs'  <- reifyOf (sub rhs)
     return (pat', rhs')
 where
   varPatT# :: Var -> TranslateU CoreExpr
   varPatT# v = appsE varPatS [varType v] [varLitE v]

reifyBranch _ _ = fail "reifyBranch: Only handles pair patterns so far."


reifyMisc :: ReExpr
reifyMisc = tries [ ("reifyEval"   , reifyEval)
                  , ("reifyApp"    , reifyApp)
                  , ("reifyLam"    , reifyLam)
                  , ("reifyLet"    , reifyLetToRedex >>> reifyMisc)  -- experimental
                  , ("reifyCase"   , reifyCase)
                  , ("reifyInline" , reifyInline     >>> reifyMisc)  -- experimental
                  -- To come: case, lamT, appT
                  ]

-- Note: the ">>> reifyMisc" comes from the intent to use (anytdR reifyMisc),
-- which apparently does not revisit the current node after rewriting. To do:
-- Ask Andy whether I should be using a different combinator.

-- reifyExprC :: RewriteH Core
-- reifyExprC = tryR unshadowR >>> anytdR reifyDef >>> anytdR (promoteExprR reifyMisc)

reifyRules :: RewriteH Core
reifyRules = tryRulesBU $ map ("reify/" ++)
  ["not","(&&)","(||)","xor","(+)","exl","exr","pair","inl","inr","if","false","true"]

-- or: words $ "not (&&) (||) xor ..."

-- TODO: Is there a way not to redundantly specify this rule list?
-- Yes -- trust GHC to apply the rules later.

callNameLam :: String -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callNameLam = callNameT . lamName

-- TODO: reifyEval replaced with tryRulesBU ["reify'/eval","eval/reify'"], and
-- even those rules are no longer invoked explicitly.

inlineCleanup :: String -> RewriteH Core
inlineCleanup nm = tryR $ anybuER (inlineNameR nm) >>> anybuER cleanupUnfoldR

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-rules"
        (reifyRules :: RewriteH Core)
        ["convert some non-local vars to consts"]
    , external "inline-cleanup"
        (inlineCleanup :: String -> RewriteH Core)
        ["inline a named definition, and clean-up beta-redexes"]
    , external "reify-rhs"
        (promoteExprR reifyRhs :: RewriteH Core)
        ["reifyE the RHS of a definition"]
    , external "reify-def"
        (promoteBindR reifyDef :: RewriteH Core)
        ["reifyE a definition"]
    , external "reify-misc"
        (promoteExprR reifyMisc :: RewriteH Core)
        ["Simplify 'reify e'"]  -- use with any-td
    -- for debugging
    , external "unreify"
        (promoteExprR unReify :: RewriteH Core)
        ["Drop reify"]
    , external "reify-inline"
        (promoteExprR reifyInline :: RewriteH Core)
        ["inline names where reified"]
    , external "unless-io"
        (promoteExprR unlessIO :: RewriteH Core)
        ["Pass through if not IO-typed"]
    , external "reify-it" (promoteExprR reifyR :: RewriteH Core) ["apply reify"]
    , external "eval-it" (promoteExprR evalR :: RewriteH Core) ["apply eval"]
    , external "reify-let-to-redex"
        (promoteExprR reifyLetToRedex :: RewriteH Core) ["let to redex"]
    , external "reify-case"
        (promoteExprR reifyCase :: RewriteH Core) ["reify case"]
    , external "reify-module"
        (promoteModGutsR reifyModGuts :: RewriteH Core) ["reify all top-level definitions"]
    , external "prog-test"
        (promoteProgR progTest :: RewriteH Core) ["mumble"]
    ]
