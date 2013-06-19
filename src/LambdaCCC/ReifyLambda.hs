{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ReifyLambda
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Reify a Core expression into GADT
----------------------------------------------------------------------

module LambdaCCC.ReifyLambda where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Control.Monad ((<=<),liftM2)
import Control.Arrow (arr,(>>>),(&&&))
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf (printf)

import qualified Language.Haskell.TH as TH

import GhcPlugins hiding (mkStringExpr)

import Language.HERMIT.Context
  (ReadBindings,HermitBindingSite(LAM),hermitBindings)
import Language.HERMIT.Core (Crumb(..))
import Language.HERMIT.External
import Language.HERMIT.GHC (uqName,var2String)
import Language.HERMIT.Kure hiding (apply)
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.Primitive.GHC (rule)
-- import Language.HERMIT.Primitive.Navigation (rhsOf)
import Language.HERMIT.Primitive.Unfold (unfoldNameR,cleanupUnfoldR)
import qualified Language.HERMIT.Kure as Kure

import qualified LambdaCCC.Lambda as E
import LambdaCCC.MkStringExpr (mkStringExpr)

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

listToPair :: [a] -> Maybe (a,a)
listToPair [a,b] = Just (a,b)
listToPair _     = Nothing

unTuple :: CoreExpr -> Maybe [CoreExpr]
unTuple expr@(App {})
  | (Var f, dropWhile isTypeArg -> valArgs) <- collectArgs expr
  , Just dc <- isDataConWorkId_maybe f
  , isTupleTyCon (dataConTyCon dc) && (valArgs `lengthIs` idArity f)
  = Just valArgs
unTuple _ = Nothing

-- tuple :: [CoreExpr] -> CoreExpr
-- tuple es = ... ?
--
-- pair :: Binop CoreExpr
-- pair a b = tuple [a,b]

unPair :: CoreExpr -> Maybe (CoreExpr,CoreExpr)
unPair = listToPair <=< unTuple

{-
-- Unsafe way to ppr in pure code.
tr :: Outputable a => a -> a
tr x = trace ("tr: " ++ pretty x) x

pretty :: Outputable a => a -> String
pretty = showPpr tracingDynFlags

pretties :: Outputable a => [a] -> String
pretties = intercalate "," . map pretty
-}

-- | Variant of GHC's 'collectArgs'
collectTypeArgs :: CoreExpr -> (CoreExpr, [Type])
collectTypeArgs expr = go expr []
  where
    go (App f (Type t)) ts = go f (t:ts)
    go e 	        ts = (e, ts)

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

unfoldRules :: [String] -> RewriteH CoreExpr
unfoldRules nms = catchesM (rule <$> nms) >>> cleanupUnfoldR

-- | Translate a pair expression.
pairT :: (Monad m, ExtendPath c Crumb) =>
         Translate c m CoreExpr a -> Translate c m CoreExpr b
      -> (Type -> Type -> a -> b -> z) -> Translate c m CoreExpr z
pairT tu tv f = translate $ \ c ->
  \ case (unPair -> Just (u,v)) ->
           liftM2 (f (exprType u) (exprType v))
                  (Kure.apply tu (c @@ App_Fun @@ App_Arg) u)
                  (Kure.apply tv (c            @@ App_Arg) v)
         _         -> fail "not a pair node."

-- | Translate an n-ary type-instantiation of a variable, where n >= 0.
appVTysT :: (ExtendPath c Crumb, Monad m) =>
            Translate c m Var a -> (a -> [Type] -> b) -> Translate c m CoreExpr b
appVTysT tv h = translate $ \c ->
  \ case (collectTypeArgs -> (Var v, ts)) ->
           liftM2 h (Kure.apply tv (applyN (length ts) (@@ App_Fun) c) v)
                    (return ts)
         _ -> fail "not an application of a variable to types."
  where
    applyN :: Int -> (a -> a) -> a -> a
    applyN n f a = foldr ($) a (replicate n f)


rhsR :: RewriteH CoreExpr -> RewriteH Core
rhsR r = prunetdR (promoteDefR (defAllR idR r) <+ promoteBindR (nonRecAllR idR r))

unfoldNames :: [TH.Name] -> RewriteH CoreExpr
unfoldNames nms = catchesM (unfoldNameR <$> nms) -- >>> cleanupUnfoldR

-- Just the lambda-bound variables in a HERMIT context
lambdaVars :: ReadBindings c => c -> S.Set Var
lambdaVars = M.keysSet .  M.filter (isLam . snd) . hermitBindings
 where
   isLam LAM = True
   isLam _   = False

-- | Extract just the lambda-bound variables in a HERMIT context
lambdaVarsT :: (ReadBindings c, Applicative m) => Translate c m a (S.Set Var)
lambdaVarsT = contextonlyT (pure . lambdaVars)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

type ReExpr = RewriteH CoreExpr

observing :: Bool
observing = False

observeR' :: String -> ReExpr
observeR' | observing = observeR
          | otherwise = const idR

reifyExpr :: ReExpr
reifyExpr =
  do varId   <- findIdT 'E.var
     appId   <- findIdT '(E.:^)
     lamvId  <- findIdT 'E.lamv
     evalId  <- findIdT 'E.evalE
     reifyId <- findIdT 'E.reifyE
     let rew :: ReExpr
         rew = tries [ ("Var",rVar)
                     , ("Reify", rReify)
                     , ("App",rApp)
                     , ("LamT",rLamT), ("Lam",rLam)
                     ]
          where
            tries :: [(String,ReExpr)] -> ReExpr
            tries = foldr (<+) (observeR' "Other" >>> fail "unhandled")
                  . map (uncurry try)
            try label = (>>> observeR' label)
         rVar, rApp, rLamT, rLam :: ReExpr
         rVar  = do bvars <- lambdaVarsT
                    varT $
                      do v <- idR
                         if S.member v bvars then
                           do (name,ty) <- mkVarName
                              return $ apps varId [ty] [name]
                          else
                           fail "rVar: not a lambda-bound variable"
                            -- return $ apps reifyId [varType v] [Var v]
         -- Reify (non-lambda) variables and their polymorphic instantiations.
         rReify = do e@(collectTypeArgs -> (Var _, _)) <- idR
                     return $ apps reifyId [exprType e] [e]
         rApp  = do App (exprType -> funTy) _ <- idR
                    appT  rew rew $ arr $ \ u' v' ->
                      let (a,b) = splitFunTy funTy in
                        apps appId [b,a] [u', v'] -- note b,a
         rLamT = do Lam (isTyVar -> True) _ <- idR
                    lamT idR rew (arr Lam)
         rLam  = do Lam _ (exprType -> bodyTy) <- idR
                    lamT mkVarName rew $ arr $ \ (name,ty) e' ->
                      apps lamvId [ty, bodyTy] [name,e']
         -- TODO: Literals
     do ty <- arr exprType
        let mkEval e' = apps evalId [ty] [e']
        mkEval <$> rew


-- TODO: Remove pairing recognition (and supporting code), and instead use the
-- rewrite in Lambda.

mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

reifyRules :: RewriteH Core
reifyRules = anybuR $ promoteExprR $ unfoldRules $ map ("reify/" ++)
               ["not","(&&)","(||)","xor","(+)","fst","snd","pair"]

cleanupReifyR :: RewriteH Core
cleanupReifyR =
      tryR reifyRules
  >>> (tryR $ anybuR $ promoteExprR $ unfoldNames ['E.var,'E.lamv])
  >>> (tryR $ anybuR $ promoteExprR $ cleanupUnfoldR)

-- I thought the following line would be equivalent to the previous two, but I
-- don't get cleanup after lamv unfolding.

--   >>> anybuR (promoteExprR (unfoldNames ['E.var,'E.lamv] >>> cleanupUnfoldR))

-- I think I could remove cleanupReifyR and rely on GHC, but I'm unsure.

reifyDef :: RewriteH Core
reifyDef = rhsR reifyExpr

-- reifyExprPlus :: RewriteH Core
-- reifyExprPlus = promoteExprR reifyExpr >>> cleanupReifyR

-- reifyDefPlus :: RewriteH Core
-- reifyDefPlus = reifyDef >>> cleanupReifyR


{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-expr" (promoteExprR reifyExpr :: RewriteH Core)
        [ "Reify a Core expression into a GADT construction" ]
    , external "reify-rules" (reifyRules :: RewriteH Core)
        [ "convert some non-local vars to consts" ]
    , external "cleanup-reify" (cleanupReifyR :: RewriteH Core)
        [ "convert some non-local vars to consts" ]
    , external "reify-def" (reifyDef :: RewriteH Core)
        [ "reify for definitions" ]
    , external "reify-expr-cleanup" (promoteExprR reifyExpr >>> cleanupReifyR :: RewriteH Core)
        [ "reify-core and cleanup for expressions" ]
    , external "reify-def-cleanup" (reifyDef >>> cleanupReifyR :: RewriteH Core)
        [ "reify-core and cleanup for definitions" ]
    ]
