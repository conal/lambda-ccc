{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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
import Text.Printf (printf)

import qualified Language.Haskell.TH as TH

import GhcPlugins hiding (mkStringExpr)

-- TODO: Pare down
import Language.HERMIT.External
import Language.HERMIT.Kure hiding (apply)
import qualified Language.HERMIT.Kure as Kure
import Language.HERMIT.Core (Crumb(..))
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Navigation (rhsOf)
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.GHC (uqName,var2String)
import Language.HERMIT.Primitive.Unfold (unfoldNameR,cleanupUnfoldR)
import Language.HERMIT.Primitive.GHC (rule)

import qualified LambdaCCC.Lambda as E
import LambdaCCC.MkStringExpr (mkStringExpr)

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d arguments but got %d."
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
appVTysT :: Monad m =>
            Translate c m Var a -> (a -> [Type] -> b) -> Translate c m CoreExpr b
appVTysT tv h = translate $ \c ->
  \ case (collectTypeArgs -> (Var v, ts)) ->
           liftM2 h (Kure.apply tv c v)      -- TODO: Crumbs
                    (return ts)
         _ -> fail "not an application of a variable to types."



rhsR :: RewriteH CoreExpr -> RewriteH Core
rhsR r = prunetdR (promoteDefR (defAllR idR r) <+ promoteBindR (nonRecAllR idR r))

unfoldNames :: [TH.Name] -> RewriteH CoreExpr
unfoldNames nms = catchesM (unfoldNameR <$> nms) -- >>> cleanupUnfoldR

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
  do varId  <- findIdT 'E.var
     appId  <- findIdT '(E.:^)
     lamvId <- findIdT 'E.lamv
     evalId <- findIdT 'E.evalE
     let rew :: ReExpr
         rew = tries [ ("AppT",rAppT), ("App",rApp)
                     , ("LamT",rLamT), ("Lam",rLam)]
          where
            tries :: [(String,ReExpr)] -> ReExpr
            tries = foldr (<+) (observeR' "Other" >>> fail "unhandled")
                  . map (uncurry try)
            try label = (>>> observeR' label)
         rAppT, rApp, rLamT, rLam :: ReExpr
         rAppT = do e <- idR            -- TODO: ty <- arr exprType
                    appVTysT mkVarName $ \ (name,_) _ ->
                      apps varId [exprType e] [name]
         rApp  = do App u _ <- idR
                    appT  rew rew $ arr $ \ u' v' ->
                      let (a,b) = splitFunTy (exprType u) in
                        apps appId [b,a] [u', v'] -- note b,a
         rLamT = do Lam (isTyVar -> True) _ <- idR
                    lamT idR rew (arr Lam)
         rLam  = do Lam _ e <- idR
                    lamT mkVarName rew $ arr $ \ (name,ty) e' ->
                      apps lamvId [ty, exprType e] [name,e']
         -- TODO: Literals
     do e <- idR
        let mkEval e' = apps evalId [exprType e] [e']
        mkEval <$> rew


-- TODO: Remove pairing recognition (and supporting code), and instead use the
-- rewrite in Lambda.

mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varToConst :: RewriteH Core
varToConst = anybuR $ promoteExprR $ unfoldRules $ map ("var/" ++)
               ["xor","and","fst","snd","pair"]

cleanupReifyR :: RewriteH Core
cleanupReifyR =
      tryR varToConst
  >>> (tryR $ anybuR $ promoteExprR $ unfoldNames ['E.var,'E.lamv])
  >>> (tryR $ anybuR $ promoteExprR $ cleanupUnfoldR)

-- I thought the following line would be equivalent to the previous two, but I
-- don't get cleanup after lamv unfolding.

--   >>> anybuR (promoteExprR (unfoldNames ['E.var,'E.lamv] >>> cleanupUnfoldR))

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
    [ external "reify-expr" (promoteExprR reifyExpr)
        [ "Reify a Core expression into a GADT construction" ]
    , external "var-to-const" varToConst
        [ "convert some non-local vars to consts" ]
    , external "cleanup-reify" cleanupReifyR
        [ "convert some non-local vars to consts" ]
    , external "reify-def" reifyDef
        [ "reify for definitions" ]
    , external "reify-expr-cleanup" (promoteExprR reifyExpr >>> cleanupReifyR)
        [ "reify-core and cleanup for expressions" ]
    , external "reify-def-cleanup" (reifyDef >>> cleanupReifyR)
        [ "reify-core and cleanup for definitions" ]
    ]
