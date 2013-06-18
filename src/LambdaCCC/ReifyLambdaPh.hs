{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
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

module LambdaCCC.ReifyLambdaPh where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Control.Arrow (arr,(>>>))
import GHC.Pack (unpackCString#)
import Text.Printf (printf)
import Debug.Trace
import Data.List (intercalate)

import GhcPlugins
import TypeRep (Type(..))
import Var
import PrelNames (unpackCStringName)

-- TODO: Pare down
import Language.HERMIT.Monad (HermitM,liftCoreM)
import Language.HERMIT.External
import Language.HERMIT.Kure hiding (apply)
import qualified Language.HERMIT.Kure as Kure
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.GHC (uqName,var2String)
import Language.HERMIT.Primitive.Unfold (cleanupUnfoldR)
import Language.HERMIT.Primitive.GHC (rule)
import Language.HERMIT.Core (Crumb(..)) -- ,CoreDef(..)
import Language.HERMIT.Context (HermitBindingSite(LAM),ReadBindings(..))

import LambdaCCC.Misc (Unop)
import qualified LambdaCCC.LambdaPh as E

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

{-
-- Unsafe way to ppr in pure code.
tr :: Outputable a => a -> a
tr x = trace ("tr: " ++ pretty x) x

pretty :: Outputable a => a -> String
pretty = showPpr tracingDynFlags

pretties :: Outputable a => [a] -> String
pretties = intercalate "," . map pretty
-}

varMachStr :: Var -> CoreExpr
varMachStr = Lit . mkMachString . var2String

-- mkStringExpr :: MonadThings m => String -> m CoreExpr  -- Result :: String

-- stringLitE' :: Id -> String -> CoreExpr
-- stringLitE' unpackId = App (Var unpackId) . Lit . mkMachString

-- varMachStr' :: Id -> Var -> CoreExpr
-- varMachStr' unpackId = stringLitE' unpackId . var2String

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

unfoldRules :: [String] -> RewriteH CoreExpr
unfoldRules nms = catchesM (rule <$> nms) >>> cleanupUnfoldR

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

type ReExpr = RewriteH CoreExpr

observing :: Bool
observing = False

observeR' :: String -> ReExpr
observeR' | observing = observeR
          | otherwise = const idR

reifyCoreExpr :: ReExpr
reifyCoreExpr =
  do varId  <- findIdT 'E.var
     appId  <- findIdT '(E.:^)
     lamvId <- findIdT 'E.lamv
     evalId <- findIdT 'E.evalE
     let rew :: ReExpr
         rew = tries [ ("Var",rVar)
                   --, ("Pair",rPair)
                     , ("AppT",rAppT), ("App",rApp)
                     , ("LamT",rLamT), ("Lam",rLam)]
          where
            tries :: [(String,ReExpr)] -> ReExpr
            tries = foldr (<+) (observeR' "Other" >>> fail "unhandled")
                  . map (uncurry try)
            try label = (>>> observeR' label)

         rVar{-, rPair-}, rAppT, rApp, rLamT, rLam :: ReExpr
         rVar  = varT $ arr $ \ v ->
                   apps varId [varType v] [varMachStr v]
--          rPair = pairT rew rew $ ...
         rAppT = do App _ (Type {}) <- idR
                    appT rew idR (arr App)
         rApp  = do App u _ <- idR
                    appT  rew rew $ arr $ \ u' v' ->
                      let (a,b) = splitFunTy (exprType u) in
                        apps appId [b,a] [u', v'] -- note b,a
         rLamT = do Lam (isTyVar -> True) _ <- idR
                    lamT idR rew (arr Lam)
         rLam  = do Lam v e <- idR
                    lamT (arr varMachStr) rew $ arr $ \ v' e' ->
                      apps lamvId [varType v, exprType e] [v',e']
         -- TODO: Maybe merge rAppT/rApp and rLamT/rLam, using one match.
     do e      <- idR
        let mkEval e' = apps evalId [exprType e] [e']
        mkEval <$> rew

varToConst :: RewriteH Core
varToConst = anybuR $ promoteExprR $ unfoldRules 
               ["var/xor", "var/and", "var/pair"]

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-core" (promoteExprR reifyCoreExpr)
        [ "Turn a Core expression into a GADT construction" ]
    , external "var-to-const" varToConst
        [ "convert some non-local vars to consts" ]
    ]
