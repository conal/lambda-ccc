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
import Language.HERMIT.Core (Crumb(..),Core) -- ,CoreDef(..)
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

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- reify :: a -> E a
-- reify = error "reify: not implemented."

reifyCoreExpr :: RewriteH CoreExpr
reifyCoreExpr =
  do varId     <- findIdT 'E.var
     appId     <- findIdT '(E.:^)
     lamvId    <- findIdT 'E.lamv
     let reifyE :: Unop CoreExpr
         reifyE (Var v) = apps varId [varType v] [varMachStr v]
         reifyE (Lit _) = error "reifyE: Lit not handled"
         reifyE (App u v@(Type{})) = App (reifyE u) v
         -- TODO: Pairs
         reifyE (App u v) = apps appId [b,a] [reifyE u, reifyE v] -- note b,a
          where
            (a,b) = splitFunTy (exprType u)
         reifyE (Lam v e) | isTyVar v = Lam v (reifyE e)
                          | otherwise = apps lamvId [varType v, exprType e]
                                                    [varMachStr v,reifyE e]
         reifyE _ = error "reifyE: incomplete"
     -- reifyE <$> idR
     do e      <- idR
        evalId <- findIdT 'E.evalE
        return $ apps evalId [exprType e] [reifyE e]

varMachStr :: Var -> CoreExpr
varMachStr = Lit . mkMachString . var2String

-- mkStringExpr :: MonadThings m => String -> m CoreExpr  -- Result :: String

-- stringLitE' :: Id -> String -> CoreExpr
-- stringLitE' unpackId = App (Var unpackId) . Lit . mkMachString

-- varMachStr' :: Id -> Var -> CoreExpr
-- varMachStr' unpackId = stringLitE' unpackId . var2String


{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-core" (promoteExprR reifyCoreExpr)
        [ "Turn a Core expression into a GADT construction" ]
    ]
