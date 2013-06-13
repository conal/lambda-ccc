{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures, ViewPatterns #-}
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
import GHC.Pack (unpackCString#)

import GhcPlugins
import TypeRep (Type(..))
import Var

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
import LambdaCCC.Ty
import qualified LambdaCCC.Lambda as E
import qualified LambdaCCC.Ty     as E

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}


-- reify :: a -> E a
-- reify = error "reify: not implemented."

reifyCoreExpr :: RewriteH CoreExpr
reifyCoreExpr =
  do unitTId   <- findIdT 'UnitT
     boolTId   <- findIdT 'BoolT
     intTId    <- findIdT 'IntT
     pairTId   <- findIdT '(E.:*)
     funTId    <- findIdT '(E.:=>)
     varId     <- findIdT 'E.Var
     appId     <- findIdT '(E.:^)
     lamId     <- findIdT 'E.Lam
     varPId    <- findIdT 'E.VarP
     varString <- varToStringLitE' <$> findIdT 'unpackCString#
     let reifyT :: Type -> CoreExpr
         -- reifyT (TyVarTy v) 
         reifyT (TyConApp tc [])
           | isTupleTyCon tc && tyConArity tc == 0 = Var unitTId
           | tc ==  intTyCon                       = Var  intTId
           | tc == boolTyCon                       = Var boolTId
         reifyT (TyConApp tc [a,b])
           | isTupleTyCon tc && tyConArity tc == 2 =
             apps pairTId tys (reifyT <$> tys)
          where
            tys = [a,b]
--         reifyT (ForAllTy v t) = ForAllTy v (reifyT t)  -- ??  
         reifyT (splitFunTy_maybe -> Just (a,b)) =
           apps funTId tys (reifyT <$> tys)
          where
            tys = [a,b]
         reifyT t = error $ "reifyT: unhandled: " ++ showPpr tracingDynFlags t
         ----
         reifyE :: Unop CoreExpr
         reifyE (Var v) = apps varId [vt] [varString v, reifyT vt]
          where
            vt = varType v
         reifyE (Lit _) = undefined
         reifyE (App u v@(Type{})) = App (reifyE u) v
         reifyE (App u v) = apps appId [a,b] [reifyE u, reifyE v]
          where
            (a,b) = splitFunTy (exprType u)
         reifyE (Lam v e) | isTyVar v = Lam v (reifyE e)
                          | otherwise = apps lamId [vt, exprType e] [p,reifyE e]
          where
            vt = varType v
            p  = apps varPId [vt] [varString v, reifyT vt]
         reifyE _ = error "reifyE: incomplete"
     reifyE <$> idR


-- mkStringExpr is hanging for some reason, so for now I'm just creating
-- (type-incorrect) unboxed strings (NS)
varToStringLitE :: Var -> CoreExpr
-- varToStringLitE = mkStringExpr . var2String
varToStringLitE = Lit . mkMachString . var2String

-- mkStringExpr :: MonadThings m => String -> m CoreExpr  -- Result :: String

stringLitE' :: Id -> String -> CoreExpr
stringLitE' unpackId = App (Var unpackId) . Lit . mkMachString

varToStringLitE' :: Id -> Var -> CoreExpr
varToStringLitE' unpackId = stringLitE' unpackId . var2String



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
