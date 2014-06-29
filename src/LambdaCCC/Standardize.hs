{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Standardize
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Transform away all non-standard types
----------------------------------------------------------------------

-- #define SizedTypes

module LambdaCCC.Standardize where

-- TODO: explicit exports
import Prelude hiding (id,(.))

import Control.Category (id,(.))
import Control.Applicative (pure,(<*>))
import Control.Arrow (arr)
import Data.Functor ((<$>))
import Data.Maybe (catMaybes)

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT, labeled)

import qualified Type

type InTvM a = TvSubst -> a

type ReTv a = a -> InTvM a

class Standardizable a where standardize :: ReTv a

instance Standardizable Type where
  standardize l@(LitTy {}) = pure l
  standardize (coreView -> Just ty) = standardize ty
  standardize (TyVarTy v) = flip Type.substTyVar v
  standardize (a `FunTy` b) = FunTy <$> standardize a <*> standardize b
  standardize t@(TyConApp tc []) | tc `elem` [boolTyCon, intTyCon] = pure t
  standardize ty@(TyConApp (tyConDataCons_maybe -> Just dcs0) tcTys0) =
    do tcTys <- mapM standardize tcTys0
       mbs   <- mapM (dcApp ty tcTys) dcs0
       case catMaybes mbs of
         [argTys] -> pure $ foldT unitTy pairTy (toTree argTys)
         _ -> fail "standardize: data type with multiple consistent constructors"
  standardize (ForAllTy v ty) =
    ForAllTy v <$> standardize ty       -- TODO: check for v in sub
  standardize ty = flip Type.substTy ty

dcApp :: Type -> [Type] -> DataCon -> InTvM (Maybe [Type])
dcApp ty tcTys dc sub =
  (\ xsub -> Type.substTy xsub <$> argTys) <$> mbExtraSub
 where
   (tvs,body) = splitForAllTys (dataConRepType dc)
   (argTys,resTy) =
     splitFunTys (Type.substTy sub (Type.substTyWith tvs tcTys body))
   mbExtraSub = tcUnifyTy ty resTy

instance Standardizable Var where
  standardize x = \ sub -> setVarType x (Type.substTy sub (varType x))

instance Standardizable CoreExpr where
  standardize (Var x)        = Var <$> standardize x
  standardize e@(Lit _)      = pure e
  standardize (App u v)      = App <$> standardize u <*> standardize v
  standardize (Lam x e)      = Lam <$> standardize x <*> standardize e
  standardize (Let b e)      = Let <$> standardize b <*> standardize e
  standardize (Case e w ty alts) =
    Case <$> standardize e
         <*> standardize w
         <*> standardize ty
         <*> mapM (standardizeAlt (exprType e)) alts
  standardize (Cast e co)    = mkCast <$> standardize e <*> standardize co
  standardize (Tick t e)     = Tick t <$> standardize e
  standardize (Type t)       = Type <$> standardize t
  standardize (Coercion co)  = Coercion <$> standardize co

instance Standardizable CoreBind where
  standardize (NonRec x e) =
    NonRec <$> standardize x <*> standardize e
  standardize (Rec ves)    =
    Rec <$> mapM (\ (x,e) -> (,) <$> standardize x <*> standardize e) ves

standardizeAlt :: Type -> ReTv CoreAlt
standardizeAlt scrutTy (con,vs,e) sub =
   do sub' <- extendTvSubstVars vs sub
      return (con, vs, retypeExpr e sub')


instance Standardizable Coercion where
  -- For now, convert coercions to universal.
  standardize co =
    mkUnivCo (coercionRole co) <$> standardize ty <*> standardize ty'
   where
     Pair ty ty' = coercionKind co


-- TODO: Parametrize by bndr
