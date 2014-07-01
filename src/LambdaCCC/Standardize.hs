{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module LambdaCCC.Standardize (standardizeR) where

-- import Prelude hiding (id,(.))

import Control.Arrow ((***))
import Data.Functor ((<$>))
import Data.Maybe (catMaybes)
-- import Data.List (partition)

import Unify (tcUnifyTys,BindFlag(..))
import CoreArity (etaExpand)

import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Core (CoreProg(..))

import HERMIT.Extras hiding (findTyConT, labeled)

import qualified Type

class Standardizable a where standardize :: Unop a

isStandardType :: Type -> Bool
isStandardType t = any ($ t) [isBoolTy,isIntTy,isUnitTy]

#define Trace

instance Standardizable Type where
#ifdef Trace
  standardize ty | trace ("standardize type " ++ unsafeShowPpr ty) False = undefined
#endif
  standardize t | isStandardType t = trace "standard type" $
                                     t
  standardize (coreView -> Just ty) = standardize ty
  standardize (a `FunTy` b) = standardize a `FunTy` standardize b
  standardize _ty@(TyConApp _tc@(tyConDataCons_maybe -> Just dcs0) tcTys)
    | [argTys] <- catMaybes mbs
      = foldT unitTy pairTy (toTree (map standardize argTys))
#ifdef Trace
    | w <- catMaybes mbs
      , trace (   "standardize: data type "++ uqName (tyConName _tc)
                ++" with " ++ show (length w)
                ++ " consistent constructors") False = undefined
#endif
   where
     mbs   = map (dcApp tcTys) dcs0
  standardize (ForAllTy v ty) = ForAllTy v (standardize ty)
  standardize ty = -- error "standardize on types: unhandled type"
                   ty

dcApp :: [Type] -> DataCon -> Maybe [Type]
dcApp tcTys dc =
#ifdef Trace
                 trace (unsafeShowPpr info) $
#endif
                 mbTys
 where
   tcSub = zipOpenTvSubst (dataConUnivTyVars dc) tcTys
   bodyTy = dropForAlls (dataConRepType dc)
   valArgs = filter (not.isCoVarType) (fst (splitFunTys bodyTy))
   (eqVs,eqTs) = unzip (dataConEqSpec dc)
   mbUSub = unionTvSubst tcSub <$>
            tcUnifyTys (const BindMe) (Type.substTyVar tcSub <$> eqVs) eqTs
   mbTys = (\ sub -> Type.substTy sub <$> valArgs) <$> mbUSub
#ifdef Trace
   info = ( (tcTys,dc)
          , ( dataConRepType dc
            , bodyTy
            , valArgs
            , dataConUnivTyVars dc
            , dataConExTyVars dc
            , dataConEqSpec dc )
          , (tcSub,mbUSub,mbTys)
          )
#endif

instance Standardizable Var where
#ifdef Trace
  standardize x | trace ("standardize var " ++ unsafeShowPpr x) False = undefined
#endif
  standardize v = setVarType v (standardize (varType v))

instance Standardizable CoreExpr where
#ifdef Trace
  standardize x | trace ("standardize expr " ++ unsafeShowPpr x) False = undefined
#endif
  standardize (Type t)       = Type (standardize t)
  standardize (Coercion co)  = Coercion (standardize co)
  standardize e@(collectArgs -> ( Var (isDataConWorkId_maybe -> Just con)
                                , filter (not.isTyCoArg) -> valArgs ))
    | isStandardType (exprType e) = trace "standard expression type" $
                                    e
    | let argsNeeded = dataConSourceArity con - length valArgs, argsNeeded > 0 =
        standardize (etaExpand argsNeeded e)
    | otherwise =
        trace ("standardize constructor application") $
        foldT (mkCoreTup []) (\ u v  -> mkCoreTup [u,v])
              (toTree (map standardize valArgs))
    | otherwise =
        standardize (etaExpand 1 e)
  standardize (Var v)        = Var (standardize v)
  standardize e@(Lit _)      = e
  standardize (App u v)      = App (standardize u) (standardize v)
  standardize (Lam x e)      = Lam (standardize x) (standardize e)
  standardize (Let b e)      = Let (standardize b) (standardize e)
  standardize (Case e w ty alts) =
    Case (standardize e)
         (standardize w)
         (standardize ty)
         (map (standardizeAlt (tyConAppArgs (exprType e))) alts)
  standardize (Cast e co)    = mkCast (standardize e) (standardize co)
  standardize (Tick t e)     = Tick t (standardize e)

-- standardizeConToExpr :: DataCon -> CoreExpr
-- standardizeConToExpr dc = go (dataConRepType dc)
--  where
--    go (ForAllTy v ty) = mkLam v (go ty)
--    go (FunTy a b) = 
--                           pairTreeE (map Var valArgs)
--  where
--    valArgs = filter (not.isCoVarType)
--               (fst (splitFunTys (dropForAlls (dataConRepType dc))))

-- pairTreeE :: [CoreExpr] -> CoreExpr
-- pairTreeE = foldT (mkCoreTup []) (\ u v  -> mkCoreTup [u,v]) . toTree


-- isCoercion :: Expr b -> Bool
-- isCoercion (Coercion _) = True
-- isCoercion _ = False

instance Standardizable CoreBind where
#ifdef Trace
  standardize x | trace ("standardize bind " ++ unsafeShowPpr x) False = undefined
#endif
  standardize (NonRec x e) =
    NonRec (standardize x) (standardize e)
  standardize (Rec ves)    =
    Rec (map (standardize *** standardize) ves)

standardizeAlt :: [Type] -> Unop CoreAlt
standardizeAlt tcTys (DataAlt dc,vs,e) =
  ( DataAlt (tupleCon BoxedTuple (length argTys))
  , standardize <$> drop (length tvs) vs
  , standardize e )
 where
   (tvs,body) = splitForAllTys (dataConRepType dc)
   argTys = fst (splitFunTys (Type.substTyWith tvs tcTys body))
standardizeAlt _ _ = error "standardizeAlt: non-DataAlt"

-- TODO: I may need nested patterns, which then requires generating new
-- variables.
-- For now, generate n-tuples

instance Standardizable Coercion where
  -- For now, convert coercions to universal.
  standardize co =
    mkUnivCo (coercionRole co) (standardize ty) (standardize ty')
   where
     Pair ty ty' = coercionKind co

instance Standardizable CoreProg where
  standardize ProgNil = ProgNil
  standardize (ProgCons bind prog) =
    ProgCons (standardize bind) (standardize prog)

-- TODO: Parametrize by bndr

standardizeR :: (MonadCatch m, Standardizable a, SyntaxEq a) =>
                Rewrite c m a
standardizeR = changedArrR standardize
