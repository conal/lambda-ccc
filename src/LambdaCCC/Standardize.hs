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

import Data.Functor ((<$>))
import Control.Applicative (liftA2)
import Control.Arrow ((***))
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

tracing :: Bool
tracing = True

ttrace :: String -> a -> a
ttrace | tracing   = trace
       | otherwise = flip const

instance Standardizable Type where
  standardize ty | ttrace ("standardize type " ++ unsafeShowPpr ty) False = undefined
  standardize t | isStandardType t = -- ttrace "standard type" $
                                     t
  standardize (coreView -> Just ty) = standardize ty
  standardize (a `FunTy` b) = standardize a `FunTy` standardize b
  standardize _ty@(TyConApp _tc@(tyConDataCons_maybe -> Just dcs0) tcTys)
    | [argTys] <- catMaybes mbs
      = foldT unitTy pairTy (toTree (map standardize argTys))
    | w <- catMaybes mbs
      , ttrace (  "standardize: data type "++ uqName (tyConName _tc)
                ++" with " ++ show (length w)
                ++" consistent constructors") False = undefined
   where
     mbs   = map (dcApp tcTys) dcs0
  standardize (ForAllTy v ty) = ForAllTy v (standardize ty)
  standardize ty = -- error "standardize on types: unhandled type"
                   ty

dcApp :: [Type] -> DataCon -> Maybe [Type]
dcApp tcTys dc = -- ttrace (unsafeShowPpr info) $
                 mbTys
 where
   tcSub       = zipOpenTvSubst (dataConUnivTyVars dc) tcTys
   bodyTy      = dropForAlls (dataConRepType dc)
   valArgs     = filter (not.isCoVarType) (fst (splitFunTys bodyTy))
   (eqVs,eqTs) = unzip (dataConEqSpec dc)
   mbUSub      = unionTvSubst tcSub <$>
                 tcUnifyTys (const BindMe) (Type.substTyVar tcSub <$> eqVs) eqTs
   mbTys       = (\ sub -> Type.substTy sub <$> valArgs) <$> mbUSub

--    info = ( (tcTys,dc)
--           , ( dataConRepType dc
--             , bodyTy
--             , valArgs
--             , dataConUnivTyVars dc
--             , dataConExTyVars dc
--             , dataConEqSpec dc )
--           , (tcSub,mbUSub,mbTys)
--           )

onVarType :: Unop Type -> Unop Var
onVarType f v = setVarType v (f (varType v))

instance Standardizable Var where
--   standardize x | ttrace ("standardize var " ++ unsafeShowPpr x) False = undefined
  -- standardize v = setVarType v (standardize (varType v))
--   standardize v = ttrace ("standardize type for var " ++ unsafeShowPpr (v,varType v)) $
--                   onVarType standardize v
  standardize v = ttrace ("standardize var " ++ unsafeShowPpr (v,ty,ty')) $
                  setVarType v ty'
   where
     ty = varType v
     ty' = standardize ty

instance Standardizable CoreExpr where
  -- standardize x | ttrace ("standardize expr " ++ unsafeShowPpr x) False = undefined
  standardize (Type t)       = Type (standardize t)
  standardize (Coercion co)  = Coercion (standardize co)
  standardize e@(collectArgs -> ( Var (isDataConWorkId_maybe -> Just con)
                                , filter (not.isTyCoArg) -> valArgs ))
    | isStandardType (exprType e) = ttrace "standard expression type" $
                                    e
    | let argsNeeded = dataConSourceArity con - length valArgs, argsNeeded > 0 =
        standardize (etaExpand argsNeeded e)
    | otherwise =
        ttrace ("standardize constructor application") $
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
    case' (standardize e)
          w'
          (standardize ty)
          (map (standardizeAlt w (tyConAppArgs (exprType e))) alts)
   where
     -- We may rewrite an alt to use wild, so update its OccInfo to unknown.
     w' = setIdOccInfo (standardize w) NoOccInfo
  standardize (Cast e _co)   = standardize e  -- Experiment
  -- standardize (Cast e co)    = mkCast e' co'
  --  where
  --    e'  = standardize e
  --    co' = mkUnivCo (coercionRole co) (exprType e') (standardize ty')
  --    Pair _ ty' = coercionKind co

  standardize (Tick t e)     = Tick t (standardize e)

case' :: CoreExpr -> Var -> Type -> [CoreAlt] -> CoreExpr
case' scrut wild _bodyTy [(DEFAULT,[],body)] =
  Let (NonRec wild scrut) body
case' scrut wild bodyTy alts = Case scrut wild bodyTy alts

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
  -- standardize x | ttrace ("standardize bind " ++ unsafeShowPpr x) False = undefined
  standardize (NonRec x e) =
    NonRec (standardize x) (standardize e)
  standardize (Rec ves)    =
    Rec (map (standardize *** standardize) ves)

-- vTy :: Var -> (Var,Type)
-- vTy v = (v, varType v)

standardizeAlt :: Var -> [Type] -> Unop CoreAlt
standardizeAlt wild tcTys (DataAlt dc,vs,e) =
--   ttrace ("standardizeAlt:\n" ++
--           unsafeShowPpr ((dc,vTy <$> vs,e),(valVars0,valVars)
--                         , alt' )) $
  alt'
 where
   alt' | [x] <- valVars = (DEFAULT, [], standardize (subst [(x,Var wild)] e))
        | otherwise      =
            (tupCon (length valVars), standardize <$> valVars, standardize e)
   valVars0 = filter (not . liftA2 (||) isTypeVar isCoVar) vs
   valVars  = onVarType sub <$> valVars0  -- needed?
   sub      = Type.substTy (Type.zipOpenTvSubst tvs tcTys)
   tvs      = fst (splitForAllTys (dataConRepType dc))
standardizeAlt _ _ _ = error "standardizeAlt: non-DataAlt"

tupCon :: Int -> AltCon
tupCon 1 = DEFAULT
tupCon n = DataAlt (tupleCon BoxedTuple n)


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
