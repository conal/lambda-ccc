{-# LANGUAGE GADTs, KindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Type
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Simple GADT of typed types
----------------------------------------------------------------------

module LambdaCCC.Type where

-- TODO: explicit exports

import Control.Applicative (liftA2)

import Data.Proof.EQ
import Data.IsTy

import LambdaCCC.Misc (Unit,(:*),(:=>))

-- | Typed type representation
data Ty :: * -> * where
  UnitT :: Ty Unit
  IntT  :: Ty Int
  BoolT :: Ty Bool
  PairT :: Ty a -> Ty b -> Ty (a :* b)
  FunT  :: Ty a -> Ty b -> Ty (a :=> b)

instance IsTy Ty where
  UnitT     `tyEq` UnitT       = Just Refl
  IntT      `tyEq` IntT        = Just Refl
  BoolT     `tyEq` BoolT       = Just Refl
  PairT a b `tyEq` PairT a' b' = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  FunT  a b `tyEq` FunT  a' b' = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  _         `tyEq` _           = Nothing
