{-# LANGUAGE TypeOperators, GADTs, KindSignatures, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Ty
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Typed types
----------------------------------------------------------------------

module LambdaCCC.Ty (HasTy(..),Ty(..)) where

import Control.Applicative (liftA2)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.ShowUtils

-- TODO: Try out the singletons library

-- | Typed type representation
data Ty :: * -> * where
  UnitT :: Ty Unit
  IntT  :: Ty Int
  BoolT :: Ty Bool
  (:*)  :: Ty a -> Ty b -> Ty (a :* b)
  (:=>) :: Ty a -> Ty b -> Ty (a :=> b)

instance Show (Ty a) where
  showsPrec _ UnitT     = showString "Unit"
  showsPrec _ IntT      = showString "Int"
  showsPrec _ BoolT     = showString "Bool"
  showsPrec p (a :*  b) = showsOp2' ":*"  (7,AssocLeft ) p a b
  showsPrec p (a :=> b) = showsOp2' ":=>" (1,AssocRight) p a b

instance IsTy Ty where
  UnitT     `tyEq` UnitT       = Just Refl
  IntT      `tyEq` IntT        = Just Refl
  BoolT     `tyEq` BoolT       = Just Refl
  (a :*  b) `tyEq` (a' :*  b') = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  (a :=> b) `tyEq` (a' :=> b') = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  _         `tyEq` _           = Nothing

-- | Synthesize a type
class HasTy a where typ :: Ty a

instance HasTy Unit where typ = UnitT
instance HasTy Int  where typ = IntT
instance HasTy Bool where typ = BoolT
instance (HasTy a, HasTy b) => HasTy (a :*  b) where typ = typ :*  typ
instance (HasTy a, HasTy b) => HasTy (a :=> b) where typ = typ :=> typ
