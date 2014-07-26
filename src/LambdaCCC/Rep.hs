{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Rep
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert to and from standard representations
----------------------------------------------------------------------

module LambdaCCC.Rep where

import LambdaCCC.Misc (Unit,(:+),(:*))

import TypeUnary.TyNat (Z,S)
import TypeUnary.Nat (Nat(..),IsNat(..))
import TypeUnary.Vec (Vec(..),unConsV)
import Circat.Pair (Pair(..),toP,fromP)
import Circat.RTree (Tree(..),toL,unL,toB,unB)

import Circat.Category (Rep)

-- TODO: explicit exports

#if 0
class HasRep a where
  repr :: a -> Rep a
  abst :: Rep a -> a
#else
class HasRep a where
  repr :: a' ~ Rep a => a -> a'
  abst :: a' ~ Rep a => a' -> a

-- More convenient construction:
repr' :: HasRep a => a -> Rep a
repr' = repr
abst' :: HasRep a => Rep a -> a
abst' = abst
#endif

type instance Rep (Pair a) = a :* a
instance HasRep (Pair a) where
  repr (a :# a') = (a,a')
  abst (a,a') = (a :# a')

type instance Rep (Vec Z a) = ()
instance HasRep (Vec Z a) where
  repr ZVec = ()
  abst () = ZVec

type instance Rep (Vec (S n) a) = a :* Vec n a
instance HasRep (Vec (S n) a) where
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)

type instance Rep (Tree Z a) = a
instance HasRep (Tree Z a) where
  repr (L a) = a
  abst a = L a

type instance Rep (Tree (S n) a) = Pair (Tree n a)
instance HasRep (Tree (S n) a) where
  repr (B ts) = ts
  abst ts = B ts

-- TODO: Vec

-- TODO: Maybe switch Control.Newtype
