{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
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

-- TODO: explicit exports

class HasRep a where
  type Rep a
  repr :: a -> Rep a
  abst :: Rep a -> a

instance HasRep (Pair a) where
  type Rep (Pair a) = a :* a
  repr (a :# a') = (a,a')
  abst (a,a') = (a :# a')

instance HasRep (Tree Z a) where
  type Rep (Tree Z a) = a
  repr (L a) = a
  abst a = L a

instance HasRep (Tree (S n) a) where
  type Rep (Tree (S n) a) = Pair (Tree n a)
  repr (B ts) = ts
  abst ts = B ts

-- TODO: Vec

-- TODO: Maybe switch Control.Newtype
