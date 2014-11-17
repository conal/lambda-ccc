{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Bitonic
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Bitonic sort
----------------------------------------------------------------------

module LambdaCCC.Bitonic where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Data.Foldable (toList)
import Control.Applicative (liftA2)

import TypeUnary.TyNat (N1,N2,N3,N4)
import TypeUnary.Nat (IsNat(..),Nat(..))

import Circat.Pair
import Circat.RTree

import Circat.Misc (Unop,inTranspose)

bsort :: (IsNat n, Ord a) => Bool -> Unop (RTree n a)
bsort = bsort' nat
{-# INLINE bsort #-}

bsort' :: Ord a => Nat n -> Bool -> Unop (RTree n a)
bsort' Zero _       = id
bsort' (Succ m) up = \ (B ts) ->
  merge (Succ m) up (B (liftA2 (bsort' m) (up :# not up) ts))
{-# INLINE bsort' #-}

-- bsort' (Succ m) up = \ (B (u :# v)) ->
--   merge (Succ m) up (B (bsort' m up u :# bsort' m (not up) v))

-- Bitonic merge
merge :: Ord a => Nat n -> Bool -> Unop (RTree n a)
merge Zero     _  = id
merge (Succ m) up = \ (B ts) -> B (merge m up <$> inTranspose (fmap (cswap up)) ts)
{-# INLINE merge #-}

cswap :: Ord a => Bool -> Unop (Pair a)
cswap up (a :# b) = if (a <= b) == up then a :# b else b :# a
{-# INLINE cswap #-}

test :: (IsNat n, Ord a) => Bool -> RTree n a -> [a]
test up = toList . bsort up

testUp, testDown :: (IsNat n, Ord a) => RTree n a -> [a]
testUp   = test True
testDown = test False

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

_t1 :: RTree N1 Int
_t1 = tree1 4 3

_t2 :: RTree N2 Int
_t2 = tree2 4 3 1 5

_t3 :: RTree N3 Int
_t3 = tree3 4 3 7 1 9 5 2 6

_t4 :: RTree N4 Int
_t4 = tree4 4 12 3 16 8 11 15 7 1 10 9 14 5 13 2 6
