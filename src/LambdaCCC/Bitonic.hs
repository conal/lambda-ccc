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

import Prelude hiding (reverse)

import Data.Functor ((<$>))
import Data.Foldable (toList)

import TypeUnary.TyNat (N1,N2,N3,N4)
import TypeUnary.Nat (IsNat(..),Nat(..))

import Circat.Pair
import Circat.RTree

import Circat.Misc (Unop,Reversible(..))

bsort :: (IsNat n, Ord a) => Unop (RTree n a)
bsort = bsort' nat
{-# INLINE bsort #-}

bsort' :: Ord a => Nat n -> Unop (RTree n a)
bsort' Zero     = id
bsort' (Succ m) = \ (B ts) ->
  merge (Succ m) (B (secondP reverse (bsort' m <$> ts)))
{-# INLINE bsort' #-}

-- Equivalently,

-- bsort' (Succ m) = \ (B (u :# v)) ->
--   merge (Succ m) (B (bsort' m u :# reverse (bsort' m v)))

-- Bitonic merge
merge :: Ord a => Nat n -> Unop (RTree n a)
merge n = butterfly' n sortP
{-# INLINE merge #-}

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

test :: (IsNat n, Ord a) => RTree n a -> [a]
test = toList . bsort

_t1 :: RTree N1 Int
_t1 = tree1 4 3

_t2 :: RTree N2 Int
_t2 = tree2 4 3 1 5

_t3 :: RTree N3 Int
_t3 = tree3 4 3 7 1 9 5 2 6

_t4 :: RTree N4 Int
_t4 = tree4 4 12 3 16 8 11 15 7 1 10 9 14 5 13 2 6
