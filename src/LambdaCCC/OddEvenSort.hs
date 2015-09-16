{-# LANGUAGE CPP, GADTs, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.OddEvenSort
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Batcher's even-odd merge sort
----------------------------------------------------------------------

module LambdaCCC.OddEvenSort where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Data.Foldable (toList)
import Data.Traversable (Traversable)
import Control.Arrow (first)

import TypeUnary.TyNat (Z,S)
import TypeUnary.TyNat (N1,N2,N3,N4)
import TypeUnary.Nat (Nat(..),IsNat(..))

import Circat.Misc (Unop,transpose,inTranspose)
import Circat.Pair (Pair(..),sortP)
import Circat.RTree
import Circat.Shift (shiftL,shiftR)

msort :: (IsNat n, Ord a, Bounded a) => Unop (RTree n a)
msort = msort' nat

msort' :: (IsNat n, Ord a, Bounded a) => Nat n -> Unop (RTree n a)
msort' Zero     = id
msort' (Succ m) = inB (merge . fmap (msort' m))

merge :: (Ord a, Bounded a) => Unop (Pair (RTree n a))
merge = undefined

#if 0
msort = msort' nat

msort' :: (Ord a, Bounded a) => Nat n -> Unop (RTree n a)
msort' Zero     = id
msort' (Succ m) = B . merge m . fmap (msort' m) . unB

merge :: (Ord a, Bounded a) => Nat n -> Pair (LTree n a) -> LTree n (Pair a)
merge Zero = \ (L a :# L b) -> L (sortP (a :# b))

merge (Succ m) = tweak . transpose . fmap (merge m)

-- merge (Succ m) = inB (fmap sortP . (inTranspose.fmap) (merge m))

#if 0

B :: 

transpose :: Pair (LTree (S m) a) -> LTree (S m) (Pair a)

unB             :: LTree (S m) a -> LTree m (Pair a)

transpose       :: LTree m (Pair a) -> Pair (LTree m a)

fmap (merge m)  :: Pair (LTree m a) -> Pair (LTree m a)
transpose       :: Pair (LTree m a) -> LTree m (Pair a)
tweak           :: LTree m (Pair a) -> LTree m (Pair a)

B               :: LTree m (Pair a) -> LTree (S m) a

#endif

-- Oops! I have to compare odd/even, not even/odd.

tweak :: (Bounded a, Ord a) => Unop (LTree n (Pair a))
tweak ps = unB (fst (shiftL (bot,B (sortP <$> ps'))))
 where
   (bot,unB -> ps') = shiftR (B ps,maxBound)

#if 0

ps                                         :: LTree n (Pair a)
B ps                                       :: LTree (S n) a
(B ps, maxBound)                           :: (LTree (S n) a, a)
shiftR (B ps, maxBound)                    :: (a, LTree (S n) a)
bot                                        :: a
ps'                                        :: LTree n (Pair a)
sortP <$> ps'                              :: LTree n (Pair a)
B (sortP <$> ps')                          :: LTree (S n) a
(bot,B (sortP <$> ps'))                    :: (a,LTree (S n) a)
fst (shiftL (bot,B (sortP <$> ps')))       :: LTree (S n) a
unB (fst (shiftL (bot,B (sortP <$> ps')))) :: LTree n (Pair a)

#endif

#endif

ps0 :: RTree N1 (Pair Int)
ps0 = fromList [(1 :# 4),(3 :# 5)]

-- tweak = fmap sortP

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

test :: (IsNat n, Ord a, Bounded a) => RTree n a -> [a]
test = toList . msort

_t1 :: RTree N1 Int
_t1 = tree1 4 3

_t2 :: RTree N2 Int
_t2 = tree2 4 3 1 5

_t3 :: RTree N3 Int
_t3 = tree3 4 3 7 1 9 5 2 6

_t4 :: RTree N4 Int
_t4 = tree4 4 12 3 16 8 11 15 7 1 10 9 14 5 13 2 6
