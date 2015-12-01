{-# LANGUAGE CPP, FlexibleContexts, ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-} -- for LFScan
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.RadixSort
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Parallel radix sort
----------------------------------------------------------------------

module LambdaCCC.RadixSort where

-- TODO: explicit exports

import Prelude hiding (sum)

import Data.Foldable (Foldable,sum,toList)
import Control.Applicative (Applicative(..),liftA2)
import Control.Arrow ((***),first)

import TypeUnary.Nat -- (IsNat(..))
import TypeUnary.Vec (Vec,vec1,(<+>))

import Circat.RTree
import Circat.Scan (LScan(..),LFScan,lsums)

type Bits n = Vec n Bool

oneTree :: (IsNat n, Num b) => Bits n -> Tree n b
oneTree v = update v (const 1) (pure 0)

histogramStep ::  (IsNat n, Num b) =>
                  RTree n b -> Bits n -> RTree n b
histogramStep w v = w + oneTree v

histogramFold :: (Foldable f, Functor f, IsNat n, Num b) =>
                 f (Bits n) -> RTree n b
histogramFold = sum . fmap oneTree

histogramScan :: (LFScan f, IsNat n, Num b) =>
                 f (Bits n) -> (f (RTree n b), RTree n b)
histogramScan = lsums . fmap oneTree

#if 0

     oneTree ::    Bits n    ->     Tree n b
fmap oneTree :: f (Bits n)   ->  f (Tree n b)
lsums        :: f (Tree n b) -> (f (Tree n b), b)

#endif

positions :: (Applicative f, LScan f, LScan (RTree n), IsNat n, Num b) =>
             f (Bits n) -> f b
positions vs = liftA2 combine partials vs
 where
   (partials,hist)   = histogramScan vs
   (starts,_)        = lsums hist
   combine partial v = (starts + partial) ! v

#if 0

vs       :: f (Bits n)
partials :: f (RTree n b)
hist     :: RTree n b
starts   :: RTree n b
combine  :: RTree n b -> Bits n -> b

#endif

#if 0
-- Variation: (starts + partial) ! v  -->  (starts ! v) + (partial ! v).
-- I get somewhat larger circuits.
positions' :: (Applicative f, LScan f, LScan (RTree n), IsNat n, Num b) =>
              f (Bits n) -> f b
positions' vs = liftA2 combine partials vs
 where
   (partials,hist)   = histogramScan vs
   (starts,_)        = lsums hist
   combine partial v = (starts ! v) + (partial ! v)
#endif

-- TODO: Generalize to other tries

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- Test histogramFold
testHF :: (Functor f, Foldable f, IsNat n, Num b) =>
          f (Bits n) -> [b]
testHF = toList . histogramFold

-- Test histogramScan
testHS :: (LFScan f, Foldable f, IsNat n, Num b) =>
          f (Bits n) -> ([[b]], [b])
testHS = first toList . (fmap toList *** toList) . histogramScan

-- Test positions
testPs :: (Foldable f, Applicative f, LScan f, LScan (RTree n), IsNat n, Num b) =>
          f (Bits n) -> [b]
testPs = toList . positions

-- testSort vs = 

f,t :: Bits N1
f = vec1 False
t = vec1 True

l1 :: [Bits N1]
l1 = [t,f,f,t,f]

t1 :: Tree N2 (Bits N1)
t1 = tree2 t f f t

-- > testHF l1
-- [3,2]
-- > testHF t1
-- [2,2]
-- > testHF l2
-- [3,2,2,1]
--
-- > testHS t1
-- ([[0,0],[0,1],[1,1],[2,1]],[2,2])
--
-- > testPs t1
-- [2,0,1,3]

ff,ft,tf,tt :: Bits N2
[ff,ft,tf,tt] = liftA2 (<+>) [f,t] [f,t]

l2 :: [Bits N2]
l2 = [tf,ft,ff,tt,tf,ff,ff,ft]

t2 :: Tree N3 (Bits N2)
t2 = tree3 tf ft ff tt tf ff ff ft

-- > testHS t1
-- ([[0,0],[0,1],[1,1],[2,1]],[2,2])
--
-- > testHS t2
-- ([[0,0,0,0],[0,0,1,0],[0,1,1,0],[1,1,1,0],[1,1,1,1],[1,1,2,1],[2,1,2,1],[3,1,2,1]],[3,2,2,1])
-- 
-- > testPs t2
-- [5,3,0,7,6,1,2,4]
