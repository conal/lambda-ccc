-- Test of the computational correctness of my current FFT candidate.
--
-- Original author: David Banas <capn.freako@gmail.com>
-- Original date:   October 3, 2015
--
-- Copyright (c) 2015 David Banas; all rights reserved World wide.
--
-- I'm waiting for Conal to find time to look into my latest non-termination
-- failure through his compiler. While I do, I'm attempting, here, to verify
-- the computational correctness of my current FFT candidate.

{-# LANGUAGE GADTs #-}

module Main where

import Prelude hiding ({- id,(.), -}foldl,foldr,sum,product,zipWith,reverse,and,or,scanl,minimum,maximum)

import Data.Complex
import Data.Foldable (sum)

import TypeUnary.Nat (IsNat,natToZ,Nat(..),nat)
import Circat.Pair (Pair(..))
import qualified Circat.Pair as P
import qualified Circat.RTree as RT
import Circat.Misc (transpose)

type RTree = RT.Tree

-- Defining this, in response to a complaint from GHC.
-- My hope/assumption is that, given my particular use of Pair, it is
-- a completely moot definition.
instance Eq a => Ord (Complex a) where
    (<=) x y = x <= y

-- A 2-element FFT.
fft_2 :: Num a => Pair a -> Pair a
fft_2 p = P.toP (sum p, sum (P.secondP (0 -) p))

addPhase :: Nat n -> Complex Double -> Complex Double
addPhase Zero = id
addPhase n    = (* (cis ((-pi) / (natToZ n))))

fft_r2_dit :: IsNat n => RTree n (Complex Double) -> RTree n (Complex Double)
fft_r2_dit = fft_r2_dit' nat

fft_r2_dit' :: IsNat n => Nat n -> RTree n (Complex Double) -> RTree n (Complex Double)
fft_r2_dit' Zero        = error "Whoops! Shouldn't have ended up here."
fft_r2_dit' (Succ Zero) = RT.butterfly fft_2
fft_r2_dit' (Succ n)    = RT.butterfly (fft_2 . (P.secondP (addPhase n)))

main :: IO ()
-- Delta - Should produce: [1, 1, 1, 1] as output. Works.
-- main = print $ fft_r2_dit $ RT.tree2 (1.0 :+ 0.0) (0.0 :+ 0.0) (0.0 :+ 0.0) (0.0 :+ 0.0)

-- Constant - Should produce [4, 0, 0, 0] as output. First and last output elements seem to be swapped.
-- main = print $ fft_r2_dit $ RT.tree2 (1.0 :+ 0.0) (1.0 :+ 0.0) (1.0 :+ 0.0) (1.0 :+ 0.0)

-- Nyquist - Should produce [0, 0, 4, 0] as output. Works.
-- main = print $ fft_r2_dit $ RT.tree2 (1.0 :+ 0.0) ((-1.0) :+ 0.0) (1.0 :+ 0.0) ((-1.0) :+ 0.0)

-- Fundamental - Should produce [0, 2, 0, 2] as output. First and last output elements seem to be swapped.
main = print $ fft_r2_dit $ RT.tree2 (1.0 :+ 0.0) (0.0 :+ 0.0) ((-1.0) :+ 0.0) (0.0 :+ 0.0)

