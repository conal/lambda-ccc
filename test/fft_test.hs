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
import Data.Foldable (Foldable(..),sum,product,and,or,toList,minimum,maximum)

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat,natToZ,Nat(..),nat)
import Circat.Pair (Pair(..))
import qualified Circat.Pair as P
import qualified Circat.RTree as RT

type RTree = RT.Tree

-- Defining this, in response to a complaint from GHC.
-- My hope/assumption is that, given my particular use of Pair, it is
-- a completely moot definition.
instance Eq a => Ord (Complex a) where
    (<=) x y = x <= y

-- A 2-element FFT.
fft_2 :: Num a => Pair a -> Pair a
fft_2 p = P.toP (sum p, sum p')
    where p' = P.toP (x, -y)
          x  = P.fstP p
          y  = P.sndP p
-- fft_2 p = P.toP (sum p', sum (secondP (-) p'))
--   where p' = secondP addPhasors p

addPhase :: Nat n -> Complex Double -> Complex Double
addPhase Zero = id
addPhase n    = (* (cis ((-pi) / (natToZ n))))

fft_r2_dit :: IsNat n => RTree n (Complex Double) -> RTree n (Complex Double)
fft_r2_dit = fft_r2_dit' nat

fft_r2_dit' :: IsNat n => Nat n -> RTree n (Complex Double) -> RTree n (Complex Double)
fft_r2_dit' Zero = RT.butterfly fft_2
fft_r2_dit' n    = RT.butterfly (fft_2 . (P.secondP (addPhase n)))

main :: IO ()
main = putStrLn "Hello, World!"

