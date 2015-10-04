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

import Control.Monad (forM_)
import Data.Complex
import Data.Foldable (sum)
import Data.Newtypes.PrettyDouble

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
fft_2 p = P.toP (sum p, sum (P.secondP (0 -) p))

-- Phasor, as a function of tree depth.
addPhase :: Nat n -> Complex PrettyDouble -> Complex PrettyDouble
addPhase Zero = id
addPhase n    = (* (cis ((-pi) / (natToZ n))))

-- Radix-2, DIT FFT
fft_r2_dit :: IsNat n => RTree n (Complex PrettyDouble) -> RTree n (Complex PrettyDouble)
fft_r2_dit = fft_r2_dit' nat

fft_r2_dit' :: IsNat n => Nat n -> RTree n (Complex PrettyDouble) -> RTree n (Complex PrettyDouble)
fft_r2_dit' Zero        = error "Whoops! Shouldn't have ended up here."
fft_r2_dit' (Succ Zero) = RT.butterfly fft_2
fft_r2_dit' (Succ n)    = RT.butterfly (fft_2 . (P.secondP (addPhase n)))
-- fft_r2_dit' n           = RT.butterfly (fft_2 . (P.secondP (addPhase n)))

-- Test config.
realData :: [[PrettyDouble]]
realData = [  [1.0,   0.0,   0.0,   0.0 ]  -- Delta
            , [1.0,   1.0,   1.0,   1.0 ]  -- Constant
            , [1.0, (-1.0),  1.0, (-1.0)]  -- Nyquist
            , [1.0,   0.0, (-1.0),  0.0 ]  -- Fundamental
            , [0.0,   1.0,   0.0, (-1.0)]  -- Fundamental w/ 90-deg. phase lag
           ]
complexData :: [[Complex PrettyDouble]]
complexData = map (map (:+ 0.0)) realData

myTree2 [w, x, y, z] = RT.tree2 w x y z
myTree2 _            = error "Something went horribly wrong!"

-- Discrete Fourier Transform (DFT) (our "truth" reference)
-- O(n^2)
--
dft :: RealFloat a => [Complex a] -> [Complex a]
dft xs = [ sum [ x * exp((0.0 :+ (-1.0)) * 2 * pi / lenXs * fromIntegral(k * n))
                 | (x, n) <- zip xs [0..]
               ]
           | k <- [0..(length xs - 1)]
         ]
    where lenXs = fromIntegral $ length xs

main :: IO ()
main = do
    forM_ complexData (\x -> do
        putStr "\nTesting input: "
        print x
        putStr "Expected output: "
        print $ dft x
        putStr "Actual output:   "
        print $ fft_r2_dit $ myTree2 x
        )

