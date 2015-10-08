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

import Control.Applicative
import Control.Arrow
import Control.Monad (forM_)
import Data.Complex
import Data.Foldable (sum)
import Data.Newtypes.PrettyDouble
import TypeUnary.Nat (IsNat, natToZ, Nat(..), nat, N2)

import Circat.Pair (toP, fromP)
import Circat.Scan (scanlTEx)
import qualified Circat.Pair as P
import qualified Circat.RTree as RT
import Circat.RTree (bottomSplit)

type RTree = RT.Tree

-- Phasor, as a function of tree depth.
addPhase :: (IsNat n, RealFloat a, Enum a) => RTree n (Complex a) -> RTree n (Complex a)
addPhase = addPhase' nat

addPhase' :: (IsNat n, RealFloat a, Enum a) => Nat n -> RTree n (Complex a) -> RTree n (Complex a)
addPhase' Zero = id
addPhase' n    = (* (scanlTEx (*) 1 (pure phaseDelta)))
    where phaseDelta = cis ((-pi) / (2 ** (natToZ n)))

-- Radix-2, DIT FFT
fft_r2_dit :: (IsNat n, RealFloat a, Enum a) => RTree n (Complex a) -> RTree n (Complex a)
fft_r2_dit = fft_r2_dit' nat

fft_r2_dit' :: (RealFloat a, Enum a) => Nat n -> RTree n (Complex a) -> RTree n (Complex a)
fft_r2_dit'  Zero    = id
fft_r2_dit' (Succ n) = RT.toB . toP . ((uncurry (+)) &&& (uncurry (-))) . fromP . P.secondP addPhase . fmap (fft_r2_dit' n) . bottomSplit

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

myTree2 :: [a] -> RTree N2 a
myTree2 [w, x, y, z] = RT.tree2 w x y z
myTree2 _            = error "Something went horribly wrong!"

-- Discrete Fourier Transform (DFT) (our "truth" reference)
-- O(n^2)
--
dft :: RealFloat a => [Complex a] -> [Complex a]
dft xs = [ sum [ x * exp((0.0 :+ (-1.0)) * 2 * pi / lenXs * fromIntegral(k * n))
                 | (x, n) <- Prelude.zip xs [0..]
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

