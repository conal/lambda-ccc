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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Prelude hiding ({- id,(.), -}foldl,foldr,sum,product,zipWith,reverse,and,or,scanl,minimum,maximum)

import Control.Applicative
import Control.Arrow
import Control.Monad (forM_, unless)
import Data.Complex
import Data.Foldable (Foldable, sum, foldl')
import Data.Newtypes.PrettyDouble
import System.Exit (exitFailure)
import TypeUnary.Nat (IsNat, Nat(..), nat, N2, N3, N4, N5)  -- , N6)

-- import Test.QuickCheck (choose, vectorOf, elements, collect)
import Test.QuickCheck (choose, vectorOf)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.All (quickCheckAll)

import Circat.Scan (lproducts, LScan)
import qualified Circat.Pair as P
import qualified Circat.RTree as RT
import Circat.RTree (bottomSplit)

type RTree = RT.Tree

-- FFT, as a class
-- (The LScan constraint comes from the use of 'lproducts', in 'addPhase'.)
class (LScan f) => FFT f a where
    fft  :: f a -> f a  -- Computes the FFT of a functor.

-- Note that this definition of the FFT instance for Pair assumes DIT.
-- How can we eliminate this assumption and make this more general?
instance (RealFloat a, Applicative f, Foldable f, Num (f (Complex a)), FFT f (Complex a)) => FFT P.Pair (f (Complex a)) where
    fft = P.inP (uncurry (+) &&& uncurry (-)) . P.secondP addPhase . fmap fft

instance (IsNat n, RealFloat a) => FFT (RTree n) (Complex a) where
    fft = fft' nat
        where   fft' :: (RealFloat a) => Nat n -> RTree n (Complex a) -> RTree n (Complex a)
                fft' Zero     = id
                fft' (Succ _) = inDIT fft
                    where   inDIT g  = RT.toB . g . bottomSplit

-- Adds the proper phase adjustments to a functor containing Complex RealFloats,
-- and instancing Num.
addPhase :: (Applicative f, Foldable f, LScan f, RealFloat a, Num (f (Complex a))) => f (Complex a) -> f (Complex a)
addPhase = liftA2 (*) id phasor
  where phasor f = fst $ lproducts (pure phaseDelta)
          where phaseDelta = cis ((-pi) / fromIntegral n)
                n          = flen f

-- Gives the "length" (i.e. - number of elements in) of a Foldable.
-- (Soon, to be provided by the Foldable class, as "length".)
flen :: (Foldable f) => f a -> Int
flen = foldl' (flip ((+) . const 1)) 0

-- Test config.
realData :: [[PrettyDouble]]
realData = [  [1.0,   0.0,   0.0,   0.0]  -- Delta
            , [1.0,   1.0,   1.0,   1.0]  -- Constant
            , [1.0,  -1.0,   1.0,  -1.0]  -- Nyquist
            , [1.0,   0.0,  -1.0,   0.0]  -- Fundamental
            , [0.0,   1.0,   0.0,  -1.0]  -- Fundamental w/ 90-deg. phase lag
           ]
complexData :: [[Complex PrettyDouble]]
complexData = map (map (:+ 0.0)) realData

myTree2 :: [a] -> RTree N2 a
myTree2 [w, x, y, z] = RT.tree2 w x y z
myTree2 _            = error "Something went horribly wrong!"

myTree3 :: [a] -> RTree N3 a
myTree3 [a, b, c, d, e, f, g, h] = RT.tree3 a b c d e f g h
myTree3 _            = error "Something went horribly wrong!"

myTree4 :: [a] -> RTree N4 a
myTree4 [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = RT.tree4 a b c d e f g h i j k l m n o p
myTree4 _            = error "Something went horribly wrong!"

myTree5 :: [a] -> RTree N5 a
myTree5 [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,
         a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p'] =
            RT.tree5 a b c d e f g h i j k l m n o p a' b' c' d' e' f' g' h' i' j' k' l' m' n' o' p'
myTree5 _            = error "Something went horribly wrong!"

-- myTree6 :: [a] -> RTree N6 a
-- myTree6 [a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1,
--          a2, b2, c2, d2, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2,
--          a3, b3, c3, d3, e3, f3, g3, h3, i3, j3, k3, l3, m3, n3, o3, p3,
--          a4, b4, c4, d4, e4, f4, g4, h4, i4, j4, k4, l4, m4, n4, o4, p4] =
--             RT.tree6 a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1
--                      a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2
--                      a3 b3 c3 d3 e3 f3 g3 h3 i3 j3 k3 l3 m3 n3 o3 p3
--                      a4 b4 c4 d4 e4 f4 g4 h4 i4 j4 k4 l4 m4 n4 o4 p4
-- myTree6 _            = error "Something went horribly wrong!"

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

-- QuickCheck types & propositions
newtype FFTTestVal = FFTTestVal {
    getVal :: [Complex PrettyDouble]
} deriving (Show)
instance Arbitrary FFTTestVal where
    arbitrary = do
        xs <- vectorOf 32 $ choose (-1.0::Double, 1.0)
        let zs = map ((:+ 0) . PrettyDouble) xs
        return $ FFTTestVal zs

prop_fft_test_N2 :: FFTTestVal -> Bool
prop_fft_test_N2 testVal = fft (myTree2 zs) == RT.fromList (dft zs)
    where zs = take 4 $ getVal testVal

prop_fft_test_N3 :: FFTTestVal -> Bool
prop_fft_test_N3 testVal = fft (myTree3 zs) == RT.fromList (dft zs)
    where zs = take 8 $ getVal testVal

prop_fft_test_N4 :: FFTTestVal -> Bool
prop_fft_test_N4 testVal = fft (myTree4 zs) == RT.fromList (dft zs)
    where zs = take 16 $ getVal testVal

prop_fft_test_N5 :: FFTTestVal -> Bool
prop_fft_test_N5 testVal = fft (myTree5 zs) == RT.fromList (dft zs)
    where zs = take 32 $ getVal testVal

-- Test definitions & choice
basicTest :: IO ()
basicTest = forM_ complexData (\x -> do
                putStr "\nTesting input: "
                print x
                putStr "Expected output: "
                print $ dft x
                putStr "Actual output:   "
                print $ fft $ myTree2 x
                )

-- This weirdness is required, as of GHC 7.8.
return []

runTests :: IO Bool
runTests = $quickCheckAll
-- End weirdness.

advancedTest :: IO ()
advancedTest = do
    allPass <- runTests -- Run QuickCheck on all prop_ functions
    unless allPass exitFailure

main :: IO ()
-- main = basicTest
main = advancedTest

