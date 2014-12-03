{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, ViewPatterns, ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.CRC
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- CRC computations
----------------------------------------------------------------------

module LambdaCCC.CRC where

-- TODO: explicit exports

import Prelude hiding (foldl,scanl,sum)

import Control.Applicative -- (Applicative(..),liftA2,liftA3)
import Data.Foldable (Foldable(..),sum)
import Data.Traversable (Traversable(..))
-- import Control.Category (id,(.))
-- import Control.Arrow ((&&&))

import LambdaCCC.Misc (Unop,xor,(:*)) -- ,dup
import Circat.Pair (Pair(..))
import Circat.Shift
import Circat.Mealy (Mealy(..)) -- scanl
import Circat.Circuit (GenBuses)

-- TEMP
import TypeUnary.Vec hiding (transpose)
import Circat.RTree

crcStep :: (Traversable poly, Applicative poly) =>
           poly Bool -> poly Bool :* Bool -> poly Bool
crcStep poly (shiftR -> (b0,seg')) = (if b0 then liftA2 xor poly else id) seg'

-- crcStep poly (shiftR -> (b0,seg')) = liftA2 tweak poly seg'
--  where
--    tweak c a = (b0 && c) `xor` a

#if 0
   tweak c a
== if b then (c `xor` a) else a
== if b then (c `xor` a) else (False `xor` a)
== (if b then c else False) `xor` a
== (b && c) `xor` a
#endif

-- crcStep poly (shiftR -> (b0,seg')) =
--   liftA2 (\ c a -> (b0 && c) `xor` a) poly seg'

-- crcStep poly (shiftR -> (b0,seg')) = liftA2 tweak poly seg'
--  where
--    tweak c a = (b0 && c) `xor` a

crc :: (Traversable poly, Applicative poly, Traversable msg) =>
       poly Bool -> msg Bool :* poly Bool -> poly Bool
crc poly = foldlQ (crcStep poly) . shiftRF

-- | Uncurried variant of 'foldl'
foldlQ :: Foldable f => (b :* a -> b) -> (b :* f a -> b)
foldlQ = uncurry . foldl . curry

-- Equivalently,
--
-- crc poly (shiftRF -> (seg',msg')) = foldlQ (crcStep poly) (seg',msg')
--                                   = foldl (curry (crcStep poly)) seg' msg'

crcEncode :: (Traversable poly, Applicative poly, Traversable msg) =>
             poly Bool -> msg Bool -> poly Bool
crcEncode poly msg = crc poly (msg, pure False)

#if 0

-- Curried versions (for consideration):

crcStep' :: (Traversable poly, Applicative poly) =>
            poly Bool -> poly Bool -> Bool -> poly Bool
crcStep' poly seg b = (if b0 then liftA2 xor poly else id) seg'
 where
   (b0,seg') = shiftR (seg,b)

crc' :: (Traversable poly, Applicative poly, Traversable msg) =>
        poly Bool -> msg Bool -> poly Bool -> poly Bool
crc' poly msg pad = foldl (crcStep' poly) seg0 msg0
 where
   (seg0,msg0) = shiftRF (msg,pad)

#endif

type MealyFun s a b = (a,s) -> (b,s)

-- Given an input bit,

-- *   If $i < p$, shift the input bit into the polynomial.
-- *   If $p \le i < 2 p$, shift into the remainder.
-- *   If $2 p \le i$, do a CRC step, updating the remainder.

#if 1

-- Serial
crcS :: forall poly. (GenBuses (poly Bool), Show (poly Bool), Applicative poly, Traversable poly) =>
        Mealy Bool (poly Bool)
crcS = Mealy h (pure False, pure False,0)
 where
   p = sizeA (undefined :: poly Bool)
   h :: MealyFun (poly Bool, poly Bool, Int) Bool (poly Bool)
   h (b,(poly,seg,i)) = (seg',(poly',seg',i'))
    where
      i' = i + 1
      stash q = snd (shiftR (q,b))
      (poly',seg')
        | i < p     = (stash poly,seg)
        | i < 2*p   = (poly,stash seg)
        | otherwise = (poly,crcStep poly (seg,b))
{-# INLINE crcS #-}

-- TODO: rewrite via scanl

-- Size of a structure without looking at the structure
sizeA :: forall f a. (Applicative f, Foldable f) => f a -> Int
sizeA _ = sum (pure 1 :: f Int)

type GS a = (GenBuses a, Show a)

#if 0

-- Strangely, the (<) in these definitions gets inlined before I can intercept it.
-- For now, repeat the definitions in TreeTest.

-- Serial with static polynomial
crcSKa :: forall poly. ( GS (poly Bool)
                       , Applicative poly, Traversable poly ) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKa poly = Mealy h (pure False,0)
 where
   p = sizeA (undefined :: poly Bool)
   h :: MealyFun (poly Bool, Int) Bool (poly Bool)
   h (b,(seg,i)) = (seg',(seg',i'))
    where
      -- This version doesn't increment i past p, to prevent overflow.
      (seg',i') | i < p     = (snd (shiftR (seg,b)), i+1)
                | otherwise = (crcStep poly (seg,b), i)
{-# INLINE crcSKa #-}

-- To simplify the circuit, output stepped even when i<p.
-- We expect the user to ignore this initial output either way.
crcSKb :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
           poly Bool -> Mealy Bool (poly Bool)
crcSKb poly = Mealy h (pure False,0)
 where
   p = sizeA (undefined :: poly ())
   h (b,(seg,i)) = (stepped,next)
    where
      stepped = crcStep poly (seg,b)
      next | i < p     = (snd (shiftR (seg,b)), i+1)
           | otherwise = (stepped, i)
{-# INLINE crcSKb #-}

crcSKc :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKc poly = Mealy h (pure False,0)
 where
   p = sizeA (undefined :: poly ())
   h (b,(seg,i)) = (stepped,(seg',i+1))
    where
      stepped = crcStep poly (seg,b)
      seg' | i < p     = snd (shiftR (seg,b))
           | otherwise = stepped
{-# INLINE crcSKc #-}
#endif

#endif

{--------------------------------------------------------------------
    Sample input
--------------------------------------------------------------------}

#if 0

numBits :: Integral a => a -> [Bool]
numBits ((`div` 2) &&& odd -> (m,b)) = b : numBits m

numBitsR :: forall n. IsNat n => Int -> RTree n Bool
numBitsR = fromList . take (2^d) . numBits
  where
    d = natToZ (nat :: Nat n) :: Int

numBitsV :: forall n. IsNat n => Int -> Vec n Bool
numBitsV = elemsV . take n . numBits
  where
    n = natToZ (nat :: Nat n) :: Int

-- See "Best CRC Polynomials" by Philip Koopman.
-- <http://users.ece.cmu.edu/~koopman/crc/>.

#endif

-- I'm putting these definitions here to work around a problem with inlining.
-- Fix that problem, and move these definitions back to TreeTest.hs.

class PolyD f where
  polyD :: f Bool
  -- My standard regrettable hack to help reify otherwise-single-method
  -- dictionaries.
  regrettable_hack_PolyD :: f () -> ()
  regrettable_hack_PolyD = const ()

instance PolyD (Vec N1) where polyD = vec1 True
instance PolyD (Vec N2) where polyD = vec2 True False
instance PolyD (Vec N3) where polyD = vec3 True False True
instance PolyD (Vec N4) where
  polyD = vec4 True False False True
  {-# INLINE polyD #-}
instance PolyD (Vec N5) where
  polyD = ((polyD :: Vec N3 Bool) <+> (polyD :: Vec N2 Bool))
  {-# INLINE polyD #-}

instance PolyD (Tree N0) where polyD = tree0 True
instance PolyD (Tree N1) where polyD = tree1 True False
instance PolyD (Tree N2) where polyD = tree2 True False False True
instance PolyD (Tree N3) where
  polyD = tree3 True False False True True False True False
  {-# INLINE polyD #-}
instance PolyD (Tree N4) where
  polyD = tree4 True False False True True False True False
                False True True False True False True False
  {-# INLINE polyD #-}
instance PolyD (Tree N5) where
  polyD = tree5 True False False True True False True False
                False True True False True False True False
                False False True True False True False False
                True True False True False True False True
  {-# INLINE polyD #-}
instance PolyD (Tree N6) where
  polyD = B (polyD :# bumpR True polyD)
  {-# INLINE polyD #-}
instance PolyD (Tree N7) where
  polyD = B (polyD :# bumpR True polyD)
  {-# INLINE polyD #-}

bumpR :: Traversable f => a -> Unop (f a)
bumpR a as = snd (shiftR (as,a))
