{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, ViewPatterns, ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import LambdaCCC.Misc (xor,(:*)) -- ,dup
import Circat.Shift
import Circat.Mealy (Mealy(..),scanl)
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

#if 0

-- Equivalently,
--
-- crc poly (shiftRF -> (seg',msg')) = foldlQ (crcStep poly) (seg',msg')
--                                   = foldl (curry (crcStep poly)) seg' msg'

crcEncode :: (Traversable poly, Applicative poly, Traversable msg) =>
             poly Bool -> msg Bool -> poly Bool
crcEncode poly msg = crc poly (msg, pure False)

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

-- Consider record update

-- scanl :: C b => (b -> a -> b) -> b -> Mealy a b

-- crcStep :: (Traversable poly, Applicative poly) =>
--            poly Bool -> poly Bool :* Bool -> poly Bool

-- -- Serial with static polynomial
-- crcSK :: forall poly. ( GenBuses (poly Bool), Show (poly Bool)
--                       , Applicative poly, Traversable poly ) =>
--          poly Bool -> Mealy Bool (poly Bool)
-- crcSK poly = Mealy h (pure False,0)
--  where
--    p = sizeA (undefined :: poly Bool)
--    h :: MealyFun (poly Bool, Int) Bool (poly Bool)
--    h (b,(seg,i)) = (seg',(seg',i'))
--     where
--       -- This version doesn't increment i past p, to prevent overflow.
--       (seg',i') | i < p     = (snd (shiftR (seg,b)), i+1)
--                 | otherwise = (crcStep poly (seg,b), i)
-- {-# INLINE crcSK #-}

--       i' = i + 1
--       seg' | i < p     = snd (shiftR (seg,b))
--            | otherwise = crcStep poly (seg,b)

-- Serial with static polynomial
crcSK2 :: forall poly. ( GenBuses (poly Bool), Show (poly Bool)
                       , Applicative poly, Traversable poly ) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSK2 poly = fst <$> scanl h (pure False,0)
 where
   p = sizeA (undefined :: poly Bool)
   -- h :: (poly Bool, Int) -> Bool -> (poly Bool, Int)
   h (seg,i) b | i < p     = (snd (shiftR (seg,b)), i+1)
               | otherwise = (crcStep poly (seg,b), i)
{-# INLINE crcSK2 #-}

-- scanl :: C b => (b -> a -> b) -> b -> Mealy a b

#endif

{--------------------------------------------------------------------
    Sample input
--------------------------------------------------------------------}

-- I'm putting these definitions here to work around a problem with inlining.
-- Fix that problem, and move these definitions back to TreeTest.hs.

polyV1 :: Vec N1 Bool
polyV1 = vec1 True

polyV2 :: Vec N2 Bool
polyV2 = vec2 True False

polyV3 :: Vec N3 Bool
polyV3 = vec3 True False True

polyV4 :: Vec N4 Bool
polyV4 = vec4 True False False True

polyV5 :: Vec N5 Bool
polyV5 = polyV3 <+> polyV2

polyRT0 :: Tree N0 Bool
polyRT0 = tree0 True

polyRT1 :: Tree N1 Bool
polyRT1 = tree1 True False

polyRT2 :: Tree N2 Bool
polyRT2 = tree2 True False False True

polyRT3 :: Tree N3 Bool
polyRT3 = tree3 True False False True True False True False

polyRT4 :: Tree N4 Bool
polyRT4 = tree4 True False False True True False True False
                False True True False True False True False
