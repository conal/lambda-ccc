{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, ViewPatterns #-}
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

import Prelude hiding (foldl)

import Control.Applicative -- (Applicative(..),liftA2,liftA3)
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
-- import Control.Category (id,(.))

import LambdaCCC.Misc (xor,(:*))

import Circat.Shift
-- import Circat.Mealy hiding (sumS)
-- import qualified Circat.Mealy as Mealy

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
