{-# LANGUAGE TypeOperators, TypeFamilies, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Adder
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Scan-based adder
----------------------------------------------------------------------

module LambdaCCC.Adder where

-- TODO: explicit exports

import Data.Monoid (Monoid(..))
import Control.Applicative (Applicative,liftA2,(<$>))

import Circat.Misc ((:*))
import Circat.Rep
import Circat.Scan
import Circat.Pair
import Circat.Circuit (GenBuses(..),genBusesRep')

import LambdaCCC.Prim (xor)

-- | Generate and propagate carries
data GenProp = GenProp Bool Bool 

type instance Rep GenProp = Bool :* Bool
instance HasRep GenProp where
  repr (GenProp g p) = (g,p)
  abst (g,p) = GenProp g p

-- MSB on left
instance Monoid GenProp where
  mempty = GenProp False True
  GenProp gy py `mappend` GenProp gx px =
    GenProp (gx || gy && px) (px && py)
  {-# INLINE mempty #-}
  {-# INLINE mappend #-}

genProp :: Pair Bool -> GenProp
genProp (a :# b) = GenProp (a && b) (a `xor` b)
{-# INLINE genProp #-}

type Adder t = t (Pair Bool) -> t Bool :* Bool

scanAdd :: (Applicative t, LScan t) => Adder t
scanAdd ps = (liftA2 h ps cs, co)
 where
   gprs = genProp <$> ps
   (fmap gpGen -> cs, gpGen -> co) = lscan gprs
   h (a :# b) ci = (a `xor` b) `xor` ci

gpGen :: GenProp -> Bool
gpGen (GenProp _ g) = g

gpProp :: GenProp -> Bool
gpProp (GenProp p _) = p

instance GenBuses GenProp where genBuses' = genBusesRep'
