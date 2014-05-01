{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=34 #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  VecTest
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed vectors. To run:
-- 
--   hermit VecTest.hs -v0 -opt=LambdaCCC.Reify DoVec.hss resume && ./VecTest
--   
-- Remove the 'resume' to see intermediate Core.
----------------------------------------------------------------------

-- module VecTest where

-- TODO: explicit exports

import Prelude hiding (foldr,sum)

import Control.Applicative (Applicative,liftA2)

import Data.Foldable (Foldable(..),sum)

import TypeUnary.Vec
-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import LambdaCCC.Lambda (EP,reifyEP)

import LambdaCCC.Prim (Prim(VecSP))
import LambdaCCC.Misc (Unop)

import Circat.Classes (VecCat(..))
import Circat.Circuit (IsSourceP2)

import LambdaCCC.Run

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- z :: EP (Vec Z Bool)
-- z = reifyEP ZVec

v3 :: Vec N3 Bool
v3 = True :< False :< True :< ZVec

v3' :: Vec N3 Bool
v3' = ZVec <+> v3

v6 :: Vec N6 Bool
v6 = v3 <+> v3

m3 :: Unop (Vec N3 Bool)
m3 = fmap not

f3 :: Vec N5 Bool -> Bool
f3 = foldr (||) True

-- Dot product

square :: (Functor f, Num a) => f a -> f a
square = fmap (\ x -> x * x)

prod :: (Applicative f, Foldable f, Num a) => (f a, f a) -> f a
prod (as,bs) = liftA2 (*) as bs

dot :: (Applicative f, Foldable f, Num a) => (f a, f a) -> a
dot (as,bs) = sum (liftA2 (*) as bs)

sum1 :: Vec N8 Int -> Int
sum1 = foldr (+) 0

sq1 :: Unop (Vec N4 Int)
-- sq1 x = x * x
sq1 = square

d1 :: (Vec N1 Int, Vec N1 Int) -> Int
d1 = dot

p0 :: (Vec N0 Int, Vec N0 Int) -> Vec N0 Int
p0 = prod

p1 :: (Vec N1 Int, Vec N1 Int) -> Vec N1 Int
p1 = prod


-- TODO: Use the `Num` interface for even simpler formulations, including `dot
-- as bs = sum (as * bs)` and `square a = a * a`. Would be less polymorphic.

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

-- Only works when compiled with HERMIT
main :: IO ()
-- main = run (reifyEP f3)

main = run (reifyEP sum1)

-- main = run (reifyEP d1)

-- main = run (reifyEP sq1)

-- main = run (reifyEP p1)
