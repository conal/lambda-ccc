{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=34 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  TreeTest
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit TreeTest.hs -v0 -opt=LambdaCCC.Reify DoTree.hss resume && ./TreeTest
--   
-- Remove the 'resume' to see intermediate Core.
----------------------------------------------------------------------

-- module TreeTest where

-- TODO: explicit exports

import Prelude hiding (foldr,sum)

import Control.Applicative (Applicative(..),liftA2)

import Data.Foldable (Foldable(..),sum)

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)

import Circat.RTree
-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import LambdaCCC.Lambda (EP,reifyEP)

-- import LambdaCCC.Prim (Prim(TreeSP))
import LambdaCCC.Misc (Unop,Binop)

import Circat.Pair (Pair(..))
import Circat.RTree (TreeCat(..))
import Circat.Circuit (IsSourceP2)

import LambdaCCC.Run (run)

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

t0 :: Tree N0 Bool
t0 = pure True

t1 :: Tree N1 Bool
t1 = B (pure t0)

p1 :: Unop (Pair Bool)
p1 (a :# b) = b :# a

psum :: Pair Int -> Int
psum (a :# b) = a + b

tsum :: Num a => Tree n a -> a
tsum = foldT id (+)

-- prod :: (IsNat n, Num a) => (Tree n a, Tree n a) -> Tree n a
-- prod (as,bs) = liftA2 (*) as bs

-- prod :: (IsNat n, Num a) => Tree n a -> Tree n a -> Tree n a
-- prod = liftA2 (*)

-- dot :: (IsNat n, Num a) => Tree n a -> Tree n a -> a
-- dot as bs = tsum (prod as bs)

prod :: (Functor f, Num a) => f (a,a) -> f a
prod = fmap (uncurry (*))

prodA :: (Applicative f, Num a) => Binop (f a)
prodA = liftA2 (*)

dot :: Num a => Tree n (a,a) -> a
dot = tsum . prod

square :: (Functor f, Num a) => f a -> f a
square = fmap (\ x -> x * x)

square' :: (Functor f, Num a) => f a -> f a
square' = fmap (^ (2 :: Int))

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

go :: IsSourceP2 a b => String -> (a -> b) -> IO ()
go name f = run name (reifyEP f)

-- Only works when compiled with HERMIT
main :: IO ()

-- main = go "tsum4" (tsum :: Tree N4 Int -> Int)

-- main = do go "square3" (square :: Tree N3 Int -> Tree N3 Int)
--           go "sum4"    (tsum   :: Tree N4 Int -> Int)
--           go "dot4"    (dot    :: Tree N4 (Int,Int) -> Int)

main = go "dot1" (dot :: Tree N1 (Int,Int) -> Int)

-- main = go "square2" (square :: Unop (Tree N2 Int))

-- main = go "square2" (square' :: Unop (Tree N0 Int))

-- main = go "sum1f" (sum :: Tree N1 Int -> Int)

-- main = go "prodA1" (uncurry prodA :: (Tree N1 Int,Tree N1 Int) -> Tree N1 Int)
