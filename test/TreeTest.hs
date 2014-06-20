{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=38 #-}
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

-- transformers
import Data.Functor.Identity

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

import LambdaCCC.Encode (Encodable(..))
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

psum :: Num a => Pair a -> a
psum (a :# b) = a + b

-- tsum :: Num a => Tree n a -> a
-- tsum = foldT id (+)

-- dot :: (IsNat n, Num a) => Tree n a -> Tree n a -> a
-- dot as bs = tsum (prod as bs)

prod :: (Functor f, Num a) => f (a,a) -> f a
prod = fmap (uncurry (*))

prodA :: (Applicative f, Num a) => Binop (f a)
prodA = liftA2 (*)

-- dot :: Num a => Tree n (a,a) -> a
-- dot = tsum . prod

dot :: (Functor f, Foldable f, Num a) => f (a,a) -> a
dot = sum . prod

squares :: (Functor f, Num a) => f a -> f a
squares = fmap (\ x -> x * x)

squares' :: (Functor f, Num a) => f a -> f a
squares' = fmap (^ (2 :: Int))

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

go' :: IsSourceP2 a b => String -> (a -> b) -> IO ()
go' name f = run name (reifyEP f)

go :: (Encodable a, Encodable b, IsSourceP2 (Encode a) (Encode b)) =>
      String -> (a -> b) -> IO ()
go name f = go' name (encode f)

-- With an outer encode

-- Only works when compiled with HERMIT
main :: IO ()

-- main = go "tsum4" (tsum :: Tree N4 Int -> Int)

-- main = do go "squares3" (squares :: Tree N3 Int -> Tree N3 Int)
--           go "sum4"     (tsum   :: Tree N4 Int -> Int)
--           go "dot4"     (dot    :: Tree N4 (Int,Int) -> Int)

-- Problematic examples:

-- -- This one leads to non-terminating CCC construction when the composeApply
-- -- optimization is in place.
-- main = go "dot1" (dot :: Tree N1 (Int,Int) -> Int)

-- main = go "dot0" (dot :: Tree N0 (Int,Int) -> Int)

main = go "dot2" (dot :: Tree N2 (Int,Int) -> Int)

-- -- Doesn't wedge.
-- main = go "dotp" ((psum . prod) :: Pair (Int,Int) -> Int)

-- main = go "prod1" (prod :: Tree N1 (Int,Int) -> Tree N1 Int)

-- main = go "dot5" (dot :: Tree N5 (Int,Int) -> Int)

-- main = go "squares1" (squares :: Unop (Tree N1 Int))

-- main = go "squares2" (squares :: Unop (Tree N2 Int))

-- main = go "squares0" (squares :: Unop (Tree N0 Int))

-- main = go "psum" (psum :: Pair Int -> Int)

-- main = go "tsum1" (tsum :: Tree N1 Int -> Int)

-- -- Not working yet: the (^) is problematic.
-- main = go "squares2" (squares' :: Unop (Tree N0 Int))

-- -- Working out a reify issue.
-- main = go "sum2f" (sum :: Tree N2 Int -> Int)

-- -- Causes a GHC RTS crash ("internal error: stg_ap_pp_ret") with Reify.
-- -- Seemingly infinite rewrite loop with Standard.
-- main = go "prodA1" (uncurry prodA :: (Tree N1 Int,Tree N1 Int) -> Tree N1 Int)

-- main = go "prodA0" (uncurry prodA :: (Tree N0 Int,Tree N0 Int) -> Tree N0 Int)

-- main = go "idA" (uncurry f)
--  where
--    f :: Identity Bool -> Identity Bool -> Identity (Bool,Bool)
--    f = liftA2 (,)
