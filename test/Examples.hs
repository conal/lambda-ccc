-- {-# OPTIONS_GHC -fforce-recomp -fplugin=LambdaCCC.Plugin -O -fobject-code -dcore-lint #-}

{-# LANGUAGE CPP, TupleSections, GADTs, TypeOperators, Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

----------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Examples / tinkering.
----------------------------------------------------------------------

-- module Examples where

-- Oddly, this import breaks unfolding needed by monomorphize.
import LambdaCCC.Lambda (EP,reifyEP)

import Data.Monoid (Sum(..))
import Control.Applicative (liftA2)

import TypeUnary.TyNat
import TypeUnary.Vec (Vec)

import Circat.Misc (Unop,Binop,transpose)
import Circat.Rep
import Circat.Pair
import Circat.RTree

import LambdaCCC.Run

-- dotv6 = reifyEP (dotG :: Pair ( Vec N6 Int) -> Int)
-- dott8 = reifyEP (dotG :: Pair (Tree N8 Int) -> Int)

-- main = go "dott2" (dotG :: Pair (Tree N1 Int) -> Int)

-- main = do go "dotv6" (dotG :: Pair ( Vec N6 Int) -> Int)
--           go "dott8" (dotG :: Pair (Tree N8 Int) -> Int)

-- main = go "sumt2" (sum :: Tree N2 Int -> Int)

main = do go "sumt4" (sum :: Tree N4 Int -> Int)
          go "mapt2" (fmap sqr :: Unop (Tree N2 Int))

sqr x = x * x

-- foo = reifyEP (sum :: Tree N2 Int -> Int)

-- foo = reifyEP True

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

#if 0
dotG :: (Traversable g, Foldable g, Applicative f, Foldable f, Num a) => g (f a) -> a
dotG = sum . fmap product . transpose

-- Infix binary dot product
infixl 7 <.>
(<.>) :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u <.> v = dotG (u :# v)
#endif
