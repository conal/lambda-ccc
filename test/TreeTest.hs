{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=34 #-}

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

import Circat.RTree
-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import LambdaCCC.Lambda (EP,reifyEP)

-- import LambdaCCC.Prim (Prim(TreeSP))
import LambdaCCC.Misc (Unop)

import Circat.Pair (Pair(..))
import Circat.RTree (TreeCat(..))
import Circat.Circuit (IsSourceP2)

import LambdaCCC.Run

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

tsum :: Tree n Int -> Int
tsum = foldT id (+)

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

-- Only works when compiled with HERMIT
main :: IO ()
-- main = run (reifyEP p1)
-- main = run (reifyEP (fmap not :: Unop (Tree N3 Int)))
-- main = run (reifyEP psum)
main = run (reifyEP (tsum :: Tree N3 Int -> Int))
