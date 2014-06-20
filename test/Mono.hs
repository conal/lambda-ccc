{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=38 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Mono
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit Mono.hs -v0 -opt=LambdaCCC.Monomorphize DoMono.hss
--   
-- Remove the 'resume' to see intermediate Core.
----------------------------------------------------------------------

module Mono where

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

import Prelude hiding (sum)

import Data.Foldable (Foldable(..),sum)

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)
import TypeUnary.Vec (Vec(..))

import Circat.Pair (Pair(..))
import Circat.RTree (Tree(..))

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

sum4 :: Tree (S (S Z)) Int -> Int
sum4 = sum

