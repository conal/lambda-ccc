{-# LANGUAGE CPP, TypeOperators #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=34 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ETest
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit ETest.hs -v0 -opt=LambdaCCC.Reify DoE.hss
--   
----------------------------------------------------------------------

module ETest where

import Prelude hiding (sum)

import Data.Foldable (sum)

import Circat.Pair (Pair(..))

import Circat.Misc ((:*))

import LambdaCCC.Encode (Encodable(..))

e1 :: (Pair Int -> Int) -> Encode (Pair Int -> Int)
e1 = encode

e2 :: (Pair Int -> Int) -> (Int :* Int -> Int)
e2 = encode

e3 :: Pair Int -> Int
e3 = sum

e4 :: Int :* Int -> Int
e4 = encode e3
