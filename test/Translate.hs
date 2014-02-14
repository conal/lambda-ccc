{-# LANGUAGE TypeOperators, FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

----------------------------------------------------------------------
-- |
-- Module      :  Simple
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Translate Haskell source code to CCC form:
-- 
--   hermit Translate.hs -v0 -opt=LambdaCCC.ReifyLambda +Main Translate.hss resume && ./Translate
----------------------------------------------------------------------

module Main where

import Prelude

import LambdaCCC.Misc (Unop,Binop)
import LambdaCCC.Lambda (reifyE,xor,ifThenElse)
import LambdaCCC.ToCCC (toCCC)
-- import LambdaCCC.ToCircuit

-- import Circat.Circuit (IsSourceP2,(:>),outGWith)
-- import Circat.Netlist (outV)

-- Needed for resolving names. Bug? Is there an alternative?
import qualified LambdaCCC.Lambda
import qualified LambdaCCC.Ty

import LambdaCCC.Misc ((:*),(:=>))

import LambdaCCC.Ty

swap :: (Bool,Bool) -> (Bool,Bool)
swap (a,b) = (b,a)

swap2 :: (Bool,Bool) -> (Bool,Bool)
swap2 (a,b) = (not b, not a)

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd (a,b) = (a && b, a `xor` b)

-- condInt :: Bool :* (Int :* Int) -> Int

funCond' :: Bool :* ((Int :=> Int) :* (Int :=> Int)) -> (Int :=> Int)
funCond' (p,(f,g)) a = if p then f a else g a

funCond :: (Bool :* ((Int :=> Int) :* (Int :=> Int))) :* Int -> Int
funCond ((p,(f,g)), a) = if p then f a else g a

prodCond :: Bool :* ((Int :* Int) :* (Int :* Int)) -> (Int :* Int)
prodCond (p,((a,b),(a',b'))) = (if p then a else a',if p then b else b')

main :: IO ()
main = do print e
          print c
 where
   e = reifyE funCond "funCond"
   c = toCCC e

