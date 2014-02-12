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
-- Test conversion of Haskell source code into circuits. To run:
-- 
--   hermit Simple.hs -v0 -opt=LambdaCCC.ReifyLambda +Main Simple.hss resume && ./Simple
----------------------------------------------------------------------

module Main where

import Prelude

import LambdaCCC.Misc (Unop,Binop)
import LambdaCCC.Lambda (reifyE,xor,ifThenElse)
import LambdaCCC.ToCCC (toCCC)
import LambdaCCC.ToCircuit

import Circat.Circuit (IsSourceP2,(:>),outGWith)
import Circat.Netlist (outV)

-- Needed for resolving names. Bug? Is there an alternative?
import qualified LambdaCCC.Lambda
import qualified LambdaCCC.Ty

import LambdaCCC.Ty

swap :: (Bool,Bool) -> (Bool,Bool)
swap (a,b) = (b,a)

swap2 :: (Bool,Bool) -> (Bool,Bool)
swap2 (a,b) = (not b, not a)

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd (a,b) = (a && b, a `xor` b)

-- Version with HOFs
halfAddH :: (Bool,Bool) -> (Bool,Bool)
halfAddH (a,b) = (foo (&&), foo xor)
 where
   foo :: (Bool -> Bool -> Bool) -> Bool
   foo f = f a b

-- Without the type signature on foo, I get an unhandled polymorphic type.

main :: IO ()
main = do print e
          print c
          outGV "halfAddH" (cccToCircuit c)
 where
   e = reifyE halfAddH "halfAddH"
   c = toCCC e

-- Diagram and Verilog
outGV :: IsSourceP2 a b => String -> (a :> b) -> IO ()
outGV s c = do outGWith ("pdf","") s c
               outV                s c
