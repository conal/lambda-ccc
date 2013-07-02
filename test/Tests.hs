{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

----------------------------------------------------------------------
-- |
-- Module      :  Tests
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Test conversion of Haskell source code into circuits. To run:
-- 
--   hermit Tests.hs -opt=LambdaCCC.ReifyLambda +Main Tests.hss -- -v0 && ./Tests
----------------------------------------------------------------------

module Main where

import Prelude

import LambdaCCC.Lambda (reifyE)
import LambdaCCC.ToCCC (toCCC)

-- Needed for resolving names. Bug? Is there an alternative?
import qualified LambdaCCC.Lambda
import qualified LambdaCCC.Ty

import LambdaCCC.Prim (xor)

constPair :: (Bool,Bool)
constPair = (True,False)

idBool :: Bool -> Bool
idBool a = a

fst1 :: (s,t) -> s
fst1 = fst

fst2 :: (Bool,Int) -> Bool
fst2 = fst

fst3 :: (Bool,Int) -> Bool
fst3 p = fst p

bar :: Bool -> Bool -> Bool
bar = xor

foo :: (Bool,Bool) -> Bool
foo p = fst p `xor` snd p

baz :: (Bool,Bool) -> (Bool,Bool) -> Bool
baz p q = (fst p `xor` snd p) `xor` (fst q `xor` snd q) 

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd p = (fst p && snd p, fst p `xor` snd p)

halfAdd' :: (Bool,Bool) -> (Bool,Bool)
halfAdd' (a,b) = (a `xor` b, a && b)

quux :: Bool -> (Bool,Bool)
quux p = (p,True)

p1 :: Bool -> (Bool,Bool)
p1 a = (a,not a)

-- Polymorphic
swap :: (s,t) -> (t,s)
swap p = (snd p, fst p)

swapBI :: (Bool,Int) -> (Int,Bool)
swapBI p = (snd p, fst p)

swapBI' :: (Bool,Int) -> (Int,Bool)
swapBI' (a,b) = (b,a)

f3 :: ((Bool,Bool),(Bool,Bool)) -> (Bool,Bool)
f3 ((a,b),(c,d)) = (a && c, b || d)

g :: ((Bool,Bool),Bool) -> Bool
g ((_,b),_) = b

f4 :: Bool -> (Bool,Bool)
f4 x = (y,y)
 where
   y = not x

fiddle :: Int
fiddle = length "Fiddle"

-- WEIRD: sometimes when I comment out this fiddle definition, I get the dread
-- "expectJust initTcInteractive" GHC panic.

main :: IO ()
main = do print e
          print (toCCC e)
 where
   e = reifyE "swapBI'" swapBI'

-- TODO: maybe a TH macro for reifyE "foo" foo, "[r|foo]".
-- Maybe additional macros for specialized contexts like toCCC [r|foo].
