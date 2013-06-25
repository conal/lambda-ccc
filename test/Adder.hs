{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MagicHash #-} -- for unpackCString# import

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Main where

import Prelude

-- Needed for resolving names.
-- TODO: Bug? Is there an alternative?
import LambdaCCC.Lambda (E(..),var,lamv,reifyE,evalE)
import LambdaCCC.Ty (Ty(..))

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

quux :: Bool -> (Bool,Bool)
quux p = (p,True)

p1 :: Bool -> (Bool,Bool)
p1 a = (a,not a)

-- Polymorphic
swap :: (s,t) -> (t,s)
swap p = (snd p, fst p)

swapBS :: (Bool,String) -> (String,Bool)
swapBS p = (snd p, fst p)

-- The rest don't yet transform successfully. They become 'case' expressions,
-- which we're not yet handling.

halfAdd' :: (Bool,Bool) -> (Bool,Bool)
halfAdd' (a,b) = (a `xor` b, a && b)

fiddle :: Int
fiddle = length "Fiddle"

-- WEIRD: sometimes when I comment out this fiddle definition, I get the dread
-- "expectJust initTcInteractive" GHC panic.

------

main :: IO ()
main = print t
 where
   t = swapBS (False,"Hello")
   -- t = halfAdd (True,False)
