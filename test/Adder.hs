{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MagicHash #-} -- for unpackCString# import

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Adder where

import Prelude hiding (and)

-- Needed for resolving names.
-- TODO: Bug? Is there an alternative?
import LambdaCCC.LambdaPh (E(..),var,lamv,reifyE,evalE)

constPair :: (Bool,Bool)
constPair = (True,False)

idBool :: Bool -> Bool
idBool a = a

bar :: (Bool,Bool) -> Bool
bar = xor

foo :: (Bool,Bool) -> Bool
foo p = xor p

baz :: (Bool,Bool) -> (Bool,Bool) -> Bool
baz p q = xor (xor p, xor q)

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd p = (xor p, and p)

quux :: Bool -> (Bool,Bool)
quux p = (p,True)

p1 :: Bool -> (Bool,Bool)
p1 a = (a,not a)

-- Polymorphic example

swap :: (a,b) -> (b,a)
swap p = (snd p, fst p)

-- The rest don't yet transform successfully. They become 'case' expressions,
-- which we're not yet handling.

halfAdd' :: (Bool,Bool) -> (Bool,Bool)
halfAdd' (a,b) = (xor (a,b), and (a,b))

xor, and :: (Bool,Bool) -> Bool

xor (True,False) = True
xor (False,True) = True
xor _            = False

and (True,True) = True
and _           = False

fiddle :: Int
fiddle = length "Fiddle"

{-# RULES
-- "fiddle" length "Fiddle" = length "Faddle"
  #-}
