{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Adder where

import Prelude hiding (and)

import Data.Tuple (fst,snd)

-- import LambdaCCC.CCC
import LambdaCCC.FunCCC

constPair :: (Bool,Bool)
constPair = (True,False)

idBool :: Bool -> Bool
idBool p = p

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
