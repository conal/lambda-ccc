{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Adder (foo,halfAdd) where

import Prelude hiding (and)

-- import LambdaCCC.CCC
import LambdaCCC.FunCCC

foo :: (Bool,Bool) -> Bool
foo p = xor p

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd p = (xor p, and p)

-- halfAdd (a,b) = (xor (a,b), and (a,b))

xor, and :: (Bool,Bool) :-> Bool

xor (True,False) = True
xor (False,True) = True
xor _            = False

and (True,True) = True
and _           = False
