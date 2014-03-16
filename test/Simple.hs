{-# LANGUAGE TypeOperators, FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax, CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- For qualified LambdaCCC.Lambda import :(
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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
--   hermit Simple.hs -v0 -opt=LambdaCCC.Reify +Simple Auto.hss resume && ghc -O2 --make SimpleMain.hs && ./SimpleMain
--   
----------------------------------------------------------------------

module Simple  where

import Prelude

import LambdaCCC.Lambda (EP,reifyEP,xor)

-- Needed for resolving names. Is there an alternative?
import qualified LambdaCCC.Lambda

ident :: a -> a
ident x = x

voodle :: a -> a
voodle = ident

viddle :: Bool -> Bool
viddle b = ident b

notNot :: Bool -> Bool
notNot a = not (not a)

notNot' :: Bool -> Bool
notNot' a = not (ident (not a))

bar :: Bool -> (Bool,Bool)
bar x = (y, not y)
 where
   y = not x

bar' :: Bool -> (Bool,Bool)
bar' x = (y, not y)
 where
   y = notNot x

baz :: (Bool,Bool)
baz = (x,x) where x = True

-- Polymorphic
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

-- Monomorphic
swap1 :: (Bool,()) -> ((),Bool)
swap1 = swap

-- Alias for swap
swapZ :: (a,b) -> (b,a)
swapZ = swap

-- Compute and swap
swap2 :: (Bool,Bool) -> (Bool,Bool)
swap2 (a,b) = swap (not b, not a)

-- Alias with local definition
-- (Binding gets simplified away.)
swap3 :: (Bool,Bool) -> (Bool,Bool)
swap3 = swap'
 where
   swap' (x,y) = (y,x)

swap6 :: (Bool,()) -> (Bool,())
swap6 = \ p -> swap' (swap' p)
        -- swap' . swap'
 where
   swap' :: (a,b) -> (b,a)
   swap' (x,y) = (y,x)

-- Twice swapped
swap7 :: (Bool,Bool) -> (Bool,Bool)
swap7 p = swap (swap p)

-- Eta-expanded alias
swap8 :: (Bool,Bool) -> (Bool,Bool)
swap8 p = swap p

id' :: a -> a
id' x = x

foo :: Bool -> Bool
foo = id'

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd (a,b) = (a && b, a `xor` b)

zoot :: Bool -> Bool
zoot a = a `xor` a

-- Version with HOFs
halfAddH :: (Bool,Bool) -> (Bool,Bool)
halfAddH (a,b) = (h (&&), h xor)
 where
   h :: (Bool -> Bool -> Bool) -> Bool
   h f = f a b

--------

-- Reification example for exporting

-- reified :: EP ((Bool, Bool) -> (Bool, Bool))
-- reified = reifyEP halfAdd

-- reified :: EP (Bool -> (Bool,Bool))
-- reified = reifyEP bar'

reified :: EP ((Bool,()) -> (Bool,()))
reified = reifyEP swap6
