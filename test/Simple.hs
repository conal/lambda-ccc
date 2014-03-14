{-# LANGUAGE TypeOperators, FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

module Simple where

import Prelude

import LambdaCCC.Misc (Unop,Binop)
import LambdaCCC.Lambda (EP,reifyEP,reifyEP,xor,ifThenElse)
import LambdaCCC.ToCCC (toCCC')
import LambdaCCC.CCC ((:->),convertC)

import Circat.Category (unUnitFun)
import Circat.Circuit (IsSourceP2,(:>),outGWith)
import Circat.Netlist (outV)

-- Needed for resolving names. Bug? Is there an alternative?
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

swap1 :: (Bool,Bool) -> (Bool,Bool)
swap1 (x,y) = (y,x)

swap2 :: (Bool,Bool) -> (Bool,Bool)
swap2 (a,b) = (not b, not a)

swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

swapZ :: (a,b) -> (b,a)
swapZ = swap

swap3 :: (Bool,Bool) -> (Bool,Bool)
swap3 = swap'
 where
   swap' (x,y) = (y,x)

swap4 :: (Bool,Bool) -> (Bool,Bool)
swap4 = swap'
 where
   swap' :: (a,b) -> (b,a)
   swap' (x,y) = (y,x)

swap5 :: (Bool,Int) -> (Int,Bool)
swap5 = swap

swap6 :: (Bool,Bool) -> (Bool,Bool)
swap6 = \ p -> swap' (swap' p)
        -- swap' . swap'
 where
   swap' :: (a,b) -> (b,a)
   swap' (x,y) = (y,x)

swap7 :: (Bool,Bool) -> (Bool,Bool)
swap7 p = swap (swap p)

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

reified :: EP (Bool -> (Bool,Bool))
reified = reifyEP bar'
