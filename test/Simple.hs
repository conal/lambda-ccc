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
--   hermit Simple.hs -v0 -opt=LambdaCCC.ReifyLambda +Main Simple.hss resume && ./Simple
--
-- I'm working toward splitting off main to SimpleMain. When it works:
--
--   hermit Simple.hs -v0 -opt=LambdaCCC.ReifyLambda +Simple Simple.hss resume
--   
----------------------------------------------------------------------

#define WithMain

module
#ifdef WithMain
       Main
#else
       Simple
#endif
              where

import Prelude

import LambdaCCC.Misc (Unop,Binop)
import LambdaCCC.Lambda (EP,reifyEP,xor,ifThenElse)
import LambdaCCC.ToCCC (toCCC')
import LambdaCCC.CCC ((:->),convertC)
-- import LambdaCCC.ToCircuit

import Circat.Category (unUnitFun)
import Circat.Circuit (IsSourceP2,(:>),outGWith)
import Circat.Netlist (outV)

-- Needed for resolving names. Bug? Is there an alternative?
import qualified LambdaCCC.Lambda
-- import qualified LambdaCCC.Prim
-- import qualified LambdaCCC.Ty

-- import LambdaCCC.Ty

ident :: Bool -> Bool
ident a = a

notNot :: Bool -> Bool
notNot a = not (not a)

-- swap :: (Bool,Bool) -> (Bool,Bool)
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

swap2 :: (Bool,Bool) -> (Bool,Bool)
swap2 (a,b) = (not b, not a)

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

-- Version with HOFs
halfAddH :: (Bool,Bool) -> (Bool,Bool)
halfAddH (a,b) = (h (&&), h xor)
 where
   h :: (Bool -> Bool -> Bool) -> Bool
   h f = f a b

-- Without the type signature on foo, I get into trouble with polymorphism.
-- Still working.

#ifdef WithMain

main :: IO ()
main = do print e
          print ccc
          outGV "swap6" circuit
 where
   e       = reifyEP swap6 "swap6"
   -- Both of the following definitions work:
   ccc     = toCCCTerm' e
   circuit = toCCC'     e
--    ccc     = toCCC' e
--    circuit = convertC ccc

-- Type-specialized toCCC
toCCCTerm' :: EP (a -> b) -> (a :-> b)
toCCCTerm' = toCCC'

-- Diagram and Verilog
outGV :: IsSourceP2 a b => String -> (a :> b) -> IO ()
outGV s c = do outGWith ("pdf","") s c
               outV                s c

#else

fiddle :: Int
fiddle = length "Fiddle"

-- WEIRD: sometimes when I comment out this fiddle definition, I get the dread
-- "expectJust initTcInteractive" GHC panic.

#endif
