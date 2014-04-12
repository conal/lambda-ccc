{-# LANGUAGE TypeOperators, FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}

{-# OPTIONS_GHC -Wall #-}

-- For qualified LambdaCCC.Lambda import :(
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

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

module Simple (reified) where

import Prelude

import LambdaCCC.Lambda (EP,reifyEP,xor,condBool)
import LambdaCCC.Lambda (condBool)  -- TEMP

-- Needed for resolving names. Is there an alternative?
import qualified LambdaCCC.Lambda
import GHC.Tuple ()
import Data.Either ()
import qualified TypeEncode.Encode

{--------------------------------------------------------------------
    Utilities to be moved elsewhere
--------------------------------------------------------------------}

class HasIf a where
  ifThenElse :: Bool -> a -> a -> a

instance HasIf Bool where
  ifThenElse i t e = condBool (i,(e,t))  -- note swap

instance (HasIf a, HasIf b) => HasIf (a,b) where
  ifThenElse i (t,t') (e,e') = (ifThenElse i t e,ifThenElse i t' e')

-- instance (HasIf a, HasIf b) => HasIf (a,b) where
--   if i then (t,t') else (e,e') = (if i then t else e, if i then t' else e')


{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

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

-- idOrNot :: Either Bool Bool -> Bool
-- idOrNot (Left  a) = a
-- idOrNot (Right a) = not a

if1 :: Bool -> Bool
if1 x = condBool (x,(False,True))

if2 :: Bool -> Bool
if2 x = if x then False else True

#if 1

-- Constructor applications and case expressions

case0 :: () -> Bool
case0 () = False

data G a = G a

con1 :: G Bool
con1 = G True

case1 :: G Bool -> Bool
case1 (G x) = not x

data E a = E a a

con2 :: E Bool
con2 = E False True

case2 :: E Bool -> Bool
case2 (E q r) = q || r

data Boo = F | T

caseQ :: Boo -> Bool
caseQ F = False
caseQ T = True

data A = B Integer | C () Bool () Integer | Y Integer | Z

con4 :: Integer -> A
con4 n = C () True () n

case4 :: A -> Bool
case4 (B _)        = True
case4 (C () b _ _) = not b
case4 (Y _)        = False
case4 Z            = True

-- newtype

newtype NT = NT Bool

con5 :: NT
con5 = NT True

-- GADT

data Nat = Zero | Succ Nat

infixr 5 :<

data Vec :: Nat -> * -> * where
  VecZ :: Vec Zero a
  (:<) :: a -> Vec n a -> Vec (Succ n) a

-- | Type-safe head for vectors
headV :: Vec (Succ n) a -> a
headV (a :< _) = a

-- | Type-safe tail for vectors
tailV :: Vec (Succ n) a -> Vec n a
tailV (_ :< as') = as'

#endif

--------

-- Reification example for exporting

reified :: EP ((Bool, Bool) -> (Bool, Bool))
reified = reifyEP halfAdd

-- reified :: EP (Bool -> (Bool,Bool))
-- reified = reifyEP bar'

-- reified :: EP ((Bool,Bool) -> (Bool,Bool))
-- reified = reifyEP halfAddH

-- reified :: EP (Boo -> Bool)
-- reified = reifyEP caseQ

-- reified :: EP (A -> Bool)
-- reified = reifyEP case4

-- reified :: EP (Vec (Succ n) a -> Vec n a)
-- reified = reifyEP tailV
