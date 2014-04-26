{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Encode
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Test conversion of Haskell source code into circuits. To run:
-- 
--   hermit Encode.hs -v0 -opt=LambdaCCC.Reify Auto.hss
--   
----------------------------------------------------------------------

module Encode where

import Prelude hiding (max)
import Control.Arrow ((***),(+++))

import LambdaCCC.Lambda (EP,reifyEP)

type Unop  a = a -> a
type Binop a = a -> Unop a

infixl 6 :+
infixl 7 :*

type Unit  = ()
type (:*)  = (,)
type (:+)  = Either

infixr 1 -->
-- | Add pre- and post processing
(-->) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f

-- (-->) :: Category k =>
--          (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))

class Encodable a where
  type Enc a
  encode :: a -> Enc a
  decode :: Enc a -> a

instance Encodable () where
  type Enc () = ()
  encode = id
  decode = id

instance (Encodable a, Encodable b) => Encodable (a :* b) where
  type Enc (a :* b) = Enc a :* Enc b
  encode = encode *** encode
  decode = decode *** decode

instance (Encodable a, Encodable b) => Encodable (a :+ b) where
  type Enc (a :+ b) = Enc a :+ Enc b
  encode = encode +++ encode
  decode = decode +++ decode

instance (Encodable a, Encodable b) => Encodable (a -> b) where
  type Enc (a -> b) = Enc a -> Enc b
  encode = decode --> encode
  decode = encode --> decode

infixr 5 :<

data Nat = Z | S Nat

-- | Vectors with type-determined length, having empty vector ('ZVec') and
-- vector cons ('(:<)').
data Vec :: Nat -> * -> * where
  ZVec :: Vec Z a
  (:<) :: a -> Vec n a -> Vec (S n) a

instance Functor (Vec n) where
  fmap _ ZVec     = ZVec
  fmap f (a :< u) = f a :< fmap f u

-- Applicative, Monad, Monoid, Foldable, Traversable. See type-unary.

-- instance Encodable Bool where { type Enc Bool = Bool ; encode = id ; decode = id }

#define IdEnc(ty) instance Encodable (ty) where { type Enc (ty) = ty ; encode = id ; decode = id }

IdEnc(Bool)

instance Encodable (Vec Z a) where
  type Enc (Vec Z a) = ()
  encode ZVec = ()
  decode () = ZVec

instance (Encodable a, Encodable (Vec n a)) => Encodable (Vec (S n) a) where
  type Enc (Vec (S n) a) = (Enc a, Enc (Vec n a))
  encode (a :< as) = (encode a, encode as)
  decode (b,bs) = decode b :< decode bs

-- I don't know how to express these instances with type-level naturals.

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2
type N4 = S N3

-- Operate within a vector
onVec :: b -> (forall m. n ~ S m => a -> Vec m a -> b) -> Vec n a -> b
onVec ze _ ZVec      = ze
onVec _ su (a :< as) = su a as

-- Scott-endcoding
scottVec :: Vec n a -> (b -> (forall m. n ~ S m => a -> Vec m a -> b) -> b)
scottVec v ze su = onVec ze su v

----

t0 :: Vec N0 Bool
t0 = ZVec

e0 :: ()
e0 = encode t0

-- t1 :: Vec N1 Bool
t1 :: Vec (S Z) Bool
t1 = True :< ZVec

e1 :: (Bool,())
e1 = encode t1

x1 :: EP (Bool,())
x1 = reifyEP e1

t3 :: Vec N3 Bool
t3 = True :< False :< True :< ZVec

-- e3 :: (Bool,(Bool,(Bool,())))
e3 :: Enc (Vec N3 Bool)
e3 = encode t3

x3 :: EP (Bool,(Bool,(Bool,())))
x3 = reifyEP e3

-- reified :: EP (Int, Vec N2 Int)
-- reified = reifyEP v4

-- headV :: Vec (S n) Int -> Int
-- headV (x :< _) = x

-- bar :: Int
-- bar = headV (10 :< ZVec)

t4 :: Vec N1 Bool -> Vec N1 Bool
t4 = fmap not

e4 :: Enc (Vec N1 Bool -> Vec N1 Bool)
e4 = encode t4

x4 :: EP (Enc (Vec N1 Bool -> Vec N1 Bool))
x4 = reifyEP e4

-- Try some simpler examples, say `encode (True :< ZVec) :: (Bool,())`.

x5 :: EP (Bool,())
x5 = reifyEP (encode (True :< ZVec))

x6 :: EP (Bool,(Bool,(Bool,())))
x6 = reifyEP (encode (True :< False :< True :< ZVec))

x7 :: EP (Vec N2 Bool)
x7 = reifyEP (decode (True,(False,())))

-- Now encode by itself:

x8 :: EP (Vec N1 Bool -> (Bool,()))
-- x8 :: EP (Vec N0 Bool -> ())
x8 = reifyEP encode
