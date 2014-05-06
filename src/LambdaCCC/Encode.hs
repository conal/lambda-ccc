{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}   -- See below
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Encode
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Statically typed lambda expressions
----------------------------------------------------------------------

module LambdaCCC.Encode (Encodable(..)) where

import Control.Arrow ((***),(+++))
import Data.Monoid (Any(..),All(..))

import TypeUnary.TyNat (Z,S)
import TypeUnary.Vec (Vec(..))
import Circat.Pair (Pair(..))
import Circat.RTree (Tree(..))

import LambdaCCC.Misc (Unit,(:+),(:*))

infixr 1 -->
-- | Add pre- and post processing
(-->) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f

-- (-->) :: Category k =>
--          (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))

#define INS {-# INLINE encode #-} ; {-# INLINE decode #-}

class Encodable a where
  type Encode a
  encode :: a -> Encode a
  decode :: Encode a -> a

instance (Encodable a, Encodable b) => Encodable (a :* b) where
  type Encode (a :* b) = Encode a :* Encode b ; INS
  encode = encode *** encode
  decode = decode *** decode

instance (Encodable a, Encodable b) => Encodable (a :+ b) where
  type Encode (a :+ b) = Encode a :+ Encode b ; INS
  encode = encode +++ encode
  decode = decode +++ decode

instance (Encodable a, Encodable b) => Encodable (a -> b) where
  type Encode (a -> b) = Encode a -> Encode b ; INS
  encode = decode --> encode
  decode = encode --> decode

#define PrimEncode(t) \
 instance Encodable (t) where \
   { type Encode (t) = t ; INS ; encode = id ; decode = id }

PrimEncode(Unit)
PrimEncode(Bool)
PrimEncode(Int)

{--------------------------------------------------------------------
    Library types
--------------------------------------------------------------------}

#define NewtypeEncode(n,o,wrap,unwrap) \
  instance Encodable (n) where \
    { type Encode (n) = Encode (o) ; INS ; encode = encode . unwrap ; decode = wrap . decode }

NewtypeEncode(Any,Bool,Any,getAny)
NewtypeEncode(All,Bool,All,getAll)
-- etc

--     Application is no smaller than the instance head
--       in the type family application: Encode Bool
--     (Use UndecidableInstances to permit this)
--     In the type instance declaration for ‘Encode’
--     In the instance declaration for ‘Encodable (Any)’


-- TODO: Can we get some help from the Newtype class?

-- Sized types

instance Encodable a => Encodable (Pair a) where
  type Encode (Pair a) = Encode (a :* a) ; INS
  encode (a :# a') = (encode a, encode a')
  decode (b,b') = decode b :# decode b'

instance Encodable (Vec Z a) where
  type Encode (Vec Z a) = Unit ; INS
  encode ZVec = ()
  decode () = ZVec

instance (Encodable a, Encodable (Vec n a)) => Encodable (Vec (S n) a) where
  type Encode (Vec (S n) a) = Encode (a :* Vec n a) ; INS
  encode (a :< as) = (encode a, encode as)
  decode (b,bs) = decode b :< decode bs

instance Encodable (Tree Z a) where
  type Encode (Tree Z a) = a ; INS
  encode (L a) = a
  decode a = L a

instance Encodable (Tree n a) => Encodable (Tree (S n) a) where
  type Encode (Tree (S n) a) = Encode (Pair (Tree n a)) ; INS
  encode (B ts) = encode ts
  decode x = B (decode x)
