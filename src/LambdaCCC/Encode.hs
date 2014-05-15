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
import TypeUnary.Vec (Vec(..),unConsV)
import Circat.Pair (Pair(..),toP,fromP)
import Circat.RTree (Tree(..),toL,unL,toB,unB)

import LambdaCCC.Misc (Unit,(:+),(:*))

infixr 1 -->
-- | Add pre- and post processing
(-->) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f

-- (-->) :: Category k =>
--          (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))

-- Inlining!
#define INS {-# INLINE encode #-} ; {-# INLINE decode #-}

class Encodable a where
  type Encode a
  encode :: a -> Encode a
  decode :: Encode a -> a

#define EncTy(n,o) type Encode (n) = o ; INS

instance (Encodable a, Encodable b) => Encodable (a :* b) where
  -- EncTy(a :* b, Encode a :* Encode b)
  EncTy((a,b), (Encode a,Encode b))
  encode = encode *** encode
  decode = decode *** decode

instance (Encodable a, Encodable b) => Encodable (a :+ b) where
  EncTy(a :+ b, Encode a :+ Encode b)
  encode = encode +++ encode
  decode = decode +++ decode

instance (Encodable a, Encodable b) => Encodable (a -> b) where
  EncTy(a -> b, Encode a -> Encode b)
  encode = decode --> encode
  decode = encode --> decode

#define PrimEncode(t) \
 instance Encodable (t) where { EncTy(t,t) ; encode = id ; decode = id }

PrimEncode(Unit)
PrimEncode(Bool)
PrimEncode(Int)

-- instance Encodable Bool where
--   EncTy(Bool,() :+ ())
--   encode False = Left ()
--   encode True  = Right ()
--   decode (Left  ()) = False
--   decode (Right ()) = True

{--------------------------------------------------------------------
    Library types
--------------------------------------------------------------------}

#define EEncTy(n,o) EncTy(n,Encode(o))

#define RepEncode(n,o,wrap,unwrap) \
  instance Encodable (o) => Encodable (n) where \
    { EEncTy(n,o) ; encode = encode . (unwrap) ; decode = (wrap) . decode }

-- TODO: Can we get some help from the Newtype class?

RepEncode(Pair a, a :* a, toP, fromP)

RepEncode(Vec Z a, Unit, \ () -> ZVec, \ ZVec -> ())
RepEncode(Vec (S n) a, a :* Vec n a, uncurry (:<), unConsV)

RepEncode(Tree Z a, a, toL, unL)
RepEncode(Tree (S n) a, Pair (Tree n a), toB, unB)

-- Standard newtypes:
RepEncode(Any,Bool,Any,getAny)
RepEncode(All,Bool,All,getAll)
-- etc

--     Application is no smaller than the instance head
--       in the type family application: Encode Bool
--     (Use UndecidableInstances to permit this)
--     In the type instance declaration for ‘Encode’
--     In the instance declaration for ‘Encodable (Any)’

