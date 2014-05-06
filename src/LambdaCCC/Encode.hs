{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds, GADTs #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, EmptyDataDecls #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module LambdaCCC.Encode where

-- import Prelude hiding (id,(.))
import Data.Foldable
import Data.Traversable
-- import Control.Category (Category(..))
import Control.Arrow ((***),(+++),(|||))

import Data.Monoid

import TypeUnary.Vec
import Circat.Pair
import Circat.RTree

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
  type Encode a
  encode :: a -> Encode a
  decode :: Encode a -> a

instance Encodable () where
  type Encode () = ()
  encode = id
  decode = id

instance (Encodable a, Encodable b) => Encodable (a :* b) where
  type Encode (a :* b) = Encode a :* Encode b
  encode = encode *** encode
  decode = decode *** decode

instance (Encodable a, Encodable b) => Encodable (a :+ b) where
  type Encode (a :+ b) = Encode a :+ Encode b
  encode = encode +++ encode
  decode = decode +++ decode

instance (Encodable a, Encodable b) => Encodable (a -> b) where
  type Encode (a -> b) = Encode a -> Encode b
  encode = decode --> encode
  decode = encode --> decode

-- instance Encodable Bool where
--   { type Encode Bool = Bool ; encode = id ; decode = id }

instance Encodable Bool where
  type Encode Bool = () :+ ()
  encode False = Left ()
  encode True  = Right ()
  decode (Left  ()) = False
  decode (Right ()) = True

-- instance Encodable Bool where
--   type Encode Bool = () :+ ()
--   encode = bool (Left ()) (Right ())
--   decode = const False ||| const True

bool :: a -> a -> Bool -> a
bool t e i = if i then t else e

{--------------------------------------------------------------------
    Library types
--------------------------------------------------------------------}

instance Encodable Any where
  { type Encode Any = Encode Bool ; encode = encode . getAny ; decode = Any . decode }

instance Encodable All where
  { type Encode All = Encode Bool ; encode = encode . getAll ; decode = All . decode }

-- etc

-- TODO: Can we get some help from the Newtype class?

instance Encodable a => Encodable (Pair a) where
  type Encode (Pair a) = Encode (a :* a)
  encode (a :# a') = (encode a, encode a')
  decode (b,b') = decode b :# decode b'

instance Encodable (Vec Z a) where
  type Encode (Vec Z a) = Unit
  encode ZVec = ()
  decode () = ZVec

instance (Encodable a, Encodable (Vec n a)) => Encodable (Vec (S n) a) where
  type Encode (Vec (S n) a) = Encode (a :* Vec n a)
  encode (a :< as) = (encode a, encode as)
  decode (b,bs) = decode b :< decode bs

instance Encodable (Tree Z a) where
  type Encode (Tree Z a) = a
  encode (L a) = a
  decode a = L a

instance Encodable (Tree n a) => Encodable (Tree (S n) a) where
  type Encode (Tree (S n) a) = Encode (Pair (Tree n a))
  encode (B ts) = encode ts
  decode x = B (decode x)
