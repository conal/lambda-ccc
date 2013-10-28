{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds, GADTs #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
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

instance Encodable Any where
  { type Encode Any = Encode Bool ; encode = encode . getAny ; decode = Any . decode }

instance Encodable All where
  { type Encode All = Encode Bool ; encode = encode . getAll ; decode = All . decode }

-- etc

-- Uniform pairs
data Pair a = a :#: a deriving (Eq,Show,Functor,Foldable,Traversable)

instance Encodable a => Encodable (Pair a) where
  type Encode (Pair a) = Encode (a :* a)
  encode (a :#: a') = (encode a, encode a')
  decode (u,u') = decode u :#: decode u'

data Nat = Z | S Nat

-- Depth-typed, top-down, perfect, binary leaf trees
data T :: Nat -> * -> * where
  L :: a -> T Z a
  B :: Pair (T n a) -> T (S n) a

instance Encodable (T Z a) where
  type Encode (T Z a) = a
  encode (L a) = a
  decode a = L a

instance Encodable (T n a) => Encodable (T (S n) a) where
  type Encode (T (S n) a) = Encode (Pair (T n a))
  encode (B ts) = encode ts
  decode x = B (decode x)

-- Expressions
data E a

idE :: E (a -> a)
idE = undefined

reifyE :: Encodable a => a -> E (Encode a)
reifyE = error "reifyE: Oops! Not rewritten away."

infixr 3 &&*
infixr 2 ||*

(&&*), (||*) :: E (Binop (Encode Bool))
(&&*) = undefined
(||*) = undefined

{-# RULES
"reifyE/id"           reifyE id                  = idE
"reifyE/(&&)"         reifyE (&&)                = (&&*)
"reifyE/(||)"         reifyE (||)                = (||*)
"reifyE/Any"          reifyE Any                 = reifyE (id :: Unop Bool)  -- = idE
"reifyE/All"          reifyE All                 = reifyE (id :: Unop Bool)  -- = idE
"reifyE/mappend Any"  reifyE ((<>) :: Binop Any) = reifyE (||)
"reifyE/mappend All"  reifyE ((<>) :: Binop All) = reifyE (&&)
  #-}

-- instance Encodable a => Encodable [a] where
--   -- type Encode [a] = Encode (() :+ a :* [a])
--   type Encode [a] = () :+ a :* Encode [a]
--   encode []     = Left  ()
--   encode (a:as) = Right (encode (a,as))
--   decode (Left  ()    ) = []    
--   decode (Right (a,as)) = decode a : decode as


-- Oops! Infinite type:
-- 
--     Occurs check: cannot construct the infinite type:
--       uf0 = (Encode a, Either () uf0)
--     Expected type: Encode [a]
--       Actual type: Either () (Encode a, Either () uf0)
--     In the return type of a call of `Right'
--     In the expression: Right (encode (a, as))
--     In an equation for `decode':
--         encode (a : as) = Right (encode (a, as))
