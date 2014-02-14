{-# LANGUAGE TypeOperators, TypeFamilies, CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Misc
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Miscellany
----------------------------------------------------------------------

module LambdaCCC.Misc
  ( Unop, Binop, compose
  , (:=>), (:+), (:*), Unit
  , Eq1'(..), Eq2'(..), unsafeEq1, unsafeEq2
  -- , Untyped(..)
  , Evalable(..)
  ) where

import Unsafe.Coerce (unsafeCoerce)     -- see below

import Data.Proof.EQ ((:=:)(..))

import Circat.Misc (Unop,Binop, Unit,(:+),(:*),(:=>))

{--------------------------------------------------------------------
    Transformations
--------------------------------------------------------------------}

#if 0

-- | Unary transformation
type Unop  a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

#endif

-- | Compose list of unary transformations
compose :: [Unop a] -> Unop a
compose = foldr (.) id

{--------------------------------------------------------------------
    Types
--------------------------------------------------------------------}

#if 0

infixr 1 :=>
infixl 6 :+
infixl 7 :*

TODO: Perhaps replace these definitions with a GADT to emphasize the
distinction between standard Haskell unit, cartesian product, and function
types, vs the categorical counterparts (terminal object, categorical
products, and coproducts).

type Unit  = ()
type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

#endif

{--------------------------------------------------------------------
    Equality
--------------------------------------------------------------------}

infix 4 ===, ====

-- | Equality when we don't know that the types match
class Eq1' f where
  (===) :: f a -> f b -> Bool

-- | Equality when we don't know that the types match
class Eq2' k where
  (====) :: k a b -> k c d -> Bool

unsafeEq1 :: Eq1' f => f a -> f b -> Maybe (a :=: b)
fa `unsafeEq1` fb | fa === fb = unsafeCoerce (Just Refl)
                  | otherwise = Nothing

unsafeEq2 :: Eq2' k => k a b -> k c d -> Maybe ((a,c) :=: (b,d))
kab `unsafeEq2` kcd | kab ==== kcd = unsafeCoerce (Just Refl)
                    | otherwise    = Nothing

-- newtype Untyped f = Untyped (forall a. f a)

-- instance Eq' f => Eq (Untyped f) where
--   Untyped fa == Untyped fb = fa === fb

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

class Evalable e where
  type ValT e
  eval :: e -> ValT e
