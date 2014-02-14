{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, CPP #-}
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
  , Eq'(..), (==?)
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

infix 4 ===, ==?

-- | Equality when we don't know that the types match. Important requirement:
-- when the result is True, then it must be that a and b are the same type.
-- See '(==?)'.
class Eq' a b where
  (===) :: a -> b -> Bool

(==?) :: Eq' a b => a -> b -> Maybe (a :=: b)
a ==? b | a === b   = unsafeCoerce (Just Refl)
        | otherwise = Nothing

-- TODO: Maybe make (==?) the method and drop (===), moving the type proofs into
-- the instances and using unsafeCoerce only where necessary. Experiment in a
-- new branch. Alternatively, make (===) and (==?) *both* be methods, with
-- defaults defined in terms of each other.

-- newtype Untyped f = Untyped (forall a. f a)

-- instance Eq' f => Eq (Untyped f) where
--   Untyped fa == Untyped fb = fa === fb

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

class Evalable e where
  type ValT e
  eval :: e -> ValT e
