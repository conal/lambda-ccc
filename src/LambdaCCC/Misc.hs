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
  ( module Circat.Misc
  , Eq1'(..), (===?)
  ) where

import Unsafe.Coerce (unsafeCoerce)     -- see below

import Data.Proof.EQ ((:=:)(..))

import Circat.Misc

{--------------------------------------------------------------------
    Transformations
--------------------------------------------------------------------}

#if 0

-- | Unary transformation
type Unop  a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

-- | Compose list of unary transformations
compose :: [Unop a] -> Unop a
compose = foldr (.) id

#endif

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

-- | Equality when we don't know that the type parameters match.
class Eq1' f where
  (====) :: f a -> f b -> Bool

-- | Test for equality. If equal, generate a type equality proof. The proof
-- generation is done with @unsafeCoerce@, so it's very important that equal
-- terms really do have the same type.
(===?) :: Eq1' f => f a -> f b -> Maybe (a :=: b)
a ===? b | a ==== b  = unsafeCoerce (Just Refl)
         | otherwise = Nothing

-- TODO: Maybe eliminate Eq' and ==?. If so, rename (====) and (===?).
