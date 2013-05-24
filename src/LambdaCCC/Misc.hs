{-# LANGUAGE TypeOperators, TypeFamilies #-}
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

module LambdaCCC.Misc where

-- TODO: explicit exports

{--------------------------------------------------------------------
    Transformations
--------------------------------------------------------------------}

-- | Unary transformation
type Unop  a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

-- | Compose list of unary transformations
compose :: [Unop a] -> Unop a
compose = foldr (.) id

{--------------------------------------------------------------------
    Types
--------------------------------------------------------------------}

infixr 1 :=>
infixl 6 :+
infixl 7 :*

-- TODO: Perhaps replace these definitions with a GADT to emphasize the
-- distinction between standard Haskell unit, cartesian product, and function
-- types, vs the categorical counterparts (terminal object, categorical
-- products, and coproducts).

type Unit  = ()
type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

class Evalable e where
  type ValT e
  eval :: e -> ValT e
