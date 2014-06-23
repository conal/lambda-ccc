{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=38 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Mono
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit Mono.hs -v0 -opt=LambdaCCC.Monomorphize DoMono.hss
--   
----------------------------------------------------------------------

module Mono where

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

import Prelude hiding (sum)

import Data.Foldable (Foldable(..),sum)

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)
-- import TypeUnary.Vec (Vec(..))

import Circat.Pair (Pair(..))
import Circat.RTree (Tree(..))

#define BuildDictBug

#ifdef BuildDictBug
-- Bug workaround. Hopefully remove soon See
-- <https://github.com/ku-fpg/hermit/issues/88#issuecomment-46869719> and later
-- comment.
import LambdaCCC.Encode (Encodable(..))
#endif

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- sum4 :: Tree N4 Int -> Int
-- sum4 = sum

test :: Tree Z Int -> Int
test = sum

-- test :: Pair Bool -> Bool
-- test (a :# b) = a || b

-- test :: Bool -> Bool
-- test = not

-- test :: Bool
-- test = False

-- foo :: Encodable a => a -> Encode a
-- foo = encode

-- test :: Tree Z Int -> Int
-- test = sum

-- test = encode (sum :: Tree Z Int -> Int)

-- test = encode (L 3 :: Tree Z Int)

-- -- test :: Tree Z Int -> Int
-- test :: Tree Z Int -> Encode (Tree Z Int)
-- test = encode
