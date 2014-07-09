{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs, TypeOperators #-}
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

import Data.Monoid (Sum)
import Data.Foldable (Foldable(..),sum)

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)
import TypeUnary.Vec (Vec(..))

import Circat.Pair (Pair(..))
import Circat.RTree (Tree(..))

-- #define BuildDictBug

#ifdef BuildDictBug
-- Bug workaround. Hopefully remove soon See
-- <https://github.com/ku-fpg/hermit/issues/88#issuecomment-46869719> and later
-- comment.
import LambdaCCC.Encode (Encodable(..))
#endif

import LambdaCCC.Misc (Unop)

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- test :: ()
-- test = ()

-- test :: Pair Bool -> Pair Bool
-- test = id

-- test :: Pair Bool -> Pair Bool
-- test (x :# y) = (y :# x)

-- test :: Tree N0 Int -> Tree N0 Int
-- test = id

-- test :: Vec N6 Int -> Vec N6 Int
-- test = id

-- test :: Tree N0 Int
-- test = L 3

-- test :: Tree N1 Int
-- test = B (L 3 :# L 4)

-- test :: Int -> Tree N0 Int
-- test = L

-- test :: Pair (Tree N0 Int) -> Tree N1 Int
-- test = B

-- test :: (Bool,Int,Bool)
-- test = (True,3,False)

test :: Tree N8 Int -> Int
test = sum

-- test :: Int -> Bool
-- test = even

-- test :: Tree N3 Int -> Tree N3 Bool
-- test = fmap even

-- test = undefined

-- test :: Unop (Tree N4 Bool)
-- test = fmap not

-- test = encode (fmap not :: Tree N1 Bool -> Tree N1 Bool)

-- type EncTy a = a -> Encode a

-- test :: EncTy (Tree N0 Bool -> Tree N0 Bool)
-- test = encode

-- test = encode (sum :: Tree N2 Int -> Int)

-- test :: Pair Bool -> Bool
-- test (a :# b) = a || b

-- test :: Pair Int -> Int
-- test = sum

-- test :: Pair (Sum Int) -> Sum Int
-- test = fold

-- test :: Bool -> Bool
-- test = not

-- test :: Bool
-- test = False
