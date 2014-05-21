{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=38 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Hang
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit Hang.hs -v0 -opt=LambdaCCC.NormalizeCore DoHang.hss
--   
----------------------------------------------------------------------

module Hang where

import Prelude hiding (foldr,sum)

import Control.Applicative (liftA2)

-- transformers
import Data.Functor.Identity
import Circat.Pair (Pair(..))
import TypeUnary.Vec (Vec(..))
import Circat.RTree (Tree(..))
import TypeUnary.TyNat

import LambdaCCC.Encode (Encodable(..))

-- Good
#if 0
hang1 :: (Identity Bool, Identity ()) -> Identity (Bool,())
hang1 = uncurry (liftA2 (,))

hang :: Encode ((Identity Bool, Identity ()) -> Identity (Bool,()))
hang = encode hang1
#endif

-- Good
#if 0
hang1 :: (Pair Bool, Pair ()) -> Pair (Bool,())
hang1 = uncurry (liftA2 (,))

hang :: Encode ((Pair Bool, Pair ()) -> Pair (Bool,()))
hang = encode hang1
#endif

-- Good
#if 0
hang1 :: (Tree N1 Bool, Tree N1 ()) -> Tree N1 (Bool,())
hang1 = uncurry (liftA2 (,))

hang :: Encode ((Tree N1 Bool, Tree N1 ()) -> Tree N1 (Bool,()))
hang = encode hang1
#endif

-- Good
#if 1
hang1 :: (Vec N1 Bool, Vec N1 ()) -> Vec N1 (Bool,())
hang1 = uncurry (liftA2 (,))

hang :: Encode ((Vec N1 Bool, Vec N1 ()) -> Vec N1 (Bool,()))
hang = encode hang1
#endif
