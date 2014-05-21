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

import LambdaCCC.Encode (Encodable(..))

-- No longer hangs (with lintExprR)
#if 0
hang1 :: (Identity Bool, Identity ()) -> Identity (Bool,())
hang1 = uncurry (liftA2 (,))

hang :: Encode ((Identity Bool, Identity ()) -> Identity (Bool,()))
hang = encode hang1
#endif

#if 1
hang1 :: (Pair Bool, Pair ()) -> Pair (Bool,())
hang1 = uncurry (liftA2 (,))

hang :: Encode ((Pair Bool, Pair ()) -> Pair (Bool,()))
hang = encode hang1
#endif

