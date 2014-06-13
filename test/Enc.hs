{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=38 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Enc
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit Enc.hs -v0 -opt=LambdaCCC.CoreEncode DoEnc.hss
--   
----------------------------------------------------------------------

module Enc where

import Prelude hiding (foldr,sum,or)

import Data.Foldable (foldr,sum,or)

-- import Control.Applicative (liftA2)

-- -- transformers
-- import Data.Functor.Identity
import Circat.Pair (Pair(..))

import TypeUnary.TyNat
import TypeUnary.Vec

-- #define TreeSplit

#ifdef TreeSplit
import Circat.RTreeS
#else
import Circat.RTree
#endif

import LambdaCCC.Encode (Encodable(..),recode)

-- e_a = encode True
-- e_b = encode not
-- e_d = encode (||)
-- e_e = encode (False :# True)
-- e_f = encode ZVec
-- e_g = encode (True :< ZVec)
-- e_h = encode ((:<) :: Bool -> Vec0 Bool -> Vec1 Bool)

-- e_i = encode (fmap not (True :< False :< ZVec))
-- e_k = encode (False,())
-- e_l = encode (fmap :: ((Int -> Bool) -> Vec1 Int -> Vec1 Bool))
-- e_m = encode (fmap odd :: (Vec1 Int -> Vec1 Bool))
-- e_n = encode (fmap odd ((3 :: Int) :< ZVec))
-- e_o = encode (fmap not (True :< ZVec))
-- e_p = encode ((\ n -> n > 0) :: Int -> Bool)
-- e_q = encode (fmap (\ n -> n > 0) :: Vec N1 Int -> Vec N1 Bool)
-- e_r = encode ((\ x -> x + x) :: Int -> Int)

-- e_s = encode (fmap :: ((Int -> Bool) -> Tree N1 Int -> Tree N1 Bool))

-- e_t = encode (fmap not :: Tree N2 Bool -> Tree N2 Bool)
-- e_u = encode (fmap not :: Vec N4 Bool -> Vec N4 Bool)

-- e = encode (fmap :: (Int -> Bool) -> Tree N2 Int -> Tree N2 Bool)

-- e = encode (or (False :< True :< ZVec))

-- -- Hangs up on a cast.
-- e = encode (or :: Vec N1 Bool -> Bool)

e = encode (fmap :: ((Int -> Bool) -> Tree N1 Int -> Tree N1 Bool))
