{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Scan
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Parallel scan
----------------------------------------------------------------------

-- module Scan where

import Prelude hiding (foldr,sum,product)

import Data.Monoid (Monoid(..),(<>))
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)

import TypeUnary.TyNat
import Circat.Pair
import Circat.RTree

class LScan f where
  lscan :: Monoid a => f a -> (f a, a)

instance LScan Pair where
  lscan (a :# b) = (mempty :# a, a <> b)

instance LScan (Tree Z) where
  lscan (L a) = (L mempty, a)

instance LScan (Tree n) => LScan (Tree (S n)) where
  lscan (B ts)  = (B (adjust <$> zipA (tots',ts')), tot)
   where
     (ts' ,tots)   = unzipA (lscan <$> ts)
     (tots',tot)   = lscan tots
     adjust (p,t)  = (p <>) <$> t

zipA :: Applicative f => (f a, f b) -> f (a,b)
zipA = uncurry (liftA2 (,))

unzipA :: Applicative f => f (a,b) -> (f a, f b)
unzipA ps = (fst <$> ps, snd <$> ps)
