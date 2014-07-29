{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Recastable
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Class to assist translation of representational casts
----------------------------------------------------------------------

module LambdaCCC.Recastable (Recastable(..)) where

import Data.Monoid (Sum(..))   -- TODO: more
import Control.Arrow ((***))

import Circat.Rep

-- | Add pre- and post-processing
(-->) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f

class Recastable a a' where
  recast :: a -> a'
--   -- Temporary hack to avoid dictionary casts
--   recastDummy :: a
--   recastDummy = error "recastDummy"

instance Recastable (Sum a) a where
  recast = repr
instance Recastable a (Sum a) where
  recast = abst

-- TODO: more

instance (Recastable a' a, Recastable b b')
      => Recastable (a -> b) (a' -> b') where
  recast = recast --> recast

instance (Recastable a a', Recastable b b')
      => Recastable (a,b) (a',b') where
  recast = recast *** recast

instance Recastable a a where recast = id
