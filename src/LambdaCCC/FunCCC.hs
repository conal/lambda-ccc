{-# LANGUAGE TypeOperators, ExplicitForAll #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.FunCCC
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- CCC vocabulary for functions only
-- Most come from the Prelude
----------------------------------------------------------------------

module LambdaCCC.FunCCC
  ( (:->),(:*),(:=>),(&&&),apply
  -- , compFst,compSnd,applyComp
  , applyUnit
  ) where

import LambdaCCC.Misc ((:*),(:=>))

infix  0 :->
infixr 3 &&&

-- | Stand-in for arbitrary CCC
type (:->) = (->)

(&&&) :: forall a c d. (a :-> c) -> (a :-> d) -> (a :-> c :* d)
(f &&& g) a = (f a, g a) 

apply :: forall a b. (a :=> b) :* a :-> b
apply (f,a) = f a

-- compFst :: forall b b' c. (b  :-> c) -> (b :* b' :-> c)
-- compFst f = f . fst

-- compSnd :: forall b b' c. (b' :-> c) -> (b :* b' :-> c)
-- compSnd f = f . snd

-- applyComp :: forall a b c. (a :-> (b :=> c)) -> (a :-> b) -> (a :-> c)
-- applyComp h k = apply . (h &&& k)

applyUnit :: forall a. (() -> a) -> a
applyUnit f = f ()
