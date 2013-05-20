{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Misc
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Misc defs
----------------------------------------------------------------------

module LambdaCCC.Misc where

-- TODO: explicit exports

infixr 1 :=>
infixl 6 :+
infixl 7 :*

type Unit  = ()
type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)
