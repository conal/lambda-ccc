{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Prim
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Primitives
----------------------------------------------------------------------

module LambdaCCC.Prim (Prim(..)) where

import LambdaCCC.Misc

-- | Primitives
data Prim :: * -> * where
  Lit        :: Show a => a -> Prim a
  Pair       :: Prim (a :=> b :=> a :* b)
  Not        :: Prim (Bool :=> Bool)
  And,Or,Xor :: Prim (Bool :* Bool :=> Bool)
  Add        :: Num  a => Prim (a :* a :=> a)
  -- More here

instance Show (Prim a) where
  showsPrec p (Lit a) = showsPrec p a
  showsPrec _ Pair    = showString "(,)"
  showsPrec _ Not     = showString "not"
  showsPrec _ And     = showString "and"
  showsPrec _ Or      = showString "or"
  showsPrec _ Xor     = showString "xor"
  showsPrec _ Add     = showString "add"

instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (Lit x) = x
  eval Pair    = (,)
  eval Not     = not
  eval And     = uncurry (&&)
  eval Or      = uncurry (||)
  eval Xor     = uncurry (/=)
  eval Add     = uncurry (+)
