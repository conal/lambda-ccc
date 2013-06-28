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

module LambdaCCC.Prim (Prim(..),xor) where

import LambdaCCC.Misc

-- | Primitives
data Prim :: * -> * where
  LitP          :: Show a => a -> Prim a
  NotP          :: Prim (Bool -> Bool)
  AndP,OrP,XorP :: Prim (Bool -> Bool -> Bool)
  AddP          :: Num  a => Prim (a -> a -> a)
  FstP          :: Prim (a :* b -> a)
  SndP          :: Prim (a :* b -> b)
  PairP         :: Prim (a -> b -> a :* b)
  FalseP, TrueP :: Prim Bool
  -- More here

instance Show (Prim a) where
  showsPrec p (LitP a) = showsPrec p a
  showsPrec _ NotP     = showString "not"
  showsPrec _ AndP     = showString "(&&)"
  showsPrec _ OrP      = showString "(||)"
  showsPrec _ XorP     = showString "xor"
  showsPrec _ AddP     = showString "add"
  showsPrec _ FstP     = showString "fst"
  showsPrec _ SndP     = showString "snd"
  showsPrec _ PairP    = showString "(,)"
  showsPrec _ FalseP   = showString "False"
  showsPrec _ TrueP    = showString "True"

instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (LitP x) = x
  eval NotP     = not
  eval AndP     = (&&)
  eval OrP      = (||)
  eval XorP     = (/=)
  eval AddP     = (+)
  eval FstP     = fst
  eval SndP     = snd
  eval PairP    = (,)
  eval FalseP   = False
  eval TrueP    = True

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)

-- TODO: Replace xor with (/=)
