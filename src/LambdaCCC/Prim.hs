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

module LambdaCCC.Prim (Prim(..),xor,ifThenElse,cond) where

import Data.IsTy

import LambdaCCC.Misc
import LambdaCCC.Ty
import LambdaCCC.ShowUtils (showsApp1)

-- | Primitives
data Prim :: * -> * where
  LitP          :: (Eq a, Show a) => a -> Prim a
  NotP          :: Prim (Bool -> Bool)
  AndP,OrP,XorP :: Prim (Bool -> Bool -> Bool)
  AddP          :: Num  a => Prim (a -> a -> a)
  FstP          :: Prim (a :* b -> a)
  SndP          :: Prim (a :* b -> b)
  PairP         :: Prim (a -> b -> a :* b)
  CondP         :: Prim (Bool :* (a :* a) -> a)
  -- More here
  ConstP        :: Prim b -> Prim (a -> b)

instance Eq (Prim a) where
  LitP a == LitP b = a == b
  NotP   == NotP   = True
  AndP   == AndP   = True
  OrP    == OrP    = True
  XorP   == XorP   = True
  AddP   == AddP   = True
  FstP   == FstP   = True
  SndP   == SndP   = True
  PairP  == PairP  = True
  CondP  == CondP  = True
  _      == _      = False

instance IsTy Prim where
  type IsTyConstraint Prim z = HasTy z
  tyEq = tyEq'

instance Show (Prim a) where
  showsPrec p (LitP a)   = showsPrec p a
  showsPrec _ NotP       = showString "not"
  showsPrec _ AndP       = showString "(&&)"
  showsPrec _ OrP        = showString "(||)"
  showsPrec _ XorP       = showString "xor"
  showsPrec _ AddP       = showString "add"
  showsPrec _ FstP       = showString "fst"
  showsPrec _ SndP       = showString "snd"
  showsPrec _ PairP      = showString "(,)"
  showsPrec _ CondP      = showString "cond"
  showsPrec p (ConstP w) = showsApp1 "const" p w

instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (LitP x)      = x
  eval NotP          = not
  eval AndP          = (&&)
  eval OrP           = (||)
  eval XorP          = (/=)
  eval AddP          = (+)
  eval FstP          = fst
  eval SndP          = snd
  eval PairP         = (,)
  eval CondP         = cond
  eval (ConstP w)    = const (eval w)

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)
{-# NOINLINE xor #-}

ifThenElse :: Bool -> Binop a
ifThenElse i t e = cond (i,(t,e))
{-# INLINE ifThenElse #-}

cond :: (Bool, (a,a)) -> a
cond (True ,(a,_)) = a
cond (False,(_,b)) = b
{-# NOINLINE cond #-}
