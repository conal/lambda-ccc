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

-- | Primitives
data Prim :: * -> * where
  LitP          :: (Eq a, Show a) => a -> Prim a
  NotP          :: Prim (Bool -> Bool)
  AndP,OrP,XorP :: Prim (Bool -> Bool -> Bool)
  AddP          :: Num  a => Prim (a -> a -> a)
  ExlP          :: Prim (a :* b -> a)
  ExrP          :: Prim (a :* b -> b)
  PairP         :: Prim (a -> b -> a :* b)
  CondP         :: Prim (Bool :* (a :* a) -> a)
  InlP          :: Prim (a -> a :+ b)
  InrP          :: Prim (b -> a :+ b)
  -- More here

instance Eq (Prim a) where
  LitP a == LitP b = a == b
  NotP   == NotP   = True
  AndP   == AndP   = True
  OrP    == OrP    = True
  XorP   == XorP   = True
  AddP   == AddP   = True
  ExlP   == ExlP   = True
  ExrP   == ExrP   = True
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
  showsPrec _ ExlP       = showString "exl"
  showsPrec _ ExrP       = showString "exr"
  showsPrec _ PairP      = showString "(,)"
  showsPrec _ InlP       = showString "Left"
  showsPrec _ InrP       = showString "Right"
  showsPrec _ CondP      = showString "cond"

instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (LitP x)      = x
  eval NotP          = not
  eval AndP          = (&&)
  eval OrP           = (||)
  eval XorP          = (/=)
  eval AddP          = (+)
  eval ExlP          = fst
  eval ExrP          = snd
  eval PairP         = (,)
  eval InlP          = Left
  eval InrP          = Right
  eval CondP         = cond

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)
{-# NOINLINE xor #-}

-- For desugaring if-then-else expressions (assuming RebindableSyntax)
ifThenElse :: Bool -> Binop a
ifThenElse i t e = cond (i,(t,e))
{-# INLINE ifThenElse #-}

cond :: (Bool, (a,a)) -> a
cond (True ,(a,_)) = a
cond (False,(_,b)) = b
{-# NOINLINE cond #-}
