{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

module LambdaCCC.Prim (Prim(..),Lit(..),xor,ifThenElse,cond) where

import LambdaCCC.Misc

-- | Primitives
data Prim :: * -> * where
  LitP          :: Lit a -> Prim a
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

data Lit :: * -> * where
  UnitL  :: Lit ()
  BoolL  :: Bool -> Lit Bool

instance Eq' (Lit a) (Lit b) where
  UnitL   === UnitL   = True
  BoolL x === BoolL y = x == y
  _       === _       = False

instance Eq (Lit a) where (==) = (===)

instance Eq' (Prim a) (Prim b) where
  LitP a === LitP b = a === b
  NotP   === NotP   = True
  AndP   === AndP   = True
  OrP    === OrP    = True
  XorP   === XorP   = True
  AddP   === AddP   = True
  ExlP   === ExlP   = True
  ExrP   === ExrP   = True
  PairP  === PairP  = True
  CondP  === CondP  = True
  _      === _      = False

instance Eq (Prim a) where (==) = (===)

instance Show (Lit a) where
  showsPrec p UnitL     = showsPrec p ()
  showsPrec p (BoolL b) = showsPrec p b

-- TODO: showsPrec p l = showsPrec p . eval
-- I'll need to construct a proof of Show a using the constraints/Dict trick.

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
  eval (LitP l)      = eval l
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

instance Evalable (Lit a) where
  type ValT (Lit a) = a
  eval UnitL  = ()
  eval (BoolL b) = b

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
