{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, ViewPatterns, PatternGuards, CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
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

module LambdaCCC.Prim
  ( Lit(..), HasLit(..), litSS
  , Prim(..),litP,xor,ifThenElse,cond
  ) where

import Prelude hiding (id,(.),not,and,or,curry,uncurry,const)

-- import Control.Arrow ((&&&))
import Data.Constraint (Dict(..))

import Circat.Category
import Circat.Classes (BoolCat(not,and,or))
import qualified Circat.Classes as C
import Circat.Circuit ((:>),IsSourceP,constC) -- :( . Disentangle!

-- TODO: sort out the two uses of xor and simplify the Circat.Classes imports
-- and uses.

import LambdaCCC.Misc
import LambdaCCC.ShowUtils (Show'(..))

{--------------------------------------------------------------------
    Literals
--------------------------------------------------------------------}

-- | Literals
data Lit :: * -> * where
  UnitL  :: Lit ()
  BoolL  :: Bool -> Lit Bool

instance Eq' (Lit a) (Lit b) where
  UnitL   === UnitL   = True
  BoolL x === BoolL y = x == y
  _       === _       = False

instance Eq (Lit a) where (==) = (===)

-- | Convenient 'Lit' construction
class HasLit a where toLit :: a -> Lit a

instance HasLit ()   where toLit = const UnitL
instance HasLit Bool where toLit = BoolL

-- Proofs

litHasShow :: Lit a -> Dict (Show a)
litHasShow UnitL     = Dict
litHasShow (BoolL _) = Dict

#define LSh (litHasShow -> Dict)

-- instance Show (Lit a) where
--   showsPrec p UnitL     = showsPrec p ()
--   showsPrec p (BoolL b) = showsPrec p b

-- instance Show (Lit a) where
--   showsPrec p l | Dict <- litHasShow l = showsPrec p l

instance Show (Lit a) where showsPrec p l@LSh = showsPrec p l

litIsSourceP :: Lit a -> Dict (IsSourceP a)
litIsSourceP UnitL     = Dict
litIsSourceP (BoolL _) = Dict

#define LSo (litIsSourceP -> Dict)

litSS :: Lit a -> (Dict (Show a, IsSourceP a))
litSS l | (Dict,Dict) <- (litHasShow l,litIsSourceP l) = Dict

#define LS (litSS -> Dict)

instance Evalable (Lit a) where
  type ValT (Lit a) = a
  eval UnitL     = ()
  eval (BoolL b) = b

instance HasConstArrow (->) Lit where
  constArrow x = const (eval x)

instance HasConstArrow (:>) Lit where
  constArrow l@LS = constC (eval l)

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

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

instance Show' Prim where showsPrec' = showsPrec

instance (BiCCC k, BoolCat k, HasConstArrow k Lit) =>
         HasConstArrow k Prim where
  constArrow NotP  = constFun not
  constArrow AndP  = constFun (curry and)
  constArrow OrP   = constFun (curry or)
  constArrow XorP  = constFun (curry C.xor)
  constArrow ExlP  = constFun exl
  constArrow ExrP  = constFun exr
  constArrow PairP = constFun (curry id)
  constArrow InlP  = constFun inl
  constArrow InrP  = constFun inr
  -- constArrow CondP = condC
  -- constArrow AddP  = curry (namedC "add")
  constArrow (LitP l) = constArrow l
  constArrow p     = error $ "constArrow: not yet handled: " ++ show p

--     Variable `k' occurs more often than in the instance head
--       in the constraint: BiCCC k
--     (Use -XUndecidableInstances to permit this)


instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (LitP l)      = eval l
  eval NotP          = not
  eval AndP          = (&&)
  eval OrP           = (||)
  eval XorP          = xor
  eval AddP          = (+)
  eval ExlP          = fst
  eval ExrP          = snd
  eval PairP         = (,)
  eval InlP          = Left
  eval InrP          = Right
  eval CondP         = cond

-- TODO: Split LitP out of Prim, and make Prim have domain and range. Then
-- revisit 'HasConstArrow', and implement Evalable (Prim a b) homomorphically.
-- See convertP in LambdaCCC.CCC.

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)
{-# NOINLINE xor #-}

-- For desugaring if-then-else expressions (assuming RebindableSyntax)
ifThenElse :: Bool -> Binop a
ifThenElse i t e = cond (i,(e,t)) -- note t/e swap
{-# INLINE ifThenElse #-}

-- cond :: (Bool, (a,a)) -> a
-- cond (True ,(a,_)) = a
-- cond (False,(_,b)) = b
-- {-# NOINLINE cond #-}

litP :: HasLit a => a -> Prim a
litP = LitP . toLit
