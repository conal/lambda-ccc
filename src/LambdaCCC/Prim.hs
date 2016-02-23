{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, ViewPatterns, PatternGuards, CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
-- {-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=35 #-}  -- for N32

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
  , Prim(..),litP -- ,xor,cond,ifThenElse
  -- , primArrow
  , PrimBasics(..), EvalableP(..)
  -- Convenient constraint aliases
  , CircuitEq, CircuitOrd, CircuitBot, CircuitNum
  , CircuitFloating, CircuitFractional, CircuitFromIntegral
  ) where

-- #define LitSources

import Prelude hiding (id,(.),curry,uncurry)

-- import Control.Arrow ((&&&))
import Data.Constraint (Dict(..))

import Circat.Category
import Circat.Classes

import Circat.Circuit (GenBuses,(:>)
#ifdef LitSources
                      , litUnit,litBool,litInt
#else
                      , constC
#endif
                      )

-- import TypeEncode.Encode (EncodeCat(..))

-- TODO: sort out the two uses of xor and simplify the Circat.Classes imports
-- and uses.

import Circat.Misc
import Circat.ShowUtils (Show'(..))
import Circat.Show (showsApp1)
import Circat.Doubli

{--------------------------------------------------------------------
    Literals
--------------------------------------------------------------------}

-- | Literals
data Lit :: * -> * where
  UnitL   :: Unit   -> Lit Unit
  BoolL   :: Bool   -> Lit Bool
  IntL    :: Int    -> Lit Int
  FloatL  :: Float  -> Lit Float
  DoubleL :: Doubli -> Lit Doubli

-- The Unit argument is just for uniformity

instance Eq' (Lit a) (Lit b) where
  UnitL   x === UnitL   y = x == y
  BoolL   x === BoolL   y = x == y
  IntL    x === IntL    y = x == y
  FloatL  x === FloatL  y = x == y
  DoubleL x === DoubleL y = x == y
  _         === _         = False

instance Eq (Lit a) where (==) = (===)

-- | Convenient 'Lit' construction
class HasLit a where toLit :: a -> Lit a

instance HasLit Unit   where toLit = UnitL
instance HasLit Bool   where toLit = BoolL
instance HasLit Int    where toLit = IntL
instance HasLit Float  where toLit = FloatL
instance HasLit Doubli where toLit = DoubleL

-- TODO: Do I still need this stuff?

-- Proofs

litHasShow :: Lit a -> Dict (Show a)
litHasShow (UnitL   _) = Dict
litHasShow (BoolL   _) = Dict
litHasShow (IntL    _) = Dict
litHasShow (FloatL  _) = Dict
litHasShow (DoubleL _) = Dict

#define LSh (litHasShow -> Dict)

-- instance Show (Lit a) where
--   showsPrec p UnitL     = showsPrec p ()
--   showsPrec p (BoolL b) = showsPrec p b
--   showsPrec p (IntL  b) = showsPrec p b

instance Show (Lit a) where
  showsPrec p l@LSh = showsPrec p (eval l)

litGenBuses :: Lit a -> Dict (GenBuses a)
litGenBuses (UnitL   _) = Dict
litGenBuses (BoolL   _) = Dict
litGenBuses (IntL    _) = Dict
litGenBuses (FloatL  _) = Dict
litGenBuses (DoubleL _) = Dict

#define LSo (litGenBuses -> Dict)

litSS :: Lit a -> Dict (Show a, GenBuses a)
litSS l | (Dict,Dict) <- (litHasShow l,litGenBuses l) = Dict

#define LS (litSS -> Dict)

instance Evalable (Lit a) where
  type ValT (Lit a) = a
  eval (UnitL   x) = x
  eval (BoolL   x) = x
  eval (IntL    x) = x
  eval (FloatL  x) = x
  eval (DoubleL x) = x

instance HasUnitArrow (->) Lit where
  unitArrow x = const (eval x)

instance HasUnitArrow (:>) Lit where
#ifdef LitSources
  unitArrow (UnitL   x) = litUnit   x
  unitArrow (BoolL   x) = litBool   x
  unitArrow (IntL    x) = litInt    x
  unitArrow (FloatL  x) = litFloat  x
  unitArrow (DoubleL x) = litDouble x
#else
  unitArrow l@LS = constC (eval l)
#endif

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

type CircuitEq           = EqCat           (:>)
type CircuitOrd          = OrdCat          (:>)
type CircuitBot          = BottomCat       (:>)
type CircuitNum          = NumCat          (:>)
type CircuitFractional   = FractionalCat   (:>)
type CircuitFloating     = FloatingCat     (:>)
type CircuitFromIntegral = FromIntegralCat (:>)

-- NOTE: When adding a constraint alias to the list above, be sure to export so
-- reifyStdMeth can find it.

-- | Primitives
data Prim :: * -> * where
  LitP             :: Lit a -> Prim a
  NotP             :: Prim (Bool -> Bool)
  AndP,OrP,XorP    :: Prim (Bool -> Bool -> Bool)
  NegateP          :: CircuitNum a => Prim (a -> a)
  AddP,SubP,MulP   :: CircuitNum a => Prim (a -> a -> a)
  RecipP           :: CircuitFractional a => Prim (a -> a)
  DivideP          :: CircuitFractional a => Prim (a -> a -> a)
  SinP, CosP, ExpP :: CircuitFloating a => Prim (a -> a)
  FromIP           :: CircuitFromIntegral a b => Prim (a -> b)
  EqP,NeP          :: CircuitEq  a => Prim (a -> a -> Bool)
  LtP,GtP,LeP,GeP  :: CircuitOrd a => Prim (a -> a -> Bool)
  ExlP             :: Prim (a :* b -> a)
  ExrP             :: Prim (a :* b -> b)
  InlP             :: Prim (a -> a :+ b)
  InrP             :: Prim (b -> a :+ b)
  PairP            :: Prim (a -> b -> a :* b)
  IfP              :: IfCat (:>) a => Prim (Bool :* (a :* a) -> a)
  AbstP            :: (HasRep a, Rep a ~ a') => Prim (a' -> a)
  ReprP            :: (HasRep a, Rep a ~ a') => Prim (a -> a')
  BottomP          :: BottomCat (:>) a => Prim a
  DelayP           :: (GenBuses s, Show s) => s -> Prim (s -> s)

instance Eq' (Prim a) (Prim b) where
  LitP a  === LitP b  = a === b
  NotP    === NotP    = True
  AndP    === AndP    = True
  OrP     === OrP     = True
  XorP    === XorP    = True
  NegateP === NegateP = True
  AddP    === AddP    = True
  SubP    === SubP    = True
  MulP    === MulP    = True
  RecipP  === RecipP  = True
  DivideP === DivideP = True
  ExpP    === ExpP    = True
  FromIP  === FromIP  = True
  CosP    === CosP    = True
  SinP    === SinP    = True
  EqP     === EqP     = True
  NeP     === NeP     = True
  LtP     === LtP     = True
  GtP     === GtP     = True
  LeP     === LeP     = True
  GeP     === GeP     = True
  ExlP    === ExlP    = True
  ExrP    === ExrP    = True
  InlP    === InlP    = True
  InrP    === InrP    = True
  PairP   === PairP   = True
  IfP     === IfP     = True
  AbstP   === AbstP   = True
  ReprP   === ReprP   = True
  BottomP === BottomP = True
  _       === _       = False

instance Eq (Prim a) where (==) = (===)

instance Show (Prim a) where
  showsPrec p (LitP a)      = showsPrec p a
  showsPrec _ NotP          = showString "not"
  showsPrec _ AndP          = showString "(&&)"
  showsPrec _ OrP           = showString "(||)"
  showsPrec _ XorP          = showString "xor"
  showsPrec _ NegateP       = showString "negate"
  showsPrec _ AddP          = showString "add"
  showsPrec _ SubP          = showString "sub"
  showsPrec _ RecipP        = showString "recip"
  showsPrec _ DivideP       = showString "divide"
  showsPrec _ MulP          = showString "mul"
  showsPrec _ ExpP          = showString "exp"
  showsPrec _ CosP          = showString "cos"
  showsPrec _ SinP          = showString "sin"
  showsPrec _ FromIP        = showString "fromIntegral"
  showsPrec _ EqP           = showString "(==)"
  showsPrec _ NeP           = showString "(/=)"
  showsPrec _ LtP           = showString "(<)"
  showsPrec _ GtP           = showString "(>)"
  showsPrec _ LeP           = showString "(<=)"
  showsPrec _ GeP           = showString "(>=)"
  showsPrec _ ExlP          = showString "exl"
  showsPrec _ InlP          = showString "Left"
  showsPrec _ InrP          = showString "Right"
  showsPrec _ ExrP          = showString "exr"
  showsPrec _ PairP         = showString "(,)"
  showsPrec _ IfP           = showString "ifC"
  showsPrec _ AbstP         = showString "abst"
  showsPrec _ ReprP         = showString "repr"
  showsPrec _ BottomP       = showString "undefined"
  showsPrec p (DelayP a)    = showsApp1 "delay" p a

instance Show' Prim where showsPrec' = showsPrec

#if 0

primArrow :: Prim (a :=> b) -> (a :> b)
primArrow NotP     = notC
primArrow AndP     = curry andC
primArrow OrP      = curry orC
primArrow XorP     = curry xorC
primArrow NegateP  = negateC
primArrow AddP     = curry add
primArrow SubP     = curry sub
primArrow MulP     = curry mul
primArrow RecipP   = recipC
primArrow DivideP  = curry divide
primArrow ExpP     = curry exp
primArrow CosP     = curry cos
primArrow SinP     = curry sin
primArrow FromIP   = fromIntegral
primArrow EqP      = curry equal
primArrow NeP      = curry notEqual
primArrow LtP      = curry lessThan
primArrow GtP      = curry greaterThan
primArrow LeP      = curry lessThanOrEqual
primArrow GeP      = curry greaterThanOrEqual
primArrow ExlP     = exl
primArrow ExrP     = exr
primArrow InlP     = inl
primArrow InrP     = inr
primArrow PairP    = curry id
primArrow IfP      = ifC
primArrow AbstP    = abstC
primArrow ReprP    = reprC
primArrow BottomP  = error "primArrow: BottomP" -- bottomC?
primArrow MealyP   = Mealy
primArrow (LitP _) = error ("primArrow: LitP with function type?!")

#endif

instance -- (ClosedCat k, CoproductCat k, BoolCat k, NumCat k Int, RepCat k)
         (k ~ (:>))
      => HasUnitArrow k Prim where
  unitArrow NotP       = unitFun notC
  unitArrow AndP       = unitFun (curry andC)
  unitArrow OrP        = unitFun (curry orC)
  unitArrow XorP       = unitFun (curry xorC)
  unitArrow NegateP    = unitFun negateC
  unitArrow AddP       = unitFun (curry addC)
  unitArrow SubP       = unitFun (curry subC)
  unitArrow MulP       = unitFun (curry mulC)
  unitArrow RecipP     = unitFun recipC
  unitArrow DivideP    = unitFun (curry divideC)
  unitArrow ExpP       = unitFun expC
  unitArrow CosP       = unitFun cosC
  unitArrow SinP       = unitFun sinC
  unitArrow FromIP     = unitFun fromIntegralC
  unitArrow EqP        = unitFun (curry equal)
  unitArrow NeP        = unitFun (curry notEqual)
  unitArrow LtP        = unitFun (curry lessThan)
  unitArrow GtP        = unitFun (curry greaterThan)
  unitArrow LeP        = unitFun (curry lessThanOrEqual)
  unitArrow GeP        = unitFun (curry greaterThanOrEqual)
  unitArrow ExlP       = unitFun exl
  unitArrow ExrP       = unitFun exr
  unitArrow InlP       = unitFun inl
  unitArrow InrP       = unitFun inr
  unitArrow PairP      = unitFun (curry id)
  unitArrow IfP        = unitFun ifC
  unitArrow AbstP      = unitFun abstC
  unitArrow ReprP      = unitFun reprC
  unitArrow BottomP    = bottomC
  unitArrow (DelayP a) = unitFun (delayC a)
  unitArrow (LitP l)   = unitArrow l

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
  eval NegateP       = negate
  eval AddP          = (+)
  eval SubP          = (-)
  eval MulP          = (*)
  eval RecipP        = recip
  eval DivideP       = (/)
  eval ExpP          = exp
  eval CosP          = cos
  eval SinP          = sin
  eval FromIP        = fromIntegral
  eval EqP           = (==)
  eval NeP           = (/=)
  eval LtP           = (<)
  eval GtP           = (>)
  eval LeP           = (<=)
  eval GeP           = (>=)
  eval ExlP          = fst
  eval ExrP          = snd
  eval InlP          = Left
  eval InrP          = Right
  eval PairP         = (,)
  eval IfP           = ifC
  eval AbstP         = abstC
  eval ReprP         = reprC
  eval BottomP       = error "eval on BottomP"
  eval (DelayP a)    = delay a

-- TODO: replace fst with exl, etc.

-- TODO: Split LitP out of Prim, and make Prim have domain and range. Then
-- revisit 'HasConstArrow', and implement Evalable (Prim a b) homomorphically.
-- See convertP in LambdaCCC.CCC.

litP :: HasLit a => a -> Prim a
litP = LitP . toLit

{--------------------------------------------------------------------
    Some prim classes. Move later.
--------------------------------------------------------------------}

class PrimBasics p where
  unitP :: p Unit
  pairP :: p (a :=> b :=> a :* b)

instance PrimBasics Prim where
  unitP = LitP (UnitL ())
  pairP = PairP

class EvalableP p where evalP :: p a -> a

instance EvalableP Prim where evalP = eval
