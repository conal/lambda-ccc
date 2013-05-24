{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures, CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.CCC
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- GADT of CCC combinators
----------------------------------------------------------------------

module LambdaCCC.CCC
  ( (:->)(..), (@.)
  , (&&&), (***), (+++), (|||)
  , dup, jam, swapP, swapC
  , first, second, left, right
  ) where

import qualified Control.Arrow as A

import LambdaCCC.Misc
import LambdaCCC.ShowUtils
import LambdaCCC.Prim

infix  0 :->
infixr 3 &&&, ***
infixr 2 |||, +++
infixr 9 :.

infixr 3 :&&&
infixr 2 :|||

-- Whether to simply (fold) during show
#define ShowFolded

-- Whether to simplify during construction
#define Simplify

-- | CCC combinator expressions. Although we use standard Haskell unit,
-- cartesian product, and function types here, the intended interpretation is as
-- the categorical counterparts (terminal object, categorical products, and
-- coproducts).
data (:->) :: * -> * -> * where
  Id       :: a :-> a
  (:.)     :: (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Primitives. I'm unsure of this one. It's closer to UKonst than I like.
  Prim     :: Prim (a :=> b) -> (a :-> b)
  -- Constant
  Konst    :: Prim b -> (a :-> b)
  -- Products
  Fst      :: a :* b :-> a
  Snd      :: a :* b :-> b
  (:&&&)   :: (a :-> c) -> (a :-> d) -> (a :-> c :* d)
  -- Coproducts
  InL      :: a :-> a :+ b
  InR      :: b :-> a :+ b
  (:|||)   :: (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
  -- Exponentials
  Apply    :: ((a :=> b) :* a) :-> b
  Curry    :: (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry  :: (a :-> (b :=> c)) -> (a :* b :-> c)

instance Evalable (a :-> b) where
  type ValT (a :-> b) = a :=> b
  eval Id          = id
  eval (g :. f)    = eval g . eval f
  eval (Konst b)   = const (eval b)
  eval (Prim p)    = eval p
  eval Fst         = fst
  eval Snd         = snd
  eval (f :&&& g)  = eval f A.&&& eval g
  eval InL         = Left
  eval InR         = Right
  eval (f :||| g)  = eval f A.||| eval g
  eval Apply       = uncurry ($)
  eval (Curry   h) = curry   (eval h)
  eval (Uncurry f) = uncurry (eval f)

infixr 9 @.
-- | Optimizing arrow composition
(@.) :: (b :-> c) -> (a :-> b) -> (a :-> c)
#ifdef Simplify
Id      @. f                = f
g       @. Id               = g
Konst k @. _                = Konst k
Apply   @. (Konst k :&&& f) = Prim k @. f
#endif
g @. f  = g :. f

dup :: a :-> a :* a
dup = Id &&& Id

jam :: a :+ a :-> a
jam = Id ||| Id

swapP :: a :* b :-> b :* a
swapP = Snd &&& Fst

swapC :: a :+ b :-> b :+ a
swapC = InR ||| InL

(&&&) :: (a :-> c) -> (a :-> d) -> (a :-> c :* d)
#ifdef Simplify
Fst &&& Snd = Id
#endif
f &&& g = f :&&& g

(***) :: (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
f *** g = f @. Fst &&& g @. Snd

first :: (a :-> c) -> (a :* b :-> c :* b)
first f = f *** Id

second :: (b :-> d) -> (a :* b :-> a :* d)
second g = Id *** g

(|||) :: (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
(|||) = (:|||)

(+++) :: (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
f +++ g = InL @. f ||| InR @. g

left :: (a :-> c) -> (a :+ b :-> c :+ b)
left f = f +++ Id

right :: (b :-> d) -> (a :+ b :-> a :+ d)
right g = Id +++ g

instance Show (a :-> b) where
#ifdef ShowFolded
  showsPrec p (f :. Fst :&&& g :. Snd) = showsOp2'  "***" (3,AssocRight) p f g
  showsPrec p (InL :. f :||| InR :. g) = showsOp2'  "+++" (2,AssocRight) p f g
  showsPrec _ (Id :&&& Id)             = showString "dup"
  showsPrec _ (Id :||| Id)             = showString "jam"
  showsPrec _ (Snd :&&& Fst)           = showString "swapP"
  showsPrec _ (InR :&&& InL)           = showString "swapC"
  showsPrec p (f :. Fst :&&& Snd)      = showsApp1  "first"  p f
  showsPrec p (Fst :&&& g :. Snd)      = showsApp1  "second" p g
  showsPrec p (InL :. f :||| InR)      = showsApp1  "left"   p f
  showsPrec p (InL :||| InR :. g)      = showsApp1  "right"  p g
#endif
  showsPrec _ Id          = showString "id"
  showsPrec p (g :. f)    = showsOp2'  "."  (9,AssocRight) p g f
  showsPrec p (Prim x)    = showsApp1 "prim" p x    -- or: showsPrec p x
  showsPrec p (Konst b)   = showsApp1 "konst" p b
  showsPrec p (f :&&& g)  = showsOp2' "&&&" (3,AssocRight) p f g
  showsPrec p (f :||| g)  = showsOp2' "|||" (2,AssocRight) p f g
  showsPrec _ Fst         = showString "fst"
  showsPrec _ Snd         = showString "snd"
  showsPrec _ InL         = showString "inL"
  showsPrec _ InR         = showString "inR"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry   f) = showsApp1  "curry"   p f
  showsPrec p (Uncurry h) = showsApp1  "Uncurry" p h
