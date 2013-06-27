{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures, CPP #-}
{-# LANGUAGE ConstraintKinds #-}
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
  ( module LambdaCCC.Misc
  , (:->)(..), cccTys, (@.)
  , (&&&), (***), (+++), (|||)
  , dup, jam, swapP, swapC
  , first, second, left, right
  ) where

import qualified Control.Arrow as A

import LambdaCCC.Misc (Evalable(..),(:*),(:+),(:=>))
import LambdaCCC.ShowUtils (showsApp1,showsOp2',Assoc(..))
import LambdaCCC.Ty
import LambdaCCC.Prim (Prim(..))

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
  Id       :: HasTy a => a :-> a
  (:.)     :: HasTy3 a b c => (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Primitives. I'm unsure of this one. It's closer to UKonst than I like.
  Prim     :: HasTy2 a b => Prim (a -> b) -> (a :-> b) -- TODO: Prim (a :=> b)?
  -- Constant
  Konst    :: HasTy2 a b => Prim b -> (a :-> b)
  -- Products
  Fst      :: HasTy2 a b => a :* b :-> a
  Snd      :: HasTy2 a b => a :* b :-> b
  (:&&&)   :: HasTy3 a c d => (a :-> c) -> (a :-> d) -> (a :-> c :* d)
  -- Coproducts
  Lft      :: HasTy2 a b => a :-> a :+ b
  Rht      :: HasTy2 a b => b :-> a :+ b
  (:|||)   :: HasTy3 a b c => (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
  -- Exponentials
  Apply    :: HasTy2 a b   => ((a :=> b) :* a) :-> b
  Curry    :: HasTy3 a b c => (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry  :: HasTy3 a b c => (a :-> (b :=> c)) -> (a :* b :-> c)

-- TODO: The type constraints prevent (:->) from being a category etc without
-- some change to those classes, e.g., with instance-specific constraints via
-- ConstraintKinds.

typ2 :: HasTy2 a b => (Ty a, Ty b)
typ2 = (typ,typ)

cccTys :: (a :-> b) -> (Ty a, Ty b)
cccTys Id      {} = typ2
cccTys (:.)    {} = typ2
cccTys Prim    {} = typ2
cccTys Konst   {} = typ2
cccTys Fst     {} = typ2
cccTys Snd     {} = typ2
cccTys (:&&&)  {} = typ2
cccTys Lft     {} = typ2
cccTys Rht     {} = typ2
cccTys (:|||)  {} = typ2
cccTys Apply   {} = typ2
cccTys Curry   {} = typ2
cccTys Uncurry {} = typ2

-- Maybe parametrize this GADT by a constraint. Sadly, I'd lose the pretty infix
-- syntax ("a :-> b").

instance Evalable (a :-> b) where
  type ValT (a :-> b) = a :=> b
  eval Id          = id
  eval (g :. f)    = eval g . eval f
  eval (Konst b)   = const (eval b)
  eval (Prim p)    = eval p
  eval Fst         = fst
  eval Snd         = snd
  eval (f :&&& g)  = eval f A.&&& eval g
  eval Lft         = Left
  eval Rht         = Right
  eval (f :||| g)  = eval f A.||| eval g
  eval Apply       = uncurry ($)
  eval (Curry   h) = curry   (eval h)
  eval (Uncurry f) = uncurry (eval f)

infixr 9 @.
-- | Optimizing arrow composition
(@.) :: HasTy3 a b c => (b :-> c) -> (a :-> b) -> (a :-> c)
#ifdef Simplify
Id      @. f                      = f
g       @. Id                     = g
Konst k @. _                      = Konst k
Apply   @. (Konst k       :&&& f) = Prim k @. f
Apply   @. (h@Prim{} :. f :&&& g) = Uncurry h @. (f  &&& g)
Apply   @. (h@Prim{}      :&&& g) = Uncurry h @. (Id &&& g)
#endif
g @. f  = g :. f

-- Note: the Prim{} specialization is unnecessary for validity but I suspect
-- useful for introducing just the uncurryings we want. TODO: verify.
--
-- Note: the second Uncurry specializes the first one, but is needed for
-- syntactic matching.

dup :: HasTy a => a :-> a :* a
dup = Id &&& Id

jam :: HasTy a => a :+ a :-> a
jam = Id ||| Id

-- | Product swap
swapP :: HasTy2 a b => a :* b :-> b :* a
swapP = Snd &&& Fst

-- | Coproduct swap
swapC :: HasTy2 a b => a :+ b :-> b :+ a
swapC = Rht ||| Lft

(&&&) :: HasTy3 a c d => (a :-> c) -> (a :-> d) -> (a :-> c :* d)
#ifdef Simplify
Fst &&& Snd = Id
#endif
f &&& g = f :&&& g

(***) :: HasTy4 a b c d => (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
f *** g = f @. Fst &&& g @. Snd

first :: HasTy3 a b c => (a :-> c) -> (a :* b :-> c :* b)
first f = f *** Id

second :: HasTy3 a b d => (b :-> d) -> (a :* b :-> a :* d)
second g = Id *** g

(|||) :: HasTy3 a b c => (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
(|||) = (:|||)

(+++) :: HasTy4 a b c d => (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
f +++ g = Lft @. f ||| Rht @. g

left :: HasTy3 a b c => (a :-> c) -> (a :+ b :-> c :+ b)
left f = f +++ Id

right :: HasTy3 a b d => (b :-> d) -> (a :+ b :-> a :+ d)
right g = Id +++ g

instance Show (a :-> b) where
#ifdef ShowFolded
  showsPrec p (f :. Fst :&&& g :. Snd) = showsOp2'  "***" (3,AssocRight) p f g
  showsPrec p (Lft :. f :||| Rht :. g) = showsOp2'  "+++" (2,AssocRight) p f g
  showsPrec _ (Id :&&& Id)             = showString "dup"
  showsPrec _ (Id :||| Id)             = showString "jam"
  showsPrec _ (Snd :&&& Fst)           = showString "swapP"
  showsPrec _ (Rht :&&& Lft)           = showString "swapC"
  showsPrec p (f :. Fst :&&& Snd)      = showsApp1  "first"  p f
  showsPrec p (Fst :&&& g :. Snd)      = showsApp1  "second" p g
  showsPrec p (Lft :. f :||| Rht)      = showsApp1  "left"   p f
  showsPrec p (Lft :||| Rht :. g)      = showsApp1  "right"  p g
#endif
  showsPrec _ Id          = showString "id"
  showsPrec p (g :. f)    = showsOp2'  "."  (9,AssocRight) p g f
  showsPrec p (Prim x)    = showsPrec p x
                            -- or: showsApp1 "prim" p x
  showsPrec p (Konst b)   = showsApp1 "konst" p b
  showsPrec p (f :&&& g)  = showsOp2' "&&&" (3,AssocRight) p f g
  showsPrec p (f :||| g)  = showsOp2' "|||" (2,AssocRight) p f g
  showsPrec _ Fst         = showString "fst"
  showsPrec _ Snd         = showString "snd"
  showsPrec _ Lft         = showString "lft"
  showsPrec _ Rht         = showString "rht"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry   f) = showsApp1  "curry"   p f
  showsPrec p (Uncurry h) = showsApp1  "uncurry" p h
