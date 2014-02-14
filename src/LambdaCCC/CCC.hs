{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures, CPP #-}
{-# LANGUAGE PatternGuards, ViewPatterns, ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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
  , (:->)(..)
  , (@.), applyE, curryE, uncurryE      -- TODO: "E" --> "C"
  , prim
  , (&&&), (***), (+++), (|||)
  , twiceP, twiceC
  , dup, jam, swapP, swapC
  , first, second, left, right, distl
  ) where

import qualified Control.Arrow as A
-- import Control.Applicative (liftA3)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc (Unop,Evalable(..),(:*),(:+),(:=>),Eq1'(..),Eq2'(..),unsafeEq2)
import LambdaCCC.ShowUtils (showsApp1,showsOp2',Assoc(..))
-- import LambdaCCC.Ty
import LambdaCCC.Prim (Prim(..)) -- ,cond,ifThenElse

infix  0 :->
infixr 3 &&&, ***
infixr 2 |||, +++
infixr 9 :.

infixr 3 :&&&
infixr 2 :|||

-- Whether to introduce defined operations like (***) during show
#define Sugared

-- Whether to simplify during construction
#define Simplify

-- | CCC combinator expressions. Although we use standard Haskell unit,
-- cartesian product, sums, and function types here, the intended interpretation
-- is as the categorical counterparts (terminal object, categorical products,
-- coproducts, and exponentials).
data (:->) :: * -> * -> * where
  Id      :: a :-> a
  (:.)    :: (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Products
  Exl     :: a :* b :-> a
  Exr     :: a :* b :-> b
  (:&&&)  :: (a :-> b) -> (a :-> c) -> (a :-> b :* c)
  -- Coproducts
  Inl     :: a :-> a :+ b
  Inr     :: b :-> a :+ b
  (:|||)  :: (b :-> a) -> (c :-> a) -> (b :+ c :-> a)
  DistL   :: a :* (b :+ c) :-> a :* b :+ a :* c
  -- Exponentials
  Apply   :: (a :=> b) :* a :-> b
  Curry   :: (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry :: (a :-> (b :=> c)) -> (a :* b :-> c)
  -- Primitives
  Prim    :: Prim (a -> b) -> (a :-> b)
  Const   :: Prim       b  -> (a :-> b)

-- TODO: Do we really need both Prim and Const?

-- TODO: Try to make instances for the Category subclasses, so we don't need
-- separate terminology. Then eliminate dup, jam, etc.

instance Eq2' (:->) where
  Id         ==== Id           = True
  (g :. f)   ==== (g' :. f')   = g ==== g' && f ==== f'
  Exl        ==== Exl          = True
  Exr        ==== Exr          = True
  (f :&&& g) ==== (f' :&&& g') = f ==== f' && g ==== g'
  Inl        ==== Inl          = True
  Inr        ==== Inr          = True
  (f :||| g) ==== (f' :||| g') = f ==== f' && g ==== g'
  DistL      ==== DistL        = True
  Apply      ==== Apply        = True
  Curry h    ==== Curry h'     = h ==== h'
  Uncurry k  ==== Uncurry k'   = k ==== k'
  Prim  p    ==== Prim  p'     = p === p'
  Const p    ==== Const p'     = p === p'
  _          ==== _            = False

instance Eq (a :-> b) where (==) = (====)


-- WARNING: take care with the (==) definition above. When we add constructors
-- to the GADT, we won't get a non-exhaustive cases warning, since the last case
-- is catch-all.

-- TODO: The type constraints prevent (:->) from being a category etc without
-- some change to those classes, e.g., with instance-specific constraints via
-- ConstraintKinds.

-- Maybe parametrize this GADT by a constraint. Sadly, I'd lose the pretty infix
-- syntax ("a :-> b").

-- Homomorphic evaluation
instance Evalable (a :-> b) where
  type ValT (a :-> b) = a :=> b
  eval Id           = id
  eval (g :. f)     = eval g . eval f
  eval (Prim p)     = eval p
  eval (Const p)    = const (eval p)
  eval Exl          = fst
  eval Exr          = snd
  eval (f :&&& g)   = eval f A.&&& eval g
  eval Inl          = Left
  eval Inr          = Right
  eval (f :||| g)   = eval f A.||| eval g
  eval DistL        = distlF
  eval Apply        = uncurry ($)
  eval (Curry   h)  = curry   (eval h)
  eval (Uncurry f)  = uncurry (eval f)

distlF :: a :* (b :+ c) -> a :* b :+ a :* c
distlF (a, Left  b) = Left  (a,b)
distlF (a, Right c) = Right (a,c)


{--------------------------------------------------------------------
    Smart constructors
--------------------------------------------------------------------}

prim :: Prim (a -> b) -> (a :-> b)
prim ExlP = Exl
prim ExrP = Exr
prim InlP = Inl
prim InrP = Inr
prim p    = Prim p

infixr 9 @.
-- | Optimizing morphism composition
(@.) :: (b :-> c) -> (a :-> b) -> (a :-> c)
#ifdef Simplify
Id         @. f                   = f
g          @. Id                  = g
(h :. g)   @. f                   = h @. (g @. f)
Exl        @. (f :&&& _)          = f
Exr        @. (_ :&&& g)          = g
(f :||| _) @. Inl                 = f
(_ :||| g) @. Inr                 = g
Const p    @. _                   = Const p
Apply      @. (decompL -> g :. f) = composeApply g @. f
#endif
g          @. f                   = g :. f

--  Apply    :: ((a :=> b) :* a) :-> b

#ifdef Simplify

-- | @'composeApply' h == 'apply' . h@
composeApply :: (z :-> (a :=> b) :* a) -> (z :-> b)
composeApply (Const p :&&& f) = prim p @. f
-- apply . (curry h . f &&& g) == h . (f &&& g)
composeApply ((decompL -> (Curry h :. f)) :&&& g) = h @. (f &&& g)
composeApply (h@Prim{} :. f    :&&& g) = uncurryE h @. (f  &&& g)
composeApply (h@Prim{}         :&&& g) = uncurryE h @. (Id &&& g)
-- apply . (curry (g . exr) &&& f) == g . f
composeApply (Curry (decompR -> g :. Exr) :&&& f) = g @. f
-- apply . first f == uncurry f  -- see proof below
composeApply (f :. Exl :&&& Exr) = uncurryE f
composeApply h = Apply :. h

#endif

{-
  apply . first f
== \ p -> apply (first f p)
== \ (a,b) -> apply (first f (a,b))
== \ (a,b) -> apply (f a, b)
== \ (a,b) -> f a b
== uncurry f
-}

-- Note: the Prim{} specialization is unnecessary for validity but I suspect
-- useful for introducing just the uncurryings we want. TODO: verify.
--
-- Note: the second Uncurry specializes the first one, but is needed for
-- syntactic matching.

dup :: a :-> a :* a
dup = Id &&& Id

jam :: a :+ a :-> a
jam = Id ||| Id

-- | Product swap
swapP :: a :* b :-> b :* a
swapP = Exr &&& Exl

-- | Coproduct swap
swapC :: a :+ b :-> b :+ a
swapC = Inr ||| Inl

(&&&) :: (a :-> c) -> (a :-> d) -> (a :-> c :* d)
#ifdef Simplify
-- Experimental: const a &&& const b == const (a,b)
-- Prim (ConstP (LitP a)) &&& Prim (ConstP (LitP b)) = Prim (ConstP (LitP (a,b)))
Exl &&& Exr = Id
-- f . r &&& g . r == (f &&& g) . r
(decompR -> f :. r) &&& (decompR -> g :. r') | Just Refl <- r `unsafeEq2` r'
                                             = (f &&& g) @. r
#endif
f &&& g = f :&&& g

(***) :: (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
f *** g = f @. Exl &&& g @. Exr

twiceP :: (a :-> c)              -> (a :* a :-> c :* c)
twiceP f = f *** f

first :: (a :-> c) -> (a :* b :-> c :* b)
first f = f *** Id

second :: (b :-> d) -> (a :* b :-> a :* d)
second g = Id *** g

(|||) :: (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
(|||) = (:|||)

(+++) :: (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
f +++ g = Inl @. f ||| Inr @. g

twiceC :: (a :-> c)              -> (a :+ a :-> c :+ c)
twiceC f = f +++ f

left :: (a :-> c) -> (a :+ b :-> c :+ b)
left f = f +++ Id

right :: (b :-> d) -> (a :+ b :-> a :+ d)
right g = Id +++ g

distl :: a :* (b :+ c) :-> a :* b :+ a :* c
distl = DistL

applyE :: ((a :=> b) :* a) :-> b
applyE = Apply

curryE :: (a :* b :-> c) -> (a :-> (b :=> c))
#ifdef Simplify
curryE (Uncurry h) = h
curryE (Prim p :. Exr) = Const p   -- FIX: not general enough
-- curry (apply . (f . exl &&& exr)) == f  -- Proof below
-- curryE (Apply :. (f :. Exl :&&& Exr)) = f
#endif
curryE h = Curry h

-- curry/apply proof:
-- 
--   curry (apply . (f . exl &&& exr))
-- == curry (apply . (f . exl &&& id . exr))
-- == curry (apply . (f *** id))
-- == curry (apply . first f)
-- == curry (\ (a,b) -> apply (first f (a,b)))
-- == curry (\ (a,b) -> apply (f a,b))
-- == curry (\ (a,b) -> f a b)
-- == f

-- I commented out this rule. I don't think it'll ever fire, considering
-- composeApply.

uncurryE :: (a :-> (b :=> c)) -> (a :* b :-> c)
#ifdef Simplify
uncurryE (Curry f)    = f
uncurryE (Prim PairP) = Id
#endif
uncurryE x = Uncurry x

{--------------------------------------------------------------------
    Factoring (decomposition)
--------------------------------------------------------------------}

#if defined Simplify || defined Sugared

-- | Decompose into @g . f@, where @g@ is as small as possible, but not 'Id'.
decompL :: Unop (a :-> c)
decompL Id                         = Id
decompL ((decompL -> h :. g) :. f) = h :. (g @. f)
decompL comp@(_ :. _)              = comp
decompL f                          = f :. Id

-- | Decompose into @g . f@, where @f@ is as small as possible, but not 'Id'.
decompR :: Unop (a :-> c)
decompR Id                         = Id
decompR (h :. (decompR -> g :. f)) = (h @. g) :. f
decompR comp@(_ :. _)              = comp
decompR f                          = Id :. f

#endif

{--------------------------------------------------------------------
    Show
--------------------------------------------------------------------}

instance Show (a :-> b) where
#ifdef Sugared
  showsPrec _ (Id  :&&& Id )   = showString "dup"
  showsPrec _ (Exr :&&& Exl)   = showString "swapP"
  showsPrec p ((decompR -> f :. Exl) :&&& (decompR -> g :. Exr))
    | Id        <- g           = showsApp1 "first"  p f
    | Id        <- f           = showsApp1 "second" p g
    | f ==== g                 = showsApp1 "twiceP" p f
    | otherwise                = showsOp2'  "***" (3,AssocRight) p f g
  showsPrec _ (Id  :||| Id )   = showString "jam"
  showsPrec _ (Inr :||| Inl)   = showString "swapC"
  showsPrec p (f :. Exl :||| g :. Exr)
    | Id        <- g           = showsApp1 "left"  p f
    | Id        <- f           = showsApp1 "right" p g
    | f ==== g                 = showsApp1 "twiceC" p f
    | otherwise                = showsOp2'  "+++" (2,AssocRight) p f g
#endif
  showsPrec _ Id          = showString "id"
  showsPrec p (g :. f)    = showsOp2'  "."  (9,AssocRight) p g f
  showsPrec _ Exl         = showString "exl"
  showsPrec _ Exr         = showString "exr"
  showsPrec p (f :&&& g)  = showsOp2' "&&&" (3,AssocRight) p f g
  showsPrec _ Inl         = showString "inl"
  showsPrec _ Inr         = showString "inr"
  showsPrec p (f :||| g)  = showsOp2' "|||" (2,AssocRight) p f g
  showsPrec _ DistL       = showString "distl"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry   f) = showsApp1  "curry"   p f
  showsPrec p (Uncurry h) = showsApp1  "uncurry" p h
  showsPrec p (Prim x)    = showsPrec p x
                            -- or: showsApp1 "prim" p x
  showsPrec p (Const w)   = showsApp1 "const" p w
