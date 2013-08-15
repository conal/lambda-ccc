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
  , (@.), applyE, curryE, uncurryE
  , prim, condC, condPair                     -- TODO: use condC instead
  , (&&&), (***), (+++), (|||)
  , twiceP, twiceC
  , dup, jam, swapP, swapC
  , first, second, left, right
  , cccTys
  ) where

import qualified Control.Arrow as A
-- import Control.Applicative (liftA3)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc (Unop,Evalable(..),(:*),(:+),(:=>))
import LambdaCCC.ShowUtils (showsApp1,showsOp2',Assoc(..))
import LambdaCCC.Ty
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
  Id      :: HasTy a => a :-> a
  (:.)    :: HasTy3 a b c => (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Primitives
  Prim    :: HasTy2 a b => Prim (a -> b) -> (a :-> b)
  -- Products
  Fst     :: HasTy2 (a :* b) a => a :* b :-> a
  Snd     :: HasTy2 (a :* b) b => a :* b :-> b
  (:&&&)  :: HasTy3 a b c => (a :-> b) -> (a :-> c) -> (a :-> b :* c)
  -- Coproducts
  Lft     :: HasTy2 a b => a :-> a :+ b
  Rht     :: HasTy2 a b => b :-> a :+ b
  (:|||)  :: HasTy3 a b c => (b :-> a) -> (c :-> a) -> (b :+ c :-> a)
  -- Exponentials
  Apply   :: HasTy2 a b   => (a :=> b) :* a :-> b
  Curry   :: HasTy3 a b c => (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry :: HasTy3 a b c => (a :-> (b :=> c)) -> (a :* b :-> c)

instance IsTy2 (:->) where
  type IsTy2Constraint (:->) u v = HasTy2 u v
  tyEq2 = tyEq2'

instance HasTy2 a b => Eq (a :-> b) where
  Id         == Id                                     = True
  (g :. f)   == (g' :. f') | Just Refl <- f `tyEq2` f' = g == g'
  Prim p     == Prim p'                                = p == p'
  Fst        == Fst                                    = True
  Snd        == Snd                                    = True
  (f :&&& g) == (f' :&&& g')                           = f == f' && g == g'
  Lft        == Lft                                    = True
  Rht        == Rht                                    = True
  (f :||| g) == (f' :||| g')                           = f == f' && g == g'
  Apply      == Apply                                  = True
  Curry h    == Curry h'                               = h == h'
  Uncurry k  == Uncurry k'                             = k == k'
  _          == _                                      = False

-- TODO: The type constraints prevent (:->) from being a category etc without
-- some change to those classes, e.g., with instance-specific constraints via
-- ConstraintKinds.

typ2 :: HasTy2 a b => (Ty a, Ty b)
typ2 = (typ,typ)

cccTys :: (a :-> b) -> (Ty a, Ty b)
cccTys Id      {} = typ2
cccTys (:.)    {} = typ2
cccTys Prim    {} = typ2
cccTys Fst     {} = typ2
cccTys Snd     {} = typ2
cccTys (:&&&)  {} = typ2
cccTys Lft     {} = typ2
cccTys Rht     {} = typ2
cccTys (:|||)  {} = typ2
cccTys Apply   {} = typ2
cccTys Curry   {} = typ2
cccTys Uncurry {} = typ2
-- cccTys Cond    {} = typ2

-- Maybe parametrize this GADT by a constraint. Sadly, I'd lose the pretty infix
-- syntax ("a :-> b").

instance Evalable (a :-> b) where
  type ValT (a :-> b) = a :=> b
  eval Id           = id
  eval (g :. f)     = eval g . eval f
  eval (Prim p)     = eval p
  eval Fst          = fst
  eval Snd          = snd
  eval (f :&&& g)   = eval f A.&&& eval g
  eval Lft          = Left
  eval Rht          = Right
  eval (f :||| g)   = eval f A.||| eval g
  eval Apply        = uncurry ($)
  eval (Curry   h)  = curry   (eval h)
  eval (Uncurry f)  = uncurry (eval f)
--   eval (Cond f)     = cond . eval f

{--------------------------------------------------------------------
    Smart constructors
--------------------------------------------------------------------}

prim :: HasTy2 a b => Prim (a -> b) -> (a :-> b)
prim FstP = Fst
prim SndP = Snd
prim p    = Prim p

-- The FstP and SndP cases don't type-check with my old constraints on those
-- constructors.
-- Consider FstP :: Prim (u :* v -> u), so that a = u :* v and b = u.
-- I know HasTy (u :* v), but I need HasTy u and HasTy v for Fst.

infixr 9 @.
-- | Optimizing morphism composition
(@.) :: HasTy3 a b c => (b :-> c) -> (a :-> b) -> (a :-> c)
#ifdef Simplify
Id      @. f  = f
g       @. Id = g
Prim (ConstP p) @. _  = prim (ConstP p)
Apply   @. (decompL -> g :. f) = composeApply g @. f
(h :. g) @. f = h @. (g @. f) -- reduce parens
#endif
g       @. f  = g :. f

--  Apply    :: HasTy2 a b   => ((a :=> b) :* a) :-> b

-- | @'composeApply' h == 'apply' . h@
composeApply :: HasTy3 a b z => (z :-> (a :=> b) :* a) -> (z :-> b)
composeApply (Prim (ConstP p)          :&&& f) = prim p @. f
composeApply (h@Prim{} :. f    :&&& g) = Uncurry h @. (f  &&& g)
composeApply (h@Prim{}         :&&& g) = Uncurry h @. (Id &&& g)
-- apply . (curry (g . snd) &&& f) == g . f
composeApply (Curry (decompR -> g :. Snd) :&&& f) = g @. f
-- apply . (curry h . f &&& g) == h . (f &&& g)
composeApply ((decompL -> (Curry h :. f)) :&&& g) = h @. (f &&& g)
-- apply . first f == uncurry f  -- see proof below
composeApply (f :. Fst :&&& Snd) = uncurryE f
composeApply h = Apply :. h

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
-- Experimental: const a &&& const b == const (a,b)
-- Prim (ConstP (LitP a)) &&& Prim (ConstP (LitP b)) = Prim (ConstP (LitP (a,b)))
Fst &&& Snd = Id
-- f . r &&& g . r == (f &&& g) . r
(decompR -> f :. r) &&& (decompR -> g :. (tyEq2 r -> Just Refl)) =
  (f &&& g) @. r
#endif
f &&& g = f :&&& g

(***) :: HasTy4 a b c d => (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
f *** g = f @. Fst &&& g @. Snd

twiceP :: HasTy2 a   c   => (a :-> c)              -> (a :* a :-> c :* c)
twiceP f = f *** f

first :: HasTy3 a b c => (a :-> c) -> (a :* b :-> c :* b)
first f = f *** Id

second :: HasTy3 a b d => (b :-> d) -> (a :* b :-> a :* d)
second g = Id *** g

(|||) :: HasTy3 a b c => (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
(|||) = (:|||)

(+++) :: HasTy4 a b c d => (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
f +++ g = Lft @. f ||| Rht @. g

twiceC :: HasTy2 a   c   => (a :-> c)              -> (a :+ a :-> c :+ c)
twiceC f = f +++ f

left :: HasTy3 a b c => (a :-> c) -> (a :+ b :-> c :+ b)
left f = f +++ Id

right :: HasTy3 a b d => (b :-> d) -> (a :+ b :-> a :+ d)
right g = Id +++ g

applyE :: HasTy2 a b   => ((a :=> b) :* a) :-> b
applyE = Apply

curryE :: HasTy3 a b c => (a :* b :-> c) -> (a :-> (b :=> c))
#ifdef Simplify
curryE (Prim p :. Snd) = prim (ConstP p)   -- FIX: not general enough
-- curry (apply . (f . fst &&& snd)) == f  -- Proof below
curryE (Apply :. (f :. Fst :&&& Snd)) = f
#endif
curryE h = Curry h

-- curry/apply proof:
-- 
--   curry (apply . (f . fst &&& snd))
-- == curry (apply . (f . fst &&& id . snd))
-- == curry (apply . (f *** id))
-- == curry (apply . first f)
-- == curry (\ (a,b) -> apply (first f (a,b)))
-- == curry (\ (a,b) -> apply (f a,b))
-- == curry (\ (a,b) -> f a b)
-- == f

uncurryE :: HasTy3 a b c => (a :-> (b :=> c)) -> (a :* b :-> c)
uncurryE = Uncurry

-- Conditional. Breaks down pairs
condC :: forall a. HasTy a => Bool :* (a :* a) :-> a
condC = cond' (typ :: Ty a)
 where
   cond' (u :* v) | HasTy <- tyHasTy u, HasTy <- tyHasTy v
           = condPair
   cond' _ = Prim CondP

-- TODO: Move this smarts into the smart prim constructor.

condPair :: HasTy2 a b =>
            Bool :* ((a :* b) :* (a :* b)) :-> (a :* b)
condPair = half Fst &&& half Snd
 where
   half f = condC @. second (twiceP f)

-- condPair = condC @. second (twiceP Fst) &&& condC @. second (twiceP Snd)

-- TODO: Rewrite condC,cond',condPair more prettily

{--------------------------------------------------------------------
    Factoring (decomposition)
--------------------------------------------------------------------}

#ifdef Simplify

-- | Decompose into @g . f@, where @g@ is as small as possible, but not 'Id'.
decompL :: HasTy2 a c => Unop (a :-> c)
decompL Id                         = Id
decompL ((decompL -> h :. g) :. f) = h @. (g @. f)
decompL comp@(_ :. _)              = comp
decompL f                          = f :. Id

-- | Decompose into @g . f@, where @f@ is as small as possible, but not 'Id'.
decompR :: HasTy2 a c => Unop (a :-> c)
decompR Id                         = Id
decompR (h :. (decompR -> g :. f)) = (h @. g) @. f
decompR comp@(_ :. _)              = comp
decompR f                          = Id :. f

#endif

{--------------------------------------------------------------------
    Show
--------------------------------------------------------------------}

instance Show (a :-> b) where
#ifdef Sugared
  -- showsPrec p (f :. Fst :&&& g :. Snd) = showsOp2'  "***" (3,AssocRight) p f g
  showsPrec p (f :. Fst :&&& g :. Snd)
    | Just Refl <- f `tyEq2` g = showsApp1 "twiceP" p f
    | otherwise                = showsOp2'  "***" (3,AssocRight) p f g
  -- showsPrec p (Lft :. f :||| Rht :. g) = showsOp2'  "+++" (2,AssocRight) p f g
  showsPrec p (f :. Fst :||| g :. Snd)
    | Just Refl <- f `tyEq2` g = showsApp1 "twiceC" p f
    | otherwise                = showsOp2'  "+++" (2,AssocRight) p f g
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
  showsPrec p (f :&&& g)  = showsOp2' "&&&" (3,AssocRight) p f g
  showsPrec p (f :||| g)  = showsOp2' "|||" (2,AssocRight) p f g
  showsPrec _ Fst         = showString "fst"
  showsPrec _ Snd         = showString "snd"
  showsPrec _ Lft         = showString "lft"
  showsPrec _ Rht         = showString "rht"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry   f) = showsApp1  "curry"   p f
  showsPrec p (Uncurry h) = showsApp1  "uncurry" p h
--   showsPrec p (Cond f)    = showsApp1  "cond"    p f
