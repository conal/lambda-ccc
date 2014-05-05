{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures, CPP #-}
{-# LANGUAGE PatternGuards, ViewPatterns, ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}   -- for Int1 hack
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

-- Whether to introduce defined operations like (***) during show
#define Sugared

-- Whether to simplify during construction
#define Simplify

module LambdaCCC.CCC
  ( module LambdaCCC.Misc
  , (:->)(..), prim
  , convertC
  ) where

import Prelude hiding (id,(.),not,and,or,curry,uncurry,const)
-- import qualified Control.Arrow as A
-- import Control.Applicative (liftA3)

#ifdef Simplify
-- import Data.IsTy
import Data.Proof.EQ
#endif

-- import TypeUnary.Vec (Vec(..))

import LambdaCCC.Misc (Unop,Evalable(..),Unit,(:*),(:+),(:=>),Eq'(..),(==?))
import LambdaCCC.ShowUtils (showsApp1,showsOp2',Assoc(..))
-- import LambdaCCC.Ty
import LambdaCCC.Prim (Prim(..),Lit(..)) -- ,cond,ifThenElse

-- import TypeEncode.Encode (EncodeCat(..))

import Circat.Category
import Circat.Classes
import Circat.Pair  (PairCat(..))
import Circat.RTree (TreeCat(..))

infix  0 :->

infixr 3 :&&&
infixr 2 :|||

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
  It      :: a :-> Unit
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
  ConstU  :: Prim a -> (Unit :-> a)

-- TODO: Maybe specialize a to Unit in the type of Lit

-- TODO: Try to make instances for the Category subclasses, so we don't need
-- separate terminology. Then eliminate dup, jam, etc.

instance Eq' (a :-> b) (c :-> d) where
  Id         === Id           = True
  (g :. f)   === (g' :. f')   = g === g' && f === f'
  Exl        === Exl          = True
  Exr        === Exr          = True
  (f :&&& g) === (f' :&&& g') = f === f' && g === g'
  Inl        === Inl          = True
  Inr        === Inr          = True
  (f :||| g) === (f' :||| g') = f === f' && g === g'
  DistL      === DistL        = True
  Apply      === Apply        = True
  Curry h    === Curry h'     = h === h'
  Uncurry k  === Uncurry k'   = k === k'
  ConstU p   === ConstU p'    = p === p'
  _          === _            = False

instance Eq (a :-> b) where (==) = (===)


-- WARNING: take care with the (==) definition above. When we add constructors
-- to the GADT, we won't get a non-exhaustive cases warning, since the last case
-- is catch-all.

-- TODO: The type constraints prevent (:->) from being a category etc without
-- some change to those classes, e.g., with instance-specific constraints via
-- ConstraintKinds.

-- Maybe parametrize this GADT by a constraint. Sadly, I'd lose the pretty infix
-- syntax ("a :-> b").

-- Homomorphic evaluation
#if 0

distlF :: a :* (b :+ c) -> a :* b :+ a :* c
distlF (a, Left  b) = Left  (a,b)
distlF (a, Right c) = Right (a,c)

instance Evalable (a :-> b) where
  type ValT (a :-> b) = a :=> b
  eval Id          = id
  eval (g :. f)    = eval g . eval f
  eval (ConstU p)  = const (eval p)
  eval Exl         = fst
  eval Exr         = snd
  eval (f :&&& g)  = eval f A.&&& eval g
  eval Inl         = Left
  eval Inr         = Right
  eval (f :||| g)  = eval f A.||| eval g
  eval DistL       = distlF
  eval Apply       = uncurry ($)
  eval (Curry   h) = curry   (eval h)
  eval (Uncurry f) = uncurry (eval f)
#else
instance Evalable (a :-> b) where
  type ValT (a :-> b) = a -> b
  eval = convertC
#endif


{--------------------------------------------------------------------
    Smart constructors
--------------------------------------------------------------------}

prim :: Prim a -> (Unit :-> a)
prim ExlP = unitFun Exl
prim ExrP = unitFun Exr
prim InlP = unitFun Inl
prim InrP = unitFun Inr
prim p    = ConstU p

instance Category (:->) where
  id  = Id
  -- | Optimizing morphism composition
# ifdef Simplify
  Id         . f                   = f
  g          . Id                  = g
  (h :. g)   . f                   = h . (g . f)
  Exl        . (f :&&& _)          = f
  Exr        . (_ :&&& g)          = g
  It          . _                  = it
  (f :||| _) . Inl                 = f
  (_ :||| g) . Inr                 = g
  -- Important but occasionally leads to nontermination. Investigating.
  -- The simplest breaking example I have is `uncurry (&&)`.
--   Apply      . (decompL -> g :. f) = composeApply g . f
  -- Even the following simpler version trips nontermination.
--   Apply     . (decompL -> g :. f)  = (Apply :. g) . f
  Curry (decompR -> f :. Exr) . _  = curry (f . exr)  -- see below
# endif
  g          . f                   = g :. f


-- To prove:
-- 
--   curry (f . exr) . g == curry (f . exr)

#ifdef Simplify

-- | @'composeApply' h == 'apply' . h@
composeApply :: (z :-> (a :=> b) :* a) -> (z :-> b)
-- apply . (curry h . f &&& g) == h . (f &&& g)
composeApply ((decompL -> (Curry h :. f)) :&&& g) = h . (f &&& g)
composeApply (h@ConstU{} :. f    :&&& g) = uncurry h . (f  &&& g)
composeApply (h@ConstU{}         :&&& g) = uncurry h . (Id &&& g)
-- apply . (curry (g . exr) &&& f) == g . f
composeApply (Curry (decompR -> g :. Exr) :&&& f) = g . f
-- apply . first f == uncurry f  -- see proof below
composeApply (f :. Exl :&&& Exr) = uncurry f
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

-- Note: the ConstU{} specialization is unnecessary for validity but I suspect
-- useful for introducing just the uncurryings we want. TODO: verify.
--
-- Note: the second Uncurry specializes the first one, but is needed for
-- syntactic matching.

instance ProductCat (:->) where
  exl = Exl
  exr = Exr
# ifdef Simplify
  -- Experimental: const a &&& const b == const (a,b)
  -- ConstU (ConstP (LitP a)) &&& ConstU (ConstP (LitP b)) = ConstU (ConstP (LitP (a,b)))
  Exl &&& Exr = Id
  -- f . r &&& g . r == (f &&& g) . r
  (decompR -> f :. r) &&& (decompR -> g :. r') | Just Refl <- r ==? r'
                                               = (f &&& g) . r
# endif
  f &&& g = f :&&& g

instance TerminalCat (:->) where
  it = It

instance CoproductCat (:->) where
  inl   = Inl
  inr   = Inr
  (|||) = (:|||)                            -- no rewrites?

instance DistribCat (:->) where
  distl = DistL
  distr = (swapP +++ swapP) . distl . swapP -- maybe move to default.

instance ClosedCat (:->) where
  apply = Apply
# ifdef Simplify
  curry (Uncurry h) = h
  -- curry (apply . (f . exl &&& exr)) == f  -- Proof below
  -- curry (Apply :. (f :. Exl :&&& Exr)) = f
# endif
  curry h = Curry h
# ifdef Simplify
  uncurry (Curry f)    = f
--   uncurry (ConstU PairP) = Id             -- now ill-typed
# endif
  uncurry x = Uncurry x

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

{--------------------------------------------------------------------
    Factoring (decomposition)
--------------------------------------------------------------------}

#if defined Simplify

-- | Decompose into @g . f@, where @g@ is as small as possible, but not 'Id'.
-- Pattern matching against @_ :. _@ determines whether decomposition succeeded.
decompL :: Unop (a :-> c)
decompL Id                         = Id
decompL ((decompL -> h :. g) :. f) = h :. (g . f)
decompL comp@(_ :. _)              = comp
decompL f                          = f :. Id

#endif

#if defined Simplify || defined Sugared

-- | Decompose into @g . f@, where @f@ is as small as possible, but not 'Id'.
-- Pattern matching against @_ :. _@ determines whether decomposition succeeded.
decompR :: Unop (a :-> c)
decompR Id                         = Id
decompR (h :. (decompR -> g :. f)) = (h . g) :. f
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
    | Id <- g                  = showsApp1 "first"  p f
    | Id <- f                  = showsApp1 "second" p g
    | f === g                  = showsApp1 "twiceP" p f
    | otherwise                = showsOp2'  "***" (3,AssocRight) p f g
  showsPrec _ (Id  :||| Id )   = showString "jam"
  showsPrec _ (Inr :||| Inl)   = showString "swapC"
  showsPrec p ((decompR -> f :. Inl) :&&& (decompR -> g :. Inr))
    | Id <- g                  = showsApp1 "left"  p f
    | Id <- f                  = showsApp1 "right" p g
    | f === g                  = showsApp1 "twiceC" p f
    | otherwise                = showsOp2'  "+++" (2,AssocRight) p f g
#endif
  showsPrec _ Id          = showString "id"
  showsPrec p (g :. f)    = showsOp2'  "."  (9,AssocRight) p g f
  showsPrec _ Exl         = showString "exl"
  showsPrec _ Exr         = showString "exr"
  showsPrec p (f :&&& g)  = showsOp2'  "&&&" (3,AssocRight) p f g
  showsPrec _ It          = showString "it"
  showsPrec _ Inl         = showString "inl"
  showsPrec _ Inr         = showString "inr"
  showsPrec p (f :||| g)  = showsOp2'  "|||" (2,AssocRight) p f g
  showsPrec _ DistL       = showString "distl"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry   f) = showsApp1  "curry"   p f
  showsPrec p (Uncurry h) = showsApp1  "uncurry" p h
  showsPrec p (ConstU x)  = showsApp1  "const"   p x

-- -- | Category with boolean operations.
-- class ProductCat k => BoolCat k where
--   not :: Bool `k` Bool
--   and, or, xor :: (Bool :* Bool) `k` Bool

primFun :: Prim (a :=> b) -> (a :-> b)
primFun = unUnitFun . prim

primUnc :: Prim (a :=> b :=> c) -> (a :* b :-> c)
primUnc p = uncurry (primFun p)

instance VecCat (:->) where
  toVecZ = primFun ToVecZP
  unVecZ = primFun UnVecZP
  toVecS = primUnc VecSP
  unVecS = primFun UnVecSP

instance PairCat (:->) where
  toPair = primUnc UPairP
  unPair = primFun UnUPairP

instance TreeCat (:->) where
  toL = primFun ToLeafP
  unL = primFun UnLeafP
  toB = primFun ToBranchP
  unB = primFun UnBranchP

instance BoolCat (:->) where
  not = primFun NotP
  xor = primUnc XorP
  and = primUnc AndP
  or  = primUnc OrP

-- etc.

instance MuxCat (:->) where
  mux = primFun CondBP

instance NumCat (:->) Int where
  add = primUnc AddP
  mul = primUnc MulP

-- instance NumCat (:->) Int1 where
--   add = primUnc AddP
--   mul = primUnc MulP

-- TODO: reconcile curried vs uncurried, eliminating the conversions here.

{--------------------------------------------------------------------
    Experiment: convert to other CCC
--------------------------------------------------------------------}

convertC :: ( BiCCC k, HasUnitArrow k Lit
            , BoolCat k, MuxCat k, VecCat k, PairCat k, TreeCat k, NumCat k Int
            ) =>
            (a :-> b) -> (a `k` b)
convertC Id           = id
convertC (g :. f)     = convertC g . convertC f
convertC (ConstU p)   = unitArrow p . it
convertC Exl          = exl
convertC Exr          = exr
convertC (f :&&& g)   = convertC f &&& convertC g
convertC It           = it
convertC Inl          = inl
convertC Inr          = inr
convertC (f :||| g)   = convertC f ||| convertC g
convertC DistL        = distl
convertC Apply        = apply
convertC (Curry   h)  = curry   (convertC h)
convertC (Uncurry f)  = uncurry (convertC f)

instance HasUnitArrow (:->) Lit where unitArrow = ConstU . LitP

{--------------------------------------------------------------------
    TEMP
--------------------------------------------------------------------}

-- z :: Unit :-> (Bool -> Bool)
-- z = curry (not . exr) . it

