{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- Whether to use trees instead of vectors.
-- Restricts to power-of-two, and gives fast fold for dot.
#define UseTrees

module LambdaCCC.Examples.Linear where

import Prelude hiding (sum)
import Data.Foldable (Foldable(..),sum)
import Data.Traversable (sequenceA)
import Control.Applicative (Applicative,liftA2)

import TypeUnary.Nat
#ifdef UseTrees
import Circat.RTree
#else
import TypeUnary.Vec hiding (transpose)
#endif

infixl 7 <.>

#ifdef UseTrees
type V = Tree
#else
type V = Vec
#endif

-- | Dot product, i.e., sum of products.
(<.>) :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u <.> v = sum (liftA2 (*) u v)
{-# INLINE (<.>) #-}

-- (<.>) :: (IsNat n, Num a) => V n a -> V n a -> a
-- u <.> v = sum (u * v)

-- | Linear map from a^m to a^n: Matrix with n rows and m columns
type Lin m n a = V n (V m a)

-- | Apply a linear map: dot each row of p with v
apply :: (IsNat m, Num a) => Lin m n a -> V m a -> V n a
apply p v = fmap (<.> v) p
{-# INLINE apply #-}

-- | Matrix transpose. Specialization of 'sequenceA' from Traversable.
transpose :: IsNat m => Lin m n a -> Lin n m a
transpose = sequenceA

infixr 9 @.

-- | Compose linear transformations.
-- p-transform each column of q to get columns of composition.
(@.) :: (IsNat m, IsNat n, IsNat o, Num a) =>
        Lin n o a -> Lin m n  a -> Lin m o a
p @. q = transpose (fmap (apply p) (transpose q))
{-# INLINE (@.) #-}

-- Efficiency note: all mappings and transpositions are compiled away.

-- From TypeUnary.Vec, we get the Vec type, IsNat constraint, pointwise
-- multiplication, and Traversable instance (used by transpose).
