{-# OPTIONS_GHC -Wall #-}

module LambdaCCC.Examples.Linear where

import Prelude hiding (sum)
import Data.Foldable (sum)
import Data.Traversable (sequenceA)

import TypeUnary.Vec hiding (transpose)

infixl 7 <.>

-- | Dot product, i.e., sum of products.
(<.>) :: (IsNat n, Num a) => Vec n a -> Vec n a -> a
u <.> v = sum (u * v)
{-# INLINE (<.>) #-}

-- | Linear map from a^m to a^n: Matrix with n rows and m columns
type Lin m n a = Vec n (Vec m a)

-- | Apply a linear map: dot each row of p with v
apply :: (IsNat m, Num a) => Lin m n a -> Vec m a -> Vec n a
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
