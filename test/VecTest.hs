{-# LANGUAGE CPP #-}

-- #define CopyOfVec

#ifdef CopyOfVec
-- For copied Vec code. Remove later.
{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeOperators
           , GADTs, KindSignatures, TupleSections
           , FlexibleInstances, FlexibleContexts
           , UndecidableInstances
           , ScopedTypeVariables, CPP
           , RankNTypes
           , MultiParamTypeClasses, FunctionalDependencies
           , DeriveDataTypeable
  #-}
#endif
{-# LANGUAGE ExplicitForAll #-}  -- For :< experiment

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  VecTest
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed vectors. To run:
-- 
--   hermit VecTest.hs -v0 -opt=LambdaCCC.Reify DoVec.hss
--   
----------------------------------------------------------------------

module VecTest where

-- TODO: explicit exports

import Prelude hiding (foldr,sum)

import Control.Applicative (Applicative,liftA2)

import Data.Foldable (Foldable(..),sum)

#ifdef CopyOfVec
import TypeUnary.Nat
#else
import TypeUnary.Vec
#endif
-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import LambdaCCC.Lambda (EP,reifyEP)

import LambdaCCC.Prim (Prim(VecSP))  -- TEMP

import Circat.Classes (VecCat(..))
import LambdaCCC.Misc (Unop)

#ifdef CopyOfVec

{--------------------------------------------------------------------
    Copied from TypeUnary.Vec to try getting $W:< to fold.
    Remove later.
--------------------------------------------------------------------}

infixr 5 :<

-- | Vectors with type-determined length, having empty vector ('ZVec') and
-- vector cons ('(:<)').
data Vec :: * -> * -> * where
  ZVec :: Vec Z a 
  (:<) :: a -> Vec n a -> Vec (S n) a


infixl 1 <+>
-- | Concatenation of vectors
(<+>) :: Vec m a -> Vec n a -> Vec (m :+: n) a
ZVec     <+> v = v
(a :< u) <+> v = a :< (u <+> v)
{-# INLINE (<+>) #-}

instance Functor (Vec n) where
  fmap _ ZVec     = ZVec
  fmap f (a :< u) = f a :< fmap f u
  {-# INLINE fmap #-}

instance Foldable (Vec n) where
  foldr _  b ZVec     = b
  foldr h b (a :< as) = a `h` foldr h b as
  {-# INLINE foldr #-}

#endif

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- z :: EP (Vec Z Bool)
-- z = reifyEP ZVec

v3 :: Vec N3 Bool
v3 = True :< False :< True :< ZVec

v3' :: Vec N3 Bool
v3' = ZVec <+> v3

v6 :: Vec N6 Bool
v6 = v3 <+> v3

m3 :: Unop (Vec N3 Bool)
m3 = fmap not

f3 :: Vec N3 Bool -> Bool
f3 = foldr (||) True

-- Dot product

square :: (Functor f, Num a) => f a -> f a
square = fmap (\ x -> x * x)

dot :: (Applicative f, Foldable f, Num a) => f a -> f a -> a
dot as bs = sum (liftA2 (*) as bs)

s1 :: Unop (Vec N2 Int)
s1 = square

d1 :: Vec N2 Int -> Vec N2 Int -> Int
d1 = dot

-- TODO: Use the `Num` interface for even simpler formulations, including `dot
-- as bs = sum (as * bs)` and `square a = a * a`.

boo :: forall n a. a -> Vec n a -> Vec (S n) a
boo = (:<)

foo :: forall n a. Prim (a -> Vec n a -> Vec (S n) a)
foo = VecSP

