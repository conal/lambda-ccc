{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment
{-# LANGUAGE DataKinds #-}  -- for TU

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=38 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  TreeTest
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tests with length-typed treetors. To run:
-- 
--   hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTree.hss resume && ./TreeTest
--   
-- Remove the 'resume' to see intermediate Core.
----------------------------------------------------------------------

-- module TreeTest where

-- TODO: explicit exports

import Prelude hiding (foldr,sum,product)

import Data.Monoid (Monoid(..),Sum,Product)
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)
import Data.Foldable (Foldable(..),sum,product)
import Data.Traversable (Traversable(..))

-- transformers
import Data.Functor.Identity

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)
import TypeUnary.Vec hiding (transpose)

import LambdaCCC.Misc (Unop,Binop,transpose)

import Circat.Misc (Unop)
import Circat.Pair (Pair(..))
import qualified Circat.RTree as RTree
import qualified Circat.LTree as LTree
import qualified Circat.RaggedTree as Ragged
import Circat.RaggedTree (TU(..))
import Circat.Scan
import Circat.Circuit (GenBuses)

-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import LambdaCCC.Lambda (EP,reifyEP)

import LambdaCCC.Run (run) -- go

-- Experiment for Typeable resolution in reification
import qualified Data.Typeable

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type RTree = RTree.Tree
type LTree = LTree.Tree
type Ragged = Ragged.Tree

t0 :: RTree N0 Bool
t0 = pure True

p1 :: Unop (Pair Bool)
p1 (a :# b) = b :# a

psum :: Num a => Pair a -> a
psum (a :# b) = a + b

-- tsum :: Num a => RTree n a -> a
-- tsum = foldT id (+)

-- dot :: (IsNat n, Num a) => RTree n a -> RTree n a -> a
-- dot as bs = tsum (prod as bs)

prod :: (Functor f, Num a) => f (a,a) -> f a
prod = fmap (uncurry (*))

prodA :: (Applicative f, Num a) => Binop (f a)
prodA = liftA2 (*)

-- dot :: Num a => RTree n (a,a) -> a
-- dot = tsum . prod

dot :: (Functor f, Foldable f, Num a) => f (a,a) -> a
dot = sum . prod

square :: Num a => a -> a
square a = a * a

sumSquare :: (Functor f, Foldable f, Num a) => f a -> a
sumSquare = sum . fmap square

squares :: (Functor f, Num a) => f a -> f a
squares = fmap square

squares' :: (Functor f, Num a) => f a -> f a
squares' = fmap (^ (2 :: Int))

dot' :: (Applicative f, Foldable f, Num a) => f a -> f a -> a
dot' as bs = sum (prodA as bs)

dot'' :: (Foldable g, Functor g, Foldable f, Num a) => g (f a) -> a
dot'' = sum . fmap product

dot''' :: (Traversable g, Foldable f, Applicative f, Num a) => g (f a) -> a
dot''' = dot'' . transpose

dotap :: (Foldable t, Num (t a), Num a) => t a -> t a -> a
as `dotap` bs = sum (as * bs)

dotsp :: (Foldable g, Foldable f, Num (f a), Num a) => g (f a) -> a
dotsp = sum . product

cdot :: (Foldable f, Num (f a), Num a) => f a -> f a -> a
u `cdot` v = dotsp (u :# v)

-- | Monoid under lifted multiplication.
newtype ProductA f a = ProductA { getProductA :: f a }

instance (Applicative f, Num a) => Monoid (ProductA f a) where
  mempty = ProductA (pure 1)
  ProductA u `mappend` ProductA v = ProductA (liftA2 (*) u v)

productA :: (Foldable g, Applicative f, Num a) => g (f a) -> f a
productA = getProductA . foldMap ProductA

dota :: (Foldable g, Foldable f, Applicative f, Num a) => g (f a) -> a
dota = sum . productA

type Matrix m n a = Vec n (Vec m a)

type MatrixT m n a = RTree n (RTree m a)

infixr 1 $@
-- infixl 9 .@

-- | Apply a linear transformation represented as a matrix
-- ($@) :: (IsNat m, Num a) => Matrix m n a -> Vec m a -> Vec n a
($@) :: (Foldable m, Applicative m, Functor n, Num a) =>
        n (m a) -> m a -> n a
mat $@ vec = (`dot'` vec) <$> mat

-- -- | Compose linear transformations represented as matrices
-- (.@) :: (IsNat m, IsNat n, IsNat o, Num a) =>
--         Matrix n o a -> Matrix m n a -> Matrix m o a
(.@) :: ( Applicative o, Traversable n, Applicative n
        , Traversable m, Applicative m, Num a ) =>
        o (n a) -> n (m a) -> o (m a)
no .@ mn = transpose ((no $@) <$> transpose mn)

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

go :: GenBuses a => String -> (a -> b) -> IO ()
go name f = run name (reifyEP f)

-- Only works when compiled with HERMIT
main :: IO ()

-- main = go "map-v3" (fmap not :: Vec N3 Bool -> Vec N3 Bool)

-- main = go "tdott-2" (dot''' :: Pair (RTree N2 Int) -> Int)

-- main = go "dotsp-v3t2" (dotsp :: Vec N3 (RTree N2 Int) -> Int)

-- main = go "dotsp-t2t2" (dotsp :: RTree N2 (RTree N2 Int) -> Int)

-- main = go "dotsp-pt3" (dotsp :: Pair (RTree N3 Int) -> Int)

-- main = go "dotsp-plt3" (dotsp :: Pair (LTree N3 Int) -> Int)

-- main = go "dotap-2" (uncurry (dotap :: RTree N2 Int -> RTree N2 Int -> Int))

-- main = go "tdot-2" (dot'' :: RTree N2 (Pair Int) -> Int)

-- main = go "test" (dot'' :: RTree N4 (Pair Int) -> Int)

-- main = go "plusInt" ((+) :: Int -> Int -> Int)
-- main = go "or" ((||) :: Bool -> Bool -> Bool)

-- main = go "sum-p" (sum :: Pair Int -> Int)

-- main = go "sumSquare-p" (sumSquare :: Pair Int -> Int)

-- main = go "sumSquare-t3" (sumSquare :: RTree N3 Int -> Int)

-- main = go "sum-v2" (sum :: Vec N2 Int -> Int)

-- main = go "sum-t2" (sum :: RTree N2 Int -> Int)

-- main = go "sum-foldr-t4" (foldr (+) 0 :: RTree N4 Int -> Int)

-- main = go "sum-t3" (sum :: RTree N3 Int -> Int)

-- main = go "map-t3" (fmap not :: Unop (RTree N3 Bool))

-- main = go "test" (uncurry (dot' :: RTree N0 Int -> RTree N0 Int -> Int))

-- main = do go "squares3" (squares :: RTree N3 Int -> RTree N3 Int)
--           go "sum4"     (sum     :: RTree N4 Int -> Int)
--           go "dot4"     (dot     :: RTree N4 (Int,Int) -> Int)

-- Problematic examples:

-- -- This one leads to non-terminating CCC construction when the composeApply
-- -- optimization is in place.
-- main = go "dot1" (dot :: RTree N1 (Int,Int) -> Int)

-- main = go "test" (dot :: RTree N4 (Int,Int) -> Int)

-- main = go "transpose-pt4" (transpose :: Pair (RTree N4 Int) -> RTree N4 (Pair Int))

-- main = go "transpose-t4p" (transpose :: RTree N4 (Pair Int) -> Pair (RTree N4 Int))

-- main = go "vtranspose-34" (transpose :: Matrix N3 N4 Int -> Matrix N4 N3 Int)

-- main = go "vtranspose-34" (transpose :: Vec N3 (Vec N4 Int) -> Vec N4 (Vec N3 Int))

-- main = go "ttranspose-23" (transpose :: MatrixT N2 N3 Int -> MatrixT N3 N2 Int)

-- main = go "swap" (\ (a,b) -> (b,a) :: (Int,Bool))

-- main = go "add" (\ (a,b) -> a+b :: Int)

-- main = go "rot31" (\ (a,b,c) -> (b,c,a) :: (Bool,Bool,Bool))

-- main = go "rot41" (\ (a,b,c,d) -> (b,c,d,a) :: (Bool,Bool,Bool,Bool))

-- main = go "rev4" (\ (a,b,c,d) -> (d,c,b,a) :: (Bool,Bool,Bool,Bool))

-- main = go "sum-2" (\ (a,b) -> a+b :: Int)

-- main = go "sum-4a" ((\ (a,b,c,d) -> a+b+c+d) :: (Int,Int,Int,Int) -> Int)

-- main = go "sum-4b" ((\ (a,b,c,d) -> (a+b)+(c+d)) :: (Int,Int,Int,Int) -> Int)

-- main = go "dot-22" ((\ ((a,b),(c,d)) -> a*c + b*d) :: ((Int,Int),(Int,Int)) -> Int)

-- main = go "tdot-4" (dot :: RTree N4 (Int,Int) -> Int)

-- main = go "tpdot-4" (dot'' :: RTree N4 (Pair Int) -> Int)

-- -- Doesn't wedge.
-- main = go "dotp" ((psum . prod) :: Pair (Int,Int) -> Int)

-- main = go "prod1" (prod :: RTree N1 (Int,Int) -> RTree N1 Int)

-- main = go "dot5" (dot :: RTree N5 (Int,Int) -> Int)

-- main = go "squares1" (squares :: Unop (RTree N1 Int))

-- main = go "squares2" (squares :: Unop (RTree N2 Int))

-- main = go "squares0" (squares :: Unop (RTree N0 Int))

-- main = go "psum" (psum :: Pair Int -> Int)

-- main = go "tsum1" (tsum :: RTree N1 Int -> Int)

-- -- Not working yet: the (^) is problematic.
-- main = go "squares2" (squares' :: Unop (RTree N0 Int))

-- -- Working out a reify issue.
-- main = go "sum2f" (sum :: RTree N2 Int -> Int)

-- -- Causes a GHC RTS crash ("internal error: stg_ap_pp_ret") with Reify.
-- -- Seemingly infinite rewrite loop with Standard.
-- main = go "prodA1" (uncurry prodA :: (RTree N1 Int,RTree N1 Int) -> RTree N1 Int)

-- main = go "prodA0" (uncurry prodA :: (RTree N0 Int,RTree N0 Int) -> RTree N0 Int)

-- main = go "idA" (uncurry f)
--  where
--    f :: Identity Bool -> Identity Bool -> Identity (Bool,Bool)
--    f = liftA2 (,)

-- main = go "applyLin-v23" (uncurry (($@) :: Matrix N2 N3 Int -> Vec N2 Int -> Vec N3 Int))

-- main = go "applyLin-v42" (uncurry (($@) :: Matrix N4 N2 Int -> Vec N4 Int -> Vec N2 Int))

-- main = go "applyLin-v45" (uncurry (($@) :: Matrix N4 N5 Int -> Vec N4 Int -> Vec N5 Int))

-- main = go "applyLin-t21" (uncurry (($@) :: MatrixT N2 N1 Int -> RTree N2 Int -> RTree N1 Int))

-- main = go "applyLin-t22" (uncurry (($@) :: MatrixT N2 N2 Int -> RTree N2 Int -> RTree N2 Int))

-- main = go "applyLin-t23" (uncurry (($@) :: MatrixT N2 N3 Int -> RTree N2 Int -> RTree N3 Int))

-- main = go "applyLin-t32" (uncurry (($@) :: MatrixT N3 N2 Int -> RTree N3 Int -> RTree N2 Int))

-- main = go "applyLin-t34" (uncurry (($@) :: MatrixT N3 N4 Int -> RTree N3 Int -> RTree N4 Int))

-- main = go "applyLin-t45" (uncurry (($@) :: MatrixT N4 N5 Int -> RTree N4 Int -> RTree N5 Int))

-- main = go "applyLin-v3t2" (uncurry (($@) :: RTree N2 (Vec N3 Int) -> Vec N3 Int -> RTree N2 Int))

-- main = go "applyLin-t2v3" (uncurry (($@) :: Vec N3 (RTree N2 Int) -> RTree N2 Int -> Vec N3 Int))

-- main = go "composeLin-v234" (uncurry ((.@) :: Matrix N3 N4 Int -> Matrix N2 N3 Int -> Matrix N2 N4 Int))

-- main = go "composeLin-t234" (uncurry ((.@) :: MatrixT N3 N4 Int -> MatrixT N2 N3 Int -> MatrixT N2 N4 Int))

-- Takes a very long time. I haven't seen it through yet.
-- main = go "composeLin-t324" (uncurry ((.@) :: MatrixT N2 N4 Int -> MatrixT N3 N2 Int -> MatrixT N3 N4 Int))

-- main = go "composeLin-t222" (uncurry ((.@) :: MatrixT N2 N2 Int -> MatrixT N2 N2 Int -> MatrixT N2 N2 Int))

-- main = go "composeLin-t232" (uncurry ((.@) :: MatrixT N3 N2 Int -> MatrixT N2 N3 Int -> MatrixT N2 N2 Int))

-- main = go "shiftL-rt1" (shiftL :: (RTree N1 Bool, Bool) -> (Bool, RTree N1 Bool))

-- main = go "shiftR-rt1" (shiftR :: (Bool, RTree N1 Bool) -> (RTree N1 Bool, Bool))

-- main = go "lsumsp-rt2" (lsums' :: Unop (RTree N2 Int))

-- main = go "lsumsp-lt5" (lsums' :: Unop (LTree N5 Int))

-- main = go "lsums-rt5" (lsums :: RTree N5 Int -> (RTree N5 Int, Int))

-- main = go "lsums-lt4" (lsums :: LTree N4 Int -> (LTree N4 Int, Int))

-- main = go "foo" (\ a -> not a)

-- main = go "foo" not

-- main = go "and-curried" ((&&) :: Bool -> Bool -> Bool)

-- main = go "test-add-with-constant-fold" foo
--  where
--    foo :: Int -> Int
--    foo x = f x + g x
--    f _ = 3
--    g _ = 4

-- Ragged trees

type MatrixG p q a = Ragged q (Ragged p a)

type R1  = LU
type R2  = BU R1 R1
type R3  = BU R2 R1
type R4  = BU R2 R2
type R5  = BU R3 R2
type R8  = BU R3 R5
type R11 = BU R8 R5

type R8'  = BU R4  R4
type R13' = BU R8' R3

-- main = go "fmap-gt1" (fmap not :: Unop (Ragged R1 Bool))

-- main = go "sum-gt11" (sum :: Ragged R11 Int -> Int)

-- main = go "sum-gt13p" (sum :: Ragged R13' Int -> Int)

-- main = go "dotsp-gt8" (dotsp :: Pair (Ragged R8 Int) -> Int)

-- main = go "applyLin-gt45" (uncurry (($@) :: MatrixG R4 R5 Int -> Ragged R4 Int -> Ragged R5 Int))

-- main = go "composeLin-gt234" (uncurry ((.@) :: MatrixG R3 R4 Int -> MatrixG R2 R3 Int -> MatrixG R2 R4 Int))

-- Linear map composition mixing ragged trees, top-down perfect trees, and vectors.
main = go "composeLin-gt3rt2v2"
          (uncurry ((.@) :: Vec N2 (RTree N2 Int) -> RTree N2 (Ragged R3 Int) -> Vec N2 (Ragged R3 Int)))

-- Note: some of the scan examples redundantly compute some additions.
-- I suspect that they're only the same *after* the zero simplifications.

-- main = go "lsums-gt5" (lsums' :: Unop (Ragged R5 Int))
