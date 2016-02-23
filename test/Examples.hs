{-# LANGUAGE CPP, TupleSections, GADTs, TypeOperators, Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

----------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Examples / tinkering.
----------------------------------------------------------------------

-- {-# OPTIONS_GHC -fplugin=LambdaCCC.Plugin -dcore-lint #-}
-- {-# OPTIONS_GHC -fplugin-opt=LambdaCCC.Reify:verbose #-}

{-# OPTIONS_GHC -dppr-case-as-let -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -ddump-rule-firings #-}
-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- module Examples where

-- import Prelude

import Data.Monoid (Sum(..))
import Control.Applicative (liftA2)
import GHC.Generics ((:.:))

import LambdaCCC.Run

import Circat.Rep

import Control.Compose ((:.)(..),unO)

import LambdaCCC.Misc hiding (Sized(..))
-- import LambdaCCC.Adder
-- import LambdaCCC.CRC
-- import LambdaCCC.Bitonic
-- import LambdaCCC.Counters
-- import qualified LambdaCCC.RadixSort as RS
import LambdaCCC.Lambda (EP,reifyEP)

{-
import Circat.Pair (Pair(..),sortP)
import qualified Circat.Pair as P
import qualified Circat.RTree as RT
import qualified Circat.LTree as LT
import qualified Circat.RaggedTree as Ra
import Circat.RaggedTree (TU(..), R1, R2, R3, R4, R5, R8, R11, R13)
import Circat.Shift
import Circat.Scan
import Circat.FFT
-- import Circat.Mealy hiding (ArrowCircuit(..))
-- import qualified Circat.Mealy as Mealy
-- import Circat.Circuit (GenBuses(..), GS, Attr, systemSuccess)
-}

import Circat.Doubli
import Circat.Complex

-- import Data.Complex

import LambdaCCC.Lambda (reifyEP)
import LambdaCCC.Run

import ShapedTypes.Sized
import ShapedTypes.Nat
import ShapedTypes.Pair
import ShapedTypes.Vec
import qualified ShapedTypes.RPow as R
import qualified ShapedTypes.LPow as L
import ShapedTypes.Scan
import ShapedTypes.FFT

type RTree n = Pair R.^ n
type LTree n = Pair L.^ n

-- type Ragged = Ra.Tree

type C = Complex Doubli

main = do

--   go "lsums-p" (lsums :: Pair Int -> Pair Int :* Int)

--   goSep "lsums-rt0" 0.35 (lsums :: RTree N0 Int -> RTree N0 Int :* Int)
--   goSep "lsums-rt1" 0.5 (lsums :: RTree N1 Int -> RTree N1 Int :* Int)
--   goSep "lsums-rt2" 0.75 (lsums :: RTree N2 Int -> RTree N2 Int :* Int)
--   goSep "lsums-rt3"  1 (lsums :: RTree N3 Int -> RTree N3 Int :* Int)
--   goSep "lsums-rt4"  2 (lsums :: RTree N4 Int -> RTree N4 Int :* Int)
--   goSep "lsums-rt5"  3 (lsums :: RTree N5 Int -> RTree N5 Int :* Int)
--   goSep "lsums-rt6"  5 (lsums :: RTree N6 Int -> RTree N6 Int :* Int)
--   goSep "lsums-rt7"  8 (lsums :: RTree N7 Int -> RTree N7 Int :* Int)
--   goSep "lsums-rt8" 13 (lsums :: RTree N8 Int -> RTree N8 Int :* Int)
--   goSep "lsums-rt9" 21 (lsums :: RTree N9 Int -> RTree N9 Int :* Int)

--   goSep "lsums-rt10"  34 (lsums :: RTree N10 Int -> RTree N10 Int :* Int)
--   goSep "lsums-rt11"  55 (lsums :: RTree N11 Int -> RTree N11 Int :* Int)
--   goSep "lsums-rt12"  89 (lsums :: RTree N12 Int -> RTree N12 Int :* Int)
--   goSep "lsums-rt13" 144 (lsums :: RTree N13 Int -> RTree N13 Int :* Int)
--   goSep "lsums-rt14" 233 (lsums :: RTree N14 Int -> RTree N14 Int :* Int)
--   goSep "lsums-rt15" 377 (lsums :: RTree N15 Int -> RTree N15 Int :* Int)
--   goSep "lsums-rt16" 610 (lsums :: RTree N16 Int -> RTree N16 Int :* Int)

--   goSep "lsums-lt6"  4 (lsums :: LTree N6 Int -> LTree N6 Int :* Int)

--   go "plus-c" ((+) :: Binop C)

--   go "fft-p" (fft :: Pair C -> Pair C)

--    go "fft-v1" (fft :: Unop (Vec N1 C))

--   goSep "fft-rt1" 1 (fft :: RTree N1 C -> LTree N1 C)
--   goSep "fft-rt2" 1 (fft :: RTree N2 C -> LTree N2 C)
--   goSep "fft-rt3" 2 (fft :: RTree N3 C -> LTree N3 C)
--   goSep "fft-rt4" 3 (fft :: RTree N4 C -> LTree N4 C)
--   goSep "fft-rt5" 4 (fft :: RTree N5 C -> LTree N5 C)
--   goSep "fft-rt6" 7 (fft :: RTree N6 C -> LTree N6 C)

--   goSep "fft-lt1" 1 (fft :: LTree N1 C -> RTree N1 C)
--   goSep "fft-lt2" 1 (fft :: LTree N2 C -> RTree N2 C)
--   goSep "fft-lt3" 2 (fft :: LTree N3 C -> RTree N3 C)
--   goSep "fft-lt4" 3 (fft :: LTree N4 C -> RTree N4 C)
  goSep "fft-lt5" 4 (fft :: LTree N5 C -> RTree N5 C)
--   goSep "fft-lt6" 7 (fft :: LTree N6 C -> RTree N6 C)

--   print (reifyEP (pure () :: Pair ()))

--   print (reifyEP (pure () :: (Pair :.: Pair) ()))


--   go "foo" (size (pure () :: (Pair :.: Pair) ()))


--   go "foo" (size (pure () :: RTree N8 ()))


--   go "map-p" (fmap not :: Unop (Pair Bool))

--   go "sum-p" (sum :: Pair Int -> Int)

--   go "and-p" (liftA2 (&&) :: Binop (Pair Bool))

--   go "foo" (liftA2 (&&) :: Binop (RTree N1 Bool))

--   goSep "and-lv5-3" 3 (and :: (Vec N5 L.^ N3) Bool -> Bool)

--   goSep "map-rt6" 3 (fmap not :: Unop (RTree N6 Bool))

--   goSep "dot-prt8" 3 (dotG :: Pair (RTree N8 Int) -> Int)

--   goSep "transpose-pp" 1 (transpose :: Unop (Pair (Pair Bool)))

--   goSep "transpose-rt3p" 2 (sequenceA :: RTree N3 (Pair Bool) -> Pair (RTree N3 Bool))

--   goSep "transpose-rt3rt4" 12 (sequenceA :: RTree N3 (RTree N4 Bool) -> RTree N4 (RTree N3 Bool))

--   goSep "applyLin-rt34" 3 (($@) :: MatrixT N3 N4 Int -> RTree N3 Int -> RTree N4 Int)

--   goSep "composeLin-rt232" 4 ((.@) :: MatrixT N3 N2 Int -> MatrixT N2 N3 Int -> MatrixT N2 N2 Int)

--   go "lsums-p" (lsums :: Pair Int -> (Pair Int, Int))

  -- go "lsums-rt0" (lsums :: RTree N0 Int -> (RTree N0 Int, Int))
  -- go "lsums-lt0" (lsums :: LTree N0 Int -> (LTree N0 Int, Int))

-- fooP :: Num a => Unop (Pair a)
-- fooP (a :# b) = (a + b) :# (a - b)

-- fftP :: RealFloat a => Unop (Pair (Complex a))
-- fftP (a :# b) = (a + b) :# (a - b)


{--------------------------------------------------------------------
    Misc definitions
--------------------------------------------------------------------}

negIncr :: Num a => a -> a
negIncr = negate . (1 +)

sqr :: Num a => a -> a
sqr x = x * x

sumTI :: RTree n Int -> Int
sumTI (R.L a) = a
sumTI (R.B (u :# v)) = sumTI u + sumTI v

leftMost :: RTree n a -> a
leftMost (R.L a) = a
leftMost (R.B (u :# _)) = leftMost u

dotG :: (Traversable g, Foldable g, Applicative f, Foldable f, Num a) => g (f a) -> a
dotG = sum . fmap product . transpose

-- Infix binary dot product
infixl 7 <.>
(<.>) :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u <.> v = dotG (u :# v)

-- Generalized matrices

type Matrix  m n a = Vec    n (Vec    m a)
type MatrixT m n a = RTree  n (RTree  m a)
-- type MatrixG p q a = Ragged q (Ragged p a)

infixr 1 $@
-- infixl 9 .@

-- | Apply a linear transformation represented as a matrix
-- ($@) :: (IsNat m, Num a) => Matrix m n a -> Vec m a -> Vec n a
($@) :: (Foldable m, Applicative m, Functor n, Num a) =>
        n (m a) -> m a -> n a
mat $@ vec = (<.> vec) <$> mat

-- -- | Compose linear transformations represented as matrices
-- (.@) :: (IsNat m, IsNat n, IsNat o, Num a) =>
--         Matrix n o a -> Matrix m n a -> Matrix m o a
(.@) :: ( Applicative o, Traversable n, Applicative n
        , Traversable m, Applicative m, Num a ) =>
        o (n a) -> n (m a) -> o (m a)
-- no .@ mn = (\ n -> (n <.>) <$> transpose mn) <$> no
no .@ mn = transpose ((no $@) <$> transpose mn)

#if 0
{--------------------------------------------------------------------
    Permutations
--------------------------------------------------------------------}

invertR :: IsNat n => RTree n a -> LTree n a
invertR = invertR' nat

invertR' :: Nat n -> RTree n a -> LTree n a
invertR' Zero     = \ (R.L a ) -> L.L a
invertR' (Succ m) = \ (R.B ts) -> L.B (invertR' m (transpose ts))
-- invertR' (Succ m) = \ (R.B ts) -> L.B (transpose (invertR' m <$> ts))

#if 0
R.unB    :: RTree (S n)   a  -> Pair (RTree n a)
transpose :: Pair (RTree n a) -> RTree n (Pair a)
invertR   :: RTree n (Pair a) -> LTree n (Pair a)
L.B      :: LTree n (Pair a) -> LTree (S n)   a

R.unB       :: RTree (S n)   a  -> Pair (RTree n a)
fmap invertR :: Pair (RTree n a) -> Pair (LTree n a)
transpose    :: Pair (LTree n a) -> LTree n (Pair a)
L.B         :: LTree n (Pair a) -> LTree (S n)   a
#endif

-- We needed the IsNat n for Applicative on RTree n.
-- The reverse transformation is easier, since we know Pair is Applicative.

invertL :: LTree n a -> RTree n a
invertL (L.L a ) = R.L a
invertL (L.B ts) = R.B (transpose (invertL ts))
-- invertL (L.B ts) = R.B (invertL <$> transpose ts)

-- invertR' (Succ m) = \ (R.B ts) -> L.B (transpose (invertR' m <$> ts))

#if 0
L.unB    :: LTree (S n)   a  -> LTree n (Pair a)
invertL   :: LTree n (Pair a) -> RTree n (Pair a)
transpose :: RTree n (Pair a) -> Pair (RTree n a)
R.B      :: Pair (RTree n a) -> RTree (S n)   a

L.unB       :: LTree (S n)   a  -> LTree n (Pair a)
transpose    :: LTree n (Pair a) -> Pair (LTree n a)
fmap invertL :: Pair (LTree n a) -> Pair (RTree n a)
R.B         :: Pair (RTree n a) -> RTree (S n)   a
#endif

#endif
