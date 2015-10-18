{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment
{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE DataKinds, GADTs #-}  -- for TU
{-# LANGUAGE LambdaCase, TupleSections #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=30 #-}
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

import Prelude hiding ({- id,(.), -}foldl,foldr,sum,product,zipWith,reverse,and,or,scanl,minimum,maximum)

import Data.Monoid (Monoid(..),(<>),Sum(..),Product(..))
import Data.Functor ((<$>))
import Control.Applicative -- (Applicative(..),liftA2,liftA3)
import Data.Foldable (Foldable(..),sum,product,and,or,toList,minimum,maximum)
import Data.Traversable (Traversable(..))
-- import Control.Category (id,(.))
import Control.Arrow (Arrow(..))
import qualified Control.Arrow as Arrow
import Data.Tuple (swap)
import Data.Maybe (fromMaybe,maybe)
import Text.Printf (printf)

import Test.QuickCheck (arbitrary,Gen,generate,vectorOf)

-- transformers
import Data.Functor.Identity

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat,natToZ)
import TypeUnary.Vec hiding (transpose,iota)
import qualified TypeUnary.Vec as V

import LambdaCCC.Misc
  (xor,boolToInt,dup,Unop,Binop,Ternop,transpose,(:*),loop,delay,Reversible(..))
import LambdaCCC.Adder
import LambdaCCC.CRC -- hiding (crcS,sizeA)
import LambdaCCC.Bitonic
import LambdaCCC.Counters
import qualified LambdaCCC.RadixSort as RS

-- import Circat.Misc (Reversible(..))
import Circat.Rep (bottom)
import Circat.Pair (Pair(..),sortP)
import qualified Circat.Pair as P
import qualified Circat.RTree as RT
import qualified Circat.LTree as LT
import qualified Circat.RaggedTree as Ra
import Circat.RaggedTree (TU(..), R1, R2, R3, R4, R5, R8, R11, R13)
import Circat.Shift
import Circat.Scan
import Circat.Mealy hiding (ArrowCircuit(..))
import qualified Circat.Mealy as Mealy
import Circat.Circuit (GenBuses(..), GS, Attr, systemSuccess, Complex(..),cis)

-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import Circat.Classes (IfT)
import LambdaCCC.Lambda (EP,reifyEP)

import LambdaCCC.Run

-- Experiment for Typeable resolution in reification
import qualified Data.Typeable

-- To support Dave's FFT stuff, below.
-- import Data.Complex (cis)
import Data.Newtypes.PrettyDouble

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

liftA4 :: Applicative f =>
          (a -> b -> c -> a -> d) -> f a -> f b -> f c -> f a -> f d
liftA4 f as bs cs ds = liftA3 f as bs cs <*> ds

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type RTree = RT.Tree
type LTree = LT.Tree
type Ragged = Ra.Tree

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

{--------------------------------------------------------------------
    Dot products
--------------------------------------------------------------------}

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

-- Infix binary dot product
infixl 7 <.>
(<.>) :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u <.> v = sum (liftA2 (*) u v)

-- | Monoid under lifted multiplication.
newtype ProductA f a = ProductA { getProductA :: f a }

instance (Applicative f, Num a) => Monoid (ProductA f a) where
  mempty = ProductA (pure 1)
  ProductA u `mappend` ProductA v = ProductA (liftA2 (*) u v)

productA :: (Foldable g, Applicative f, Num a) => g (f a) -> f a
productA = getProductA . foldMap ProductA

dota :: (Foldable g, Foldable f, Applicative f, Num a) => g (f a) -> a
dota = sum . productA

{--------------------------------------------------------------------
    Generalized matrices
--------------------------------------------------------------------}

type Matrix  m n a = Vec    n (Vec    m a)
type MatrixT m n a = RTree  n (RTree  m a)
type MatrixG p q a = Ragged q (Ragged p a)

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
-- no .@ mn = (\ n -> (n <.>) <$> transpose mn) <$> no
no .@ mn = transpose ((no $@) <$> transpose mn)

{--------------------------------------------------------------------
    Permutations
--------------------------------------------------------------------}

invertR :: IsNat n => RTree n a -> LTree n a
invertR = invertR' nat

invertR' :: Nat n -> RTree n a -> LTree n a
invertR' Zero     = \ (RT.L a ) -> LT.L a
invertR' (Succ m) = \ (RT.B ts) -> LT.B (invertR' m (transpose ts))
-- invertR' (Succ m) = \ (RT.B ts) -> LT.B (transpose (invertR' m <$> ts))

#if 0
RT.unB    :: RTree (S n)   a  -> Pair (RTree n a)
transpose :: Pair (RTree n a) -> RTree n (Pair a)
invertR   :: RTree n (Pair a) -> LTree n (Pair a)
LT.B      :: LTree n (Pair a) -> LTree (S n)   a

RT.unB       :: RTree (S n)   a  -> Pair (RTree n a)
fmap invertR :: Pair (RTree n a) -> Pair (LTree n a)
transpose    :: Pair (LTree n a) -> LTree n (Pair a)
LT.B         :: LTree n (Pair a) -> LTree (S n)   a
#endif

-- We needed the IsNat n for Applicative on RTree n.
-- The reverse transformation is easier, since we know Pair is Applicative.

invertL :: LTree n a -> RTree n a
invertL (LT.L a ) = RT.L a
invertL (LT.B ts) = RT.B (transpose (invertL ts))
-- invertL (LT.B ts) = RT.B (invertL <$> transpose ts)

-- invertR' (Succ m) = \ (RT.B ts) -> LT.B (transpose (invertR' m <$> ts))

#if 0
LT.unB    :: LTree (S n)   a  -> LTree n (Pair a)
invertL   :: LTree n (Pair a) -> RTree n (Pair a)
transpose :: RTree n (Pair a) -> Pair (RTree n a)
RT.B      :: Pair (RTree n a) -> RTree (S n)   a

LT.unB       :: LTree (S n)   a  -> LTree n (Pair a)
transpose    :: LTree n (Pair a) -> Pair (LTree n a)
fmap invertL :: Pair (LTree n a) -> Pair (RTree n a)
RT.B         :: Pair (RTree n a) -> RTree (S n)   a
#endif

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

inTest :: String -> IO ()
inTest cmd = systemSuccess ("cd ../test; " ++ cmd) -- (I run ghci in ../src)

doit :: IO ()
doit = inTest "make doit"

reify :: IO ()
reify = inTest "make reify"

noReify :: IO ()
noReify = inTest "make no-reify"

make :: IO ()
make = systemSuccess "cd ../..; make"

dateFigureSvg :: String -> String -> IO ()
dateFigureSvg date fig = systemSuccess (printf "cd ../test; ./date-figure-svg %s \"%s\"" date fig)

figureSvg :: String -> IO ()
figureSvg str = systemSuccess ("cd ../test; ./figure-svg " ++ str)

dateLatestSvg :: String -> IO ()
dateLatestSvg date = systemSuccess (printf "cd ../test; ./date-latest-svg \"%s\"" date)

latestSvg :: IO ()
latestSvg = systemSuccess "cd ../test; ./latest-svg"

do1 :: IO ()
do1 = inTest "hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTreeNoReify.hss"

do2 :: IO ()
do2 = inTest "hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTree.hss"

-- Only works when compiled with HERMIT
main :: IO ()

-------- Dave's FFT stuff ----------------------------------------------
-- Phasor, as a function of tree depth.
phasor :: (IsNat n, RealFloat a, Enum a) => Nat n -> RTree n (Complex a)
phasor n = scanlTEx (*) 1 (pure phaseDelta)
    where phaseDelta = cis ((-pi) / 2 ** natToZ n)

-- Radix-2, DIT FFT
fft_r2_dit :: (IsNat n, RealFloat a, Enum a) => RTree n (Complex a) -> RTree n (Complex a)
fft_r2_dit = fft_r2_dit' nat

fft_r2_dit' :: (RealFloat a, Enum a) => Nat n -> RTree n (Complex a) -> RTree n (Complex a)
fft_r2_dit'  Zero    = id
fft_r2_dit' (Succ n) = RT.toB . P.inP (uncurry (+) &&& uncurry (-)) . P.secondP (liftA2 (*) (phasor n)) . fmap (fft_r2_dit' n) . RT.bottomSplit

-- main = go "fft_r2_dit" (fft_r2_dit :: RTree N1 (Complex Int) -> RTree N1 (Complex Int))
main = go "fft_r2_dit" (fft_r2_dit :: RTree N2 (Complex Double) -> RTree N2 (Complex Double))
-- main = go "fft_r2_dit" (fft_r2_dit :: RTree N1 (Complex PrettyDouble) -> RTree N1 (Complex PrettyDouble))
-- main = go "fft_r2_dit" (fft_r2_dit :: RTree N2 (Complex Int) -> RTree N2 (Complex Int))
-- main = goSep "fft_r2_dit" 1 (fft_r2_dit :: RTree N1 (Complex Int) -> RTree N1 (Complex Int))
-------- End Dave's FFT stuff ------------------------------------------

-- main = go "map-not-v5" (fmap not :: Vec N5 Bool -> Vec N5 Bool)

-- main = go "map-square-v5" (fmap square :: Vec N5 Int -> Vec N5 Int)

-- main = go "map-t3" (fmap not :: Unop (RTree N3 Bool))

-- main = go "tdott-2" (dot''' :: Pair (RTree N2 Int) -> Int)

-- main = go "dotsp-v3t2" (dotsp :: Vec N3 (RTree N2 Int) -> Int)

-- main = go "dotsp-t2t2" (dotsp :: RTree N2 (RTree N2 Int) -> Int)

-- main = go "dotsp-pt3" (dotsp :: Pair (RTree N3 Int) -> Int)

-- main = go "dotsp-pv5" (dotsp :: Pair (Vec N5 Int) -> Int)

-- main = go "dotsp-plt3" (dotsp :: Pair (LTree N3 Int) -> Int)

-- main = go "dotap-2" (dotap :: RTree N2 Int -> RTree N2 Int -> Int)

-- main = go "tdot-2" (dot'' :: RTree N2 (Pair Int) -> Int)

-- main = go "test" (dot'' :: RTree N4 (Pair Int) -> Int)

-- main = go "plusInt" ((+) :: Int -> Int -> Int)
-- main = go "or" ((||) :: Bool -> Bool -> Bool)

-- main = goSep "pure-rt3" 1 (\ () -> (pure False :: RTree N3 Bool))

-- main = go "foo" (\ (_ :: RTree N3 Bool) -> False)

-- main = go "sum-p" (sum :: Pair Int -> Int)

-- main = go "sumSquare-p" (sumSquare :: Pair Int -> Int)

-- main = goSep "sumSquare-rt2" 0.75 (sumSquare :: RTree N2 Int -> Int)

-- main = go "sum-v8" (sum :: Vec N8 Int -> Int)

-- main = go "and-v5" (and :: Vec N5 Bool -> Bool)

-- main = go "sum-t3" (sum :: RTree N3 Int -> Int)

-- main = go "sum-lt3" (sum :: LTree N3 Int -> Int)

-- main = go "sum-foldl-v5" (foldl (+) 0 :: Vec N5 Int -> Int)

-- main = go "sum-foldr-v5" (foldr (+) 0 :: Vec N5 Int -> Int)

-- main = go "sum-foldl-t3" (foldl (+) 0 :: RTree N3 Int -> Int)

-- main = go "sum-foldr-t3" (foldr (+) 0 :: RTree N3 Int -> Int)

-- main = do go "squares3" (squares :: RTree N3 Int -> RTree N3 Int)
--           go "sum4"     (sum     :: RTree N4 Int -> Int)
--           go "dot4"     (dot     :: RTree N4 (Int,Int) -> Int)

-- main = go "test" (dot :: RTree N4 (Int,Int) -> Int)

-- -- Ranksep: rt1=0.5, rt2=1, rt3=2, rt4=4,rt5=8
-- main = goSep "transpose-pt4" 4 (transpose :: Pair (RTree N4 Bool) -> RTree N4 (Pair Bool))

-- -- Ranksep: rt1=0.5, rt2=1, rt3=2, rt4=4,rt5=8
-- main = goSep "transpose-t4p" 4 (transpose :: RTree N4 (Pair Bool) -> Pair (RTree N4 Bool))

-- -- Ranksep: rt1=1, rt2=2, rt3=4, rt4=8, rt5=16
-- main = goSep "transpose-v3t5" 16 (transpose :: Vec N3 (RTree N5 Bool) -> RTree N5 (Vec N3 Bool))

-- -- Ranksep: rt1=2, rt2=4, rt3=8, rt4=16, rt5=32
-- main = goSep "transpose-v5t3" 8 (transpose :: Vec N5 (RTree N3 Bool) -> RTree N3 (Vec N5 Bool))

-- -- Ranksep: rt1=0.5, rt2=1, rt3=2, rt4=4, rt5=8
-- main = goSep "invertR-5" 8 (invertR :: RTree N5 Bool -> LTree N5 Bool)

-- main = go "vtranspose-34" (transpose :: Matrix N3 N4 Int -> Matrix N4 N3 Int)

-- main = go "vtranspose-34" (transpose :: Vec N3 (Vec N4 Int) -> Vec N4 (Vec N3 Int))

-- main = go "ttranspose-23" (transpose :: MatrixT N2 N3 Int -> MatrixT N3 N2 Int)

-- main = go "swap" (swap :: Int :* Bool -> Bool :* Int)

-- main = go "add" (\ (a,b) -> a+b :: Int)

-- main = go "rot31" (\ (a,b,c) -> (b,c,a) :: (Bool,Bool,Bool))

-- main = go "rot41" (\ (a,b,c,d) -> (b,c,d,a) :: (Bool,Bool,Bool,Bool))

-- main = go "rev4" (\ (a,b,c,d) -> (d,c,b,a) :: (Bool,Bool,Bool,Bool))

-- main = go "sum-2" (\ (a,b) -> a+b :: Int)

-- main = go "sum-3" (\ (a,b,c) -> a+b+c :: Int)

-- main = go "sum-4a" ((\ (a,b,c,d) -> a+b+c+d) :: (Int,Int,Int,Int) -> Int)

-- main = go "sum-4b" ((\ (a,b,c,d) -> (a+b)+(c+d)) :: (Int,Int,Int,Int) -> Int)

-- main = go "dot-22" ((\ ((a,b),(c,d)) -> a*c + b*d) :: ((Int,Int),(Int,Int)) -> Int)

-- main = go "tdot-4" (dot :: RTree N4 (Int,Int) -> Int)

-- main = go "tpdot-4" (dot'' :: RTree N4 (Pair Int) -> Int)

-- -- Doesn't wedge.
-- main = go "dotp" ((psum . prod) :: Pair (Int,Int) -> Int)

-- main = go "prod1" (prod :: RTree N1 (Int,Int) -> RTree N1 Int)

-- main = go "dot5" (dot :: RTree N5 (Int,Int) -> Int)

-- main = go "squares2" (squares :: Unop (RTree N2 Int))

-- main = go "psum" (psum :: Pair Int -> Int)

-- main = go "tsum1" (tsum :: RTree N1 Int -> Int)

-- -- Not working yet: the (^) is problematic.
-- main = go "squaresp-rt0" (squares' :: Unop (RTree N0 Int))

-- main = goSep "applyLin-v23" 1 (($@) :: Matrix N2 N3 Int -> Vec N2 Int -> Vec N3 Int)

-- main = goSep "applyLin-v42" 1 (($@) :: Matrix N4 N2 Int -> Vec N4 Int -> Vec N2 Int)

-- main = goSep "applyLin-v45" 1 (($@) :: Matrix N4 N5 Int -> Vec N4 Int -> Vec N5 Int)

-- main = goSep [ranksep 2] -t21 (($@) :: MatrixT N2 N1 Int -> RTree N2 Int -> RTree N1 Int)

-- main = go "applyLin-t22" (($@) :: MatrixT N2 N2 Int -> RTree N2 Int -> RTree N2 Int)

-- main = go "applyLin-t23" (($@) :: MatrixT N2 N3 Int -> RTree N2 Int -> RTree N3 Int)

-- main = go "applyLin-t32" (($@) :: MatrixT N3 N2 Int -> RTree N3 Int -> RTree N2 Int)

-- main = go "applyLin-t34" (($@) :: MatrixT N3 N4 Int -> RTree N3 Int -> RTree N4 Int)

-- main = go "applyLin-t45" (($@) :: MatrixT N4 N5 Int -> RTree N4 Int -> RTree N5 Int)

-- main = go "applyLin-v3t2" (($@) :: RTree N2 (Vec N3 Int) -> Vec N3 Int -> RTree N2 Int)

-- main = go "applyLin-t2v3" (($@) :: Vec N3 (RTree N2 Int) -> RTree N2 Int -> Vec N3 Int)

-- main = go "composeLin-v234" ((.@) :: Matrix N3 N4 Int -> Matrix N2 N3 Int -> Matrix N2 N4 Int)

-- main = go "composeLin-t234" ((.@) :: MatrixT N3 N4 Int -> MatrixT N2 N3 Int -> MatrixT N2 N4 Int)

-- -- Takes a very long time. I haven't seen it through yet.

-- main = go "composeLin-t324" ((.@) :: MatrixT N2 N4 Int -> MatrixT N3 N2 Int -> MatrixT N3 N4 Int)

-- main = go "composeLin-t222" ((.@) :: MatrixT N2 N2 Int -> MatrixT N2 N2 Int -> MatrixT N2 N2 Int)

-- main = go "composeLin-t232" ((.@) :: MatrixT N3 N2 Int -> MatrixT N2 N3 Int -> MatrixT N2 N2 Int)

-- -- Shift examples are identities on bit representations
-- main = go "shiftR-v3" (shiftR :: Vec N3 Bool :* Bool -> Bool :* Vec N3 Bool)

-- -- Shift examples are identities on bit representations
-- main = go "shiftR-swap-v3" (shiftR . swap :: Unop (Bool :* Vec N3 Bool))

-- main = go "shiftR-rt2" (shiftR :: RTree N2 Bool :* Bool -> Bool :* RTree N2 Bool)

-- main = go "shiftL-rt1" (shiftL :: Bool :* RTree N1 Bool -> RTree N1 Bool :* Bool)

-- main = go "shiftRF-v3v2" (shiftRF :: Vec N3 Bool :* Vec N2 Bool -> Vec N2 Bool :* Vec N3 Bool)

-- main = go "shiftRF-v2v3" (shiftRF :: Vec N2 Bool :* Vec N3 Bool -> Vec N3 Bool :* Vec N2 Bool)

-- -- Shift in two zeros from the right
-- main = go "shiftRF-v3v2F" (flip (curry shift) (pure False))
--  where
--    shift :: Vec N3 Bool :* Vec N2 Bool -> Vec N2 Bool :* Vec N3 Bool
--    shift = shiftRF

-- -- Shift in two zeros from the left
-- main = go "shiftLF-v2v3F" (curry shift (pure False))
--  where
--    shift :: Vec N2 Bool :* Vec N3 Bool -> Vec N3 Bool :* Vec N2 Bool
--    shift = shiftRF

-- -- Shift five zeros into a tree from the left
-- main = go "shiftLF-v5rt4F" (curry shift (pure False))
--  where
--    shift :: Vec N5 Bool :* RTree N4 Bool -> RTree N4 Bool :* Vec N5 Bool
--    shift = shiftRF

-- main = go "lsumsp-rt2" (lsums' :: Unop (RTree N2 Int))

-- main = go "lsumsp-rt2" (lsums' :: Unop (RTree N2 Int))

-- main = go "lsumsp-lt3" (lsums' :: Unop (LTree N3 Int))

-- main = go "lsums-v5" (lsums :: Vec N5 Int -> (Vec N5 Int, Int))

-- main = go "lsums-rt2" (lsums :: RTree N2 Int -> (RTree N2 Int, Int))

-- main = go "lsums-lt2" (lsums :: LTree N2 Int -> (LTree N2 Int, Int))

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "lParities-rt5" (5/2) (lParities :: RTree N5 Bool -> (RTree N5 Bool, Bool))

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "lParities-lt4" (4/2) (lParities :: LTree N4 Bool -> (LTree N4 Bool, Bool))

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "lParities-ex-rt3" (3/2) (fst . lParities :: Unop (RTree N3 Bool))

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "lParities-ex-lt3" (3/2) (fst . lParities :: Unop (LTree N3 Bool))

-- main = go "foo" (\ a -> not a)

-- main = go "not" not

-- main = go "not-pair" (\ a -> (not a, not a))

-- main = go "and-curried" ((&&) :: Bool -> Bool -> Bool)

-- main = go "test-add-with-constant-fold" foo
--  where
--    foo :: Int -> Int
--    foo x = f x + g x
--    f _ = 3
--    g _ = 4

-- -- True
-- main = go "foo" (\ a -> not a || True)

-- -- not a
-- main = go "foo" (\ a -> a `xor` True)

-- -- a
-- main = go "foo" (\ a -> a `xor` False)

-- main = go "fmap-gt5" (fmap not :: Unop (Ragged R5 Bool))

-- main = go "sum-gt5" (sum :: Ragged R5 Int -> Int)

-- main = go "sum-gt13p" (sum :: Ragged R13' Int -> Int)

-- main = go "dotsp-gt8" (dotsp :: Pair (Ragged R8 Int) -> Int)

-- main = go "applyLin-gt45" (($@) :: MatrixG R4 R5 Int -> Ragged R4 Int -> Ragged R5 Int)

-- main = go "composeLin-gt234" ((.@) :: MatrixG R3 R4 Int -> MatrixG R2 R3 Int -> MatrixG R2 R4 Int)

-- -- Linear map composition mixing ragged trees, top-down perfect trees, and vectors.
-- main = go "composeLin-gt3rt2v2"
--           ((.@) :: Vec N2 (RTree N2 Int) -> RTree N2 (Ragged R3 Int) -> Vec N2 (Ragged R3 Int))

-- main = go "composeLin-gt1rt0v1"
--           ((.@) :: Vec N1 (RTree N0 Int) -> RTree N0 (Ragged R1 Int) -> Vec N1 (Ragged R1 Int))

-- Note: some of the scan examples redundantly compute some additions.
-- I suspect that they're only the same *after* the zero simplifications.
-- These zero additions are now removed in the circuit generation back-end.

-- ranksep: 8=1.5, 11=2.5
-- main = goSep "lsumsp-gt3" =1.5 (lsums' :: Unop (Ragged Ra.R3 Int))

-- main = go "add3" (\ (x :: Int) -> x + 3)

-- main = go "foo" (not . not)

-- main = go "foo" (\ (a,b :: Int) -> if a then b else b)

-- -- Equivalently: a `xor` not b
-- main = go "foo" (\ (a,b) -> if a then b else not b)

-- main = go "foo" (\ a  (b :: Int :* Int) -> (if a then id else swap) b)

-- main = goSep "foo" 2.5 (\ (a, b::Int, c::Int, d::Int) -> if a then (b,c,d) else (c,d,b))

-- main = go "foo" (\ a b -> ( if a then b else False --     a && b
--                           , if a then True  else b --     a || b
--                           , if a then False else b -- not a && b
--                           , if a then b else True  -- not a || b
--                           ))

-- -- Equivalently, (&& not a) <$> b
-- main = goSep "foo" 2 (\ a (b :: Vec N4 Bool) -> if a then pure False else b)

-- -- Equivalently, (|| a) <$> b
-- main = goSep "foo" 2 (\ a (b :: Vec N4 Bool) -> if a then pure True  else b)

-- -- Equivalently, (&& not a) <$> b
-- main = goSep "foo" 2 (\ a (b :: RTree N3 Bool) -> if a then pure False else b)

-- -- Equivalently, (a `xor`) <$> b
-- main = go "foo" (\ a (b :: Vec N3 Bool) -> (if a then not else id) <$> b)

-- main = goSep "foo" 2 (\ a (b :: RTree N2 Bool) -> (if a then reverse else id) b)

-- -- Equivalent to \ a -> (a,not a)
-- main = go "foo" (\ a -> if a then (True,False) else (False,True))

-- crcStep :: (Traversable poly, Applicative poly) =>
--            poly Bool -> poly Bool :* Bool -> poly Bool

-- main = goSep "crcStep-v1" 1
--         (crcStep :: Vec N1 Bool -> Vec N1 Bool :* Bool -> Vec N1 Bool)

-- -- ranksep: rt2=1, rt3=2, rt4=4.5
-- main = goSep "crcStep-rt3" 2 (crcStep :: RTree N3 Bool -> RTree N3 Bool :* Bool -> RTree N3 Bool)

-- main = go "crcStepK-rt2" (crcStep (polyD :: RTree N2 Bool))

-- main = goSep "crcStepK-g5" 1
--         (crcStep (ra5 True False False True False))

-- crc :: (Traversable poly, Applicative poly, Traversable msg) =>
--        poly Bool -> msg Bool :* poly Bool -> poly Bool

-- main = go "crc-v3v5" (crc :: Vec N3 Bool -> Vec N5 Bool :* Vec N3 Bool -> Vec N3 Bool)

-- main = go "crcK-v3v5" (crc polyD :: Vec N5 Bool :* Vec N3 Bool -> Vec N3 Bool)

-- main = go "crc-v4rt3" (crc :: Vec N4 Bool -> RTree N3 Bool :* Vec N4 Bool -> Vec N4 Bool)

-- main = go "crc-rt3rt5" (crc :: RTree N3 Bool -> RTree N5 Bool :* RTree N3 Bool -> RTree N3 Bool)

-- main = go "crcK-rt2rt4" (crc polyD :: RTree N4 Bool :* RTree N2 Bool -> RTree N2 Bool)

-- main = go "crcK-v5rt4" (crc polyD :: RTree N4 Bool :* Vec N5 Bool -> Vec N5 Bool)

-- main = go "crc-encode-v3v5" (crcEncode :: Vec N3 Bool -> Vec N5 Bool -> Vec N3 Bool)

-- main = go "crc-encode-v3rt2" (crcEncode :: Vec N3 Bool -> RTree N2 Bool -> Vec N3 Bool)

-- main = go "crc-encode-rt2rt4" (crcEncode :: RTree N2 Bool -> RTree N4 Bool -> RTree N2 Bool)

-- Simple carry-propagate adder

-- main = go "halfAdd" halfAdd

-- main = go "add1" add1

-- main = go "add1-0" (carryIn False add1)

-- main = go "add1p" add1'

-- main = go "adder-state-v3" (adderState :: Adder' (Vec N3))

-- main = go "adder-state-rt2" (adderState :: Adder' (RTree N2))

-- main = go "adder-state-0-v1" (carryIn False adderState :: Adder (Vec N1))

-- main = go "adder-state-0-rt0" (carryIn False adderState :: Adder (RTree N0))

-- -- GHC panic: "tcTyVarDetails b{tv ah8Z} [tv]"
-- main = go "adder-state-trie-v2" (adderStateTrie :: Adder' (Vec N2))

-- main = go "adder-accuml-v8" (adderAccumL :: Adder' (Vec N8))

-- main = go "adder-accuml-rt5" (adderAccumL :: Adder' (RTree N5))

-- Monoidal scan adders

-- main = go "gpCarry" gpCarry

-- main = go "mappend-gpr" (mappend :: Binop GenProp)

ifF :: Bool -> Binop a
ifF c a b = if c then a else b

-- main = go "if-gpr" (ifF :: Bool -> Binop GenProp)

-- main = go "gprs-pair" (fmap genProp :: Pair (Pair Bool) -> Pair GenProp)

-- main = go "scan-gpr-pair" (scanGPs :: Pair (Pair Bool) -> Pair GenProp :* GenProp)

-- main = go "adder-scan-pair" (scanAdd :: Adder Pair)

-- main = go "adder-scanp-pair" (scanAdd' :: Adder' Pair)

-- main = go "adder-scanpp-pair" (scanAdd'' :: Adder Pair)

-- -- Ranksep: rt1=0.5, rt2=0.5, rt3=0.75, rt4=1.5,rt5=2
-- main = goSep "adder-scan-noinline-rt2" 0.5 (scanAdd :: Adder (RTree N2))

-- -- Ranksep: rt1=0.5, rt2=0.5, rt3=0.75, rt4=1.5,rt5=2
-- main = goSep "adder-scan-rt5" 2 (scanAdd :: Adder (RTree N5))

-- -- Ranksep: rt2=0.5, rt3=0.75, rt4=1.5,rt5=2
-- main = goSep "adder-scan-unopt-rt0" 0.5 (scanAdd :: Adder (RTree N0))

-- -- Ranksep: rt2=0.5, rt3=1, rt4=2, rt5=3
-- main = goSep "adder-scanp-rt3" 1 (scanAdd' :: Adder' (RTree N3))

-- -- Ranksep: rt2=0.5, rt3=0.75, rt4=1.5,rt5=2
-- main = goSep "adder-scanpp-rt1" 0.5 (scanAdd'' :: Adder (RTree N1))

-- main = go "foo" (\ ((gx,px),(gy,py)) -> (gx || gy && px, px && py))

-- main = go "case-just" (\ case Just b  -> not b
--                               Nothing -> True)

-- -- Demos automatic commutation
-- main = go "foo" (\ (b,a) -> a || b)

-- main = go "or-with-swap" (\ (a,b) -> (a || b, b || a))

-- -- not (a && b)
-- main = go "foo" (\ b a -> not a || not b)

-- main = go "foo" (\ (a::Int,x::Bool) -> if x then (square a,True) else (bottom,False))

-- main = go "foo" (\ x -> if x then True else bottom)

-- main = go "foo" (bottom :: Bool)

-- main = go "foo" (bottom::Int,False)

-- main = go "foo" (bottom::Bool, bottom::Int, bottom::Bool)

-- main = go "foo" (\ x -> if x then bottom else bottom :: Bool)

-- main = goSep "if-maybe" 0.75 (\ a (b :: Maybe Bool) c -> if a then b else c)

-- main = go "fmap-maybe-square" (fmap square :: Unop (Maybe Int))

-- main = go "fmap-maybe-not" (fmap not :: Unop (Maybe Bool))

-- main = go "foo" (\ a b -> if b then (not a,True) else (bottom,False))

-- main = go "fromMaybe-bool" (fromMaybe :: Bool -> Maybe Bool -> Bool)

-- main = goSep "fromMaybe-v3" 1.5 (fromMaybe :: Vec N3 Bool -> Maybe (Vec N3 Bool) -> Vec N3 Bool)

-- main = goSep "liftA2-maybe" 0.8 (liftA2 (*) :: Binop (Maybe Int))

-- main = goSep "liftA3-maybe" 0.8 (liftA3 f :: Ternop (Maybe Int))
--  where
--    f x y z = x * (y + z)

-- main = goSep "liftA4-maybe" 0.8 (\ (a,b,c,d) -> liftA4 f a b c d :: Maybe Int)
--  where
--    f w x y z = (w + x) * (y + z)

-- main = go "lift-maybe-1-1a" h
--  where
--    h a = pure square <*> a :: Maybe Int

-- main = go "lift-maybe-1-1b" h
--  where
--    h a = liftA2 (*) a a :: Maybe Int

-- main = go "lift-maybe-1-1c-no-idem" h
--  where
--    h a = fmap square b :: Maybe Int
--     where
--       b = liftA2 (+) a a

-- main = go "lift-maybe-1-2" h
--  where
--    h a = liftA2 (*) a b :: Maybe Int
--     where
--       b = liftA2 (+) a a

-- main = goSep "lift-maybe-1-3" 1 h
--  where
--    h a = liftA3 f a b c :: Maybe Int
--     where
--       b = liftA2 (*) a a
--       c = liftA2 (+) b a
--       f w x y = (w + x) * y

-- main = goSep "lift-maybe-1-4" 0.8 h
--  where
--    h a = liftA4 f a b c d :: Maybe Int
--     where
--       b = liftA2 (*) a a
--       c = liftA2 (+) b a
--       d = liftA2 (*) c b
--       f w x y z = (w + x) * (y + z)

-- main = go "liftA2-justs" (\ (a,b) -> liftA2 (*) (Just a) (Just b) :: Maybe Int)

-- Sums

-- main = go "fmap-either-square" (fmap square :: Unop (Either Bool Int))

-- main = go "case-of-either" 
--          (\ case Left  x -> if x then 3 else 5 :: Int
--                  Right n -> n + 3)

-- -- ranksep 1.5 when unoptimized.
-- main = goSep "if-to-either" 1.5 
--         (\ a -> if a then Left 2 else Right (3,5) :: Either Int (Int,Int))

-- main = goSep "case-if-either" 1
--         (\ a -> let e :: Either Int (Int,Int)
--                     e = if a then Left 2 else Right (3,5)
--                 in
--                   case e of
--                     Left n      -> n + 5
--                     Right (p,q) -> p * q )

-- main = goSep "case-if-either-2" 1
--         (\ (a,b,c,d) -> let e :: Either Int (Int,Int)
--                             e = if a then Left b else Right (c,d)
--                 in
--                   case e of
--                     Left n      -> n + 5
--                     Right (p,q) -> p * q )

-- main = goSep "case-if-either-3" 1
--         (\ (a,b,c) -> let e :: Either Int (Int -> Int)
--                           e = if a then Left b else Right (b *)
--                 in
--                   case e of
--                     Left  n -> n + c
--                     Right f -> f c )

-- -- The conditionals vanish
-- main = goSep "case-if-either-3b" 0.7
--         (\ (a,b,c) -> let e :: Either Int (Int -> Int)
--                           e = if a then Left b else Right (b +)
--                 in
--                   case e of
--                     Left  n -> n + c
--                     Right f -> f c )

-- main = go "foo" (\ (a::Int,old) -> dup (old+a))

-- main = goM "foo" (Mealy (\ (a::Int,old) -> dup (old+a)) 0)

-- main = goM "mealy-sum-0" (Mealy (\ (a::Int,old) -> dup (old+a)) 0)

-- We can't yet handle examples built from the Arrow interface.

-- main = goM "mealy-sum-1" (m :: Mealy Int Int)
--  where
--    m :: Mealy Int Int
--    m = loop (arr (\ (a,tot) -> dup (tot+a)) . second (delay 0))

-- serialSum0 :: Mealy Int Int
-- serialSum0 = Mealy (\ (old,a) -> dup (old+a)) 0

-- serialSum1 :: Mealy Int Int
-- serialSum1 = loop (arr (\ (a,tot) -> dup (tot+a)) . second (delay 0))

-- main = goM "mealy-counter-exclusive" (Mealy (\ ((),n::Int) -> (n,n+1)) 0)

-- main = goM "mealy-counter-inclusive" (Mealy (\ ((),n::Int) -> dup (n+1)) 0)

-- main = goM "mealy-sum-exclusive" (Mealy (\ (a::Int,n) -> (n,n+a)) 0)

-- main = goM "mealy-sum-inclusive" (Mealy (\ (a::Int,n) -> dup (n+a)) 0)

-- -- Square of consecutive numbers, inclusive
-- main = goM "mealy-square-counter-inclusive"
--          (Mealy (\ ((),n::Int) -> let n' = n+1 in (square n',n')) 0)

-- -- Prefix sum of square of inputs
-- main = goM "mealy-square-sum-inclusive"
--          (Mealy (\ (a::Int,tot) -> dup (tot + square a)) 0)

-- Serial Fibonacci variants:

-- main = goM "serial-fibonacci-a" $
--          Mealy (\ ((),(a,b)) -> (a,(b,a+b))) (0::Int,1)

-- main = goM "serial-fibonacci-b" $
--          Mealy (\ ((),(a,b)) -> (b,(b,a+b))) (0::Int,1)

-- main = goM "serial-fibonacci-c" $
--          Mealy (\ ((),(a,b)) -> let c = a+b in (c,(b,c))) (0::Int,1)

-- main = goM "serial-fibonacci-a-11" $
--          Mealy (\ ((),(a,b)) -> (a,(b,a+b))) (1::Int,1)

-- main = go "foo" (sumSquare :: RTree N2 Int -> Int)

-- main = goM "sumSP-rt3" (Mealy (\ (as :: RTree N3 (Sum Int),tot) -> dup (fold as <> tot)) mempty)

-- main = goM "sumSP-rt4" (sumSP :: Mealy (RTree N4 Int) Int)

-- main = goM "foldSP-rt1" (foldSP :: Mealy (RTree N1 (Sum Int)) (Sum Int))

-- main = goM "sumSP-rt2" (sumSP :: Mealy (RTree N2 Int) Int)

-- -- Not yet.
-- main = goM "dotSP-rt2p" (dotSP :: Mealy (RTree N2 (Pair Int)) Int)

-- main = goM "dotSP-rt4p" (Mealy (\ (pas :: RTree N4 (Pair Int),tot) -> dup (dot'' pas + tot)) 0)

-- type GS a = (GenBuses a, Show a)

fullAdd :: Pair Bool :* Bool -> Bool :* Bool
fullAdd = add1' . swap
{-# INLINE fullAdd #-}

-- main = go "fullAdd" (add1' . swap) -- fullAdd -- fullAdd doesn't inline

adderS :: Bool -> Mealy (Pair Bool) Bool
adderS = Mealy (add1 . swap)

-- main = goM "adderS" (adderS False)

-- main = goMSep "sumS" 0.5 (sumS :: Mealy Int Int)

-- main = goMSep "sumS-rt3" 1.5 (sumS :: Mealy (RTree N3 Int) (RTree N3 Int))

-- main = goMSep "sumPS-rt1" 0.75 (sumPS :: Mealy (RTree N1 Int) Int)

-- main = goM "dotPS-rt3p" (m :: Mealy (RTree N3 (Pair Int)) Int)
--  where
--    m = Mealy (\ (ts,tot) -> let tot' = tot + fmap product ts in (sum tot',tot')) 0

-- main = goMSep "mac-p" 1 (mac :: Mealy (Pair Int) Int)

-- main = goMSep "mac-prt2" 1 (mac :: Mealy (Pair (RTree N2 Int)) (RTree N2 Int))

-- main = goM "sum-mac-prt1" (sumMac :: Mealy (Pair (RTree N1 Int)) Int)

matVecMultSA :: (Foldable f, Applicative f, Num a, GS (f a)) =>
                Mealy (f a) a
matVecMultSA =
  Mealy (\ (row,s@(started,vec)) ->
           if started then (row <.> vec, s) else (0, (True,row))) (False,pure 0)

matVecMultS :: (Foldable f, Applicative f, Num a, GS (f a)) =>
               Mealy (f a) a
matVecMultS =
  Mealy (\ (row,s@(started,vec)) ->
           (row <.> vec, if started then s else (True,row))) (False,pure 0)

-- main = goM "mat-vec-mult-rt1" (matVecMultS :: Mealy (RTree N1 Int) Int)

-- main = goM "mat-vec-mult-rt1" (m :: Mealy (RTree N1 Int) Int)
--  where
--    m = Mealy (\ (row,mbVec) -> case mbVec of
--                                  Nothing -> (0,Just row)
--                                  Just v  -> (row <.> v, mbVec)) Nothing

-- main = goMSep "mat-vec-mult-a-rt3" 1 (m :: Mealy (RTree N3 Int) Int)
--  where
--    m = Mealy (\ (row,s@(started,vec)) ->
--                 if started then (row <.> vec, s) else (0, (True,row))) (False,pure 0)

-- -- 3:1, 4:1.5, 5:2
-- main = goMSep "mat-vec-mult-b-rt2" 1 (m :: Mealy (RTree N2 Int) Int)
--  where
--   m = Mealy (\ (row,s@(started,vec)) ->
--                (row <.> vec, if started then s else (True,row))) (False,pure 0)

-- -- Type error with MealyAsFun in Run
-- -- Same result as -b
-- main = goMSep "mat-vec-mult-c-rt2" 1 (m :: Mealy (RTree N2 Int) Int)
--  where
--   m = Mealy (\ (row,s@(started,vec)) ->
--                (row <.> vec, if started then s else (not started,row))) (False,pure 0)

-- main = goSep "get-p" 1 (P.get :: Bool -> Pair Int -> Int)

type Bits n = Vec n Bool

-- -- 3:1, 4:2, 5:3
-- main = goSep "get-rt5" 3 (RT.get :: Bits N5 -> RTree N5 Int -> Int)

-- -- 3:1, 4:2, 5:3
-- main = goSep "get-ib-rt3" 1 (RT.get :: Bits N3 -> RTree N3 (Int,Bool) -> (Int,Bool))

-- -- 3:1, 4:2, 5:3
-- main = goSep "get-lt4" 2 (LT.get :: Bits N4 -> LTree N4 Int -> Int)

-- main = go "update-p" (flip P.update (+2) :: Bool -> Pair Int -> Pair Int)

-- main = go "update-plus2-p" (\ (b,p::Pair Int) -> P.update b (+2) p)

-- main = go "update-not-p" (\ (b,p) -> P.update b not p)

-- -- 1:0.75, 2:1.5, 3:3, 4:8
-- main = goSep "update-plus2-rt1" 0.75 (\ (v,t::RTree N1 Int) -> RT.update v (+2) t)

-- -- 2:1.5, 3:3, 4:4
-- main = goSep "update-not-rt2" 1.5 (\ (v,t::RTree N2 Bool) -> RT.update v not t)

histogramStep ::  Num a => RTree n a -> Bits n -> RTree n a
histogramStep t v = RT.update v (+1) t

-- -- 1:2, 2:2, 3:2
-- main = goSep "histogramStep-3" 2 (histogramStep :: RTree N3 Int -> Bits N3 -> RTree N3 Int)

-- Combinational histogram
histogramP :: (Foldable f, IsNat n) => f (Bits n) -> RTree n Int
histogramP = foldl histogramStep (pure 0)
-- histogramP = foldl (\ t v -> RT.update v (+1) t) (pure 0)

-- -- 2-3:1, 3-4:?
-- main = goSep "histogramP-2-rt3" 1 (histogramP :: RTree N3 (Bits N2) -> RTree N2 Int)

oneTree :: (IsNat n, Num a) => Bits n -> RTree n a
oneTree = histogramStep (pure 0)

-- -- 1:0.5, 2:0.75, 3:1.5
-- main = goSep "one-c-rt1" 0.5 (oneTree :: Bits N1 -> RTree N1 Int)

oneTree' :: IsNat n => Bits n -> RTree n Bool
oneTree' v = RT.update v (const True) (pure False)

-- -- 1:0.75, 2:1.5, 3:2
-- main = goSep "onep-rt3" 2 (oneTree' :: Bits N3 -> RTree N3 Bool)

oneTree'' :: IsNat n => Bits n -> RTree n Int
oneTree'' v = boolToInt <$> oneTree' v

-- -- 1:0.5, 2:0.75, 3:1.5
-- main = goSep "onepp-rt3" 1.5 (oneTree'' :: Bits N3 -> RTree N3 Int)

-- As I hoped, oneTree'' gives identical results to oneTree.

histogramFold :: (Foldable f, Functor f, IsNat n) => f (Bits n) -> RTree n Int
histogramFold = sum . fmap oneTree

-- main = goSep "histogramFold-1-v5" 1 (histogramFold :: Vec N5 (Bits N1) -> RTree N1 Int)

-- -- 1,2:0.75; 2,3:1.5
-- main = goSep "histogramFold-1-rt2" 0.75 (histogramFold :: RTree N2 (Bits N1) -> RTree N1 Int)

histogramFold'' :: (Foldable f, Functor f, IsNat n) => f (Bits n) -> RTree n Int
histogramFold'' = sum . fmap oneTree''

-- -- 1,2:1, 2,3:1.5
-- main = goSep "histogramFoldpp-1-rt2" 0.5 (histogramFold'' :: RTree N2 (Bits N1) -> RTree N1 Int)

-- Serial histogram
histogramS :: (IsNat n, GS (RTree n Int)) => Mealy (Bits n) (RTree n Int)
histogramS = scanl histogramStep (pure 0)
-- histogramS = scanl (\ t v -> RT.update v (+1) t) (pure 0)

-- -- 1:0.5, 2:1, 3:3
-- main = goMSep "histogramS-1" 0.75 (histogramS :: Mealy (Bits N1) (RTree N1 Int))

-- main = go "pure-sum-rt3" (\ a -> sum (pure a :: RTree N3 Int))

-- main = go "pure-1-sum-rt3" (sum (pure 1 :: RTree N3 Int))

-- main = go "foo" True

-- Step via oneTree''
histogramStepO ::  IsNat n => RTree n Int -> Bits n -> RTree n Int
histogramStepO t v = t + oneTree'' v

-- -- 1:0.5;2:0.75;3:1
-- main = goSep "histogramStepO-3" 1 (histogramStepO :: RTree N3 Int -> Bits N3 -> RTree N3 Int)

-- Serial histogram
histogramSO :: (IsNat n, GS (RTree n Int)) => Mealy (Bits n) (RTree n Int)
histogramSO = scanl histogramStepO (pure 0)

-- -- 1:0.5, 2:0.75, 3:1
-- main = goMSep "histogramSO-2" 0.5 (histogramSO :: Mealy (Bits N2) (RTree N2 Int))

-- More CRC

-- crcS :: (GS (poly Bool), Applicative poly, Traversable poly) =>
--         Mealy Bool (poly Bool, Int)

-- main = goM "crcS-rt0" (crcS :: Mealy Bool (RTree N0 Bool, Int))

-- main = goM "adderS" (adderS False)

-- main = goM "mealy-counter-exclusive" (Mealy (\ ((),n::Int) -> (n,n+1)) 0)

-- main = go "sumSquare-rt2" (sumSquare :: RTree N2 Int -> Int)

-- main = goMSep "sumPS-rt4" 1 (m :: Mealy (RTree N4 Int) Int)
--  where
--    m = Mealy (\ (t,tot) -> let tot' = tot+t in (sum tot',tot')) 0

-- Explicit delay and loop

-- main = goNew "delay-false" (delay False)

-- main = goNew "delay-01" (delay (0::Int,1::Int))

-- main = goNew "foo" (loop (\ (a::Int,s::Bool) -> (a,s)))

-- -- <<loop>
-- main = goNew "foo" (loop (\ ((),n::Int) -> dup (n+1)))

-- main = goNew "foo" (loop ((\ ((),(a,b)) -> (a,(b,a+b))) . second (delay (0::Int,1))))

-- main = goNew "fibS" fibS
--  where
--   fibS :: () -> Int
--   fibS = loop ((\ ((),(a,b)) -> (a,(b,a+b))) . second (delay (0,1)))

-- main = goNew "foo" (loop (\ ((),((),())) -> ((),((),()))))

-- fibS :: Num a => () -> a
-- fibS = loop ((\ ((),(a,b)) -> (a,(b,a+b))) . second (delay (0,1)))

-- main = goNew "foo" (Mealy.asFun (Mealy (\ ((),(a,b)) -> (a,(b,a+b))) (0::Int,1)))

fibM :: MStream Int
fibM = Mealy (\ ((),(a,b)) -> (a,(b,a+b))) (0::Int,1)

-- main = goM "foo" fibM

-- main = goNew "foo" (asFun fibM)

-- main = goM "foo" fibM

-- main = goM "fib-iteratep" (fst <$> iterateU' (\ (a,b) -> (b,a+b)) (0::Int,1))

-- main = go "comparisons"
--         (\ (x::Int,y::Int) -> (x==y || x/=y) && (x<y || x>=y) && (x>y || x<=y))

-- main = go "loop-id" (loop (\ (a::Bool,b::Int) -> (a,b)))

-- main = go "loop-const" (loop (\ (a::Bool,_b::Int) -> (a,3)))

-- main = go "loop-free-state-a" (loop (\ (a::Int,b::Int) -> (b > a,3)))

-- main = go "loop-free-state-b" (loop (\ (a::Int,b::Int) -> (b > a,a)))

-- -- "<<loop>"
-- main = go "loop-oops-a" (loop (\ (a::Int,b::Int) -> (b > a,b+1)))

-- main = goM "foo" (Mealy swap 0 :: Mealy (RTree N3 Int) (RTree N3 Int))

-- Like 'shiftR' but drop the value pushed out the left, and uncurry.
shiftR' :: Traversable t => t a -> a -> t a
shiftR' = curry (snd . shiftR)
-- shiftR' as a = snd (shiftR (as,a))

-- Serial
crcS' :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
         Mealy Bool (poly Bool)
crcS' = Mealy h (pure False, pure False,0)
 where
   p = sizeA (undefined :: poly ())
   h :: MealyFun (poly Bool, poly Bool, Int) Bool (poly Bool)
   h (b,(poly,seg,i)) = (stepped,(poly',seg',i'))
    where
      stash q = shiftR' q b
      starting = i < 2*p
      i' = if starting then i+1 else i
      stepped = crcStep poly (seg,b)
      (poly',seg')
        | i < p     = (stash poly,seg)
        | starting  = (poly,stash seg)
        | otherwise = (poly,stepped)

-- Can I use step instead of stash for seg?

-- main = goM "crcS-rt1" (crcS :: Mealy Bool (RTree N1 Bool))

-- main = goM "crcSK-v1" (crcSK poly :: Mealy Bool (Vec N1 Bool))
--  where
--    poly = vec1 True

-- Serial with static polynomial
crcSKa :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKa poly = fst <$> scanl h (pure False,0)
 where
   p = sizeA (undefined :: poly ())
   h (seg,i) b | i < p     = (shiftR' seg b, i+1)
               | otherwise = (crcStep poly (seg,b), i)

-- main = goM "crcSKa-v1" (crcSKa polyD :: Mealy Bool (Vec N1 Bool))

-- main = goM "crcSKa-rt0" (crcSKa polyD :: Mealy Bool (RTree N0 Bool))

-- main = go "foo" (fmap not :: Unop (RTree N2 Bool))

shiftLS :: (Traversable f, GS (f a)) => f a -> Mealy a a
shiftLS = Mealy (swap . shiftL)

shiftRS :: (Traversable f, GS (f a)) => f a -> Mealy a a
shiftRS = Mealy (shiftR . swap)

-- Types:
-- 
--   shiftL :: (a, f a) -> (f a, a)
--   swap . shiftL :: (a, f a) -> (a, f a)
-- 
--   shiftR :: (f a, a) -> (a, f a)
--   shiftR . swap :: (a, f a) -> (a, f a)

-- main = goM "shiftL-v3"  (shiftLS (pure False :: Vec N3 Bool))

-- main = goM "shiftR-v3"  (shiftRS (pure False :: Vec N3 Bool))

-- main = goM "shiftL-iota-v3"  (shiftLS (V.iota :: Vec N3 Int))

-- main = goM "shiftR-iota-v3"  (shiftRS (V.iota :: Vec N3 Int))

-- main = goM "shiftL-iota-rt2"  (shiftLS (iota :: RTree N2 Int))

-- main = goM "shiftRS-rt3" (shiftRS (pure False :: RTree N3 Bool))

-- main = goM "shiftR-ib-v3"  (shiftRS (pure (0,False) :: Vec N3 (Int,Bool)))

-- To simplify the circuit, output stepped even when i<p.
-- We expect the user to ignore this initial output either way.
crcSKb :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKb poly = Mealy h (pure False,0)
 where
   p = sizeA (undefined :: poly ())
   h (b,(seg,i)) = (stepped,next)
    where
      stepped = crcStep poly (seg,b)
      next | i < p     = (shiftR' seg b, i+1)
           | otherwise = (stepped, i)

-- main = goM "crcSKb-rt2" (crcSKb polyD :: Mealy Bool (RTree N2 Bool))

-- In this version, advance i even when i>=p, to shorten critical path.
-- WARNING: don't use for messages of length >= 2^32.
crcSKc :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKc poly = Mealy h (pure False,0)
 where
   p = sizeA (undefined :: poly ())
   h (b,(seg,i)) = (stepped,(seg',i+1))
    where
      stepped = crcStep poly (seg,b)
      seg' | i < p     = shiftR' seg b
           | otherwise = stepped

-- main = goM "crcSKc-rt0" (crcSKc polyD :: Mealy Bool (RTree N0 Bool))

crcSKd :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKd poly = Mealy h (pure False)
 where
   h (b,seg) = dup stepped
    where
      stepped = crcStep poly (seg,b)

-- Rewrite via Mealy scanl

crcSKe :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKe poly = scanl (curry (crcStep poly)) (pure False)

-- main = goM "crcSKe-rt4" (crcSKe polyD :: Mealy Bool (RTree N4 Bool))

-- Local curried version of crcStep

crcSKf :: forall poly. (GS (poly Bool), Applicative poly, Traversable poly) =>
          poly Bool -> Mealy Bool (poly Bool)
crcSKf poly = scanl step (pure False)
 where
   step seg b0 = if b0' then liftA2 xor poly seg' else seg'
    where
      (b0',seg') = shiftR (seg,b0)

-- main = goM "crcSKf-rt2" (crcSKf polyD :: Mealy Bool (RTree N2 Bool))

boolToChar :: Bool -> Char
boolToChar False = '0'
boolToChar True  = '1'

writeFile' :: FilePath -> String -> IO ()
writeFile' fname str = writeFile fname str >> putStrLn ("Wrote " ++ fname)

crcFileName :: String -> Int -> Int -> String
crcFileName = printf "../test/out/crc-bits-%s-%d-%d.txt"

genCrcIn :: Nat d -> Int -> IO ()
genCrcIn nd n =
  do ins <- ( ++ replicate d False) <$>
            generate (vectorOf (n - d) (arbitrary :: Gen Bool))
     writeFile' (crcFileName "ina" d n) (show ins)
     writeFile' (crcFileName "inb" d n) (unlines $ (pure . boolToChar) <$> ins)
 where
   d = natToZ nd

genCrcOut :: forall d. (IsNat d, GenBuses (RTree d Bool), PolyD (RTree d)) =>
             Nat d -> Int -> IO ()
genCrcOut nd n =
  do ins <- read <$> readFile (crcFileName "ina" d n)
     let outs = reverse <$> runMealy (crcSKf (polyD :: RTree d Bool)) ins
     writeFile' (crcFileName "outa-f" d n) (show outs)
     writeFile' (crcFileName "outb-f" d n)
       (unlines $ (map boolToChar . toList) <$> outs)
 where
   d = natToZ nd

-- main = genCrcIn d n
--  where
--    d = nat :: Nat N5
--    n = 4096

-- main = genCrcOut d n
--  where
--    d = nat :: Nat N5
--    n = 4096

-- main = goM "foo" (foo :: MStream (RTree N0 Bool))

-- Sequential-of-parallel
crcSPK :: (GS (poly Bool), Applicative poly, Traversable poly, Foldable chunk) =>
          poly Bool -> Mealy (chunk Bool) (poly Bool)
crcSPK poly = scanl (foldl step) (pure False)
 where
   step seg b0 = if b0' then liftA2 xor poly seg' else seg'
    where
      (b0',seg') = shiftR (seg,b0)

-- main = goM "crcSPK-rt3-rt2" (crcSPK polyD :: Mealy (RTree N3 Bool) (RTree N2 Bool))

crcP :: (Applicative poly, Traversable poly, Foldable msg) =>
        poly Bool -> msg Bool -> poly Bool
crcP poly = foldl step (pure False)
 where
   step seg b0 = if b0' then liftA2 xor poly seg' else seg'
    where
      (b0',seg') = shiftR (seg,b0)

-- -- 1,2: 0.5; 2,2: 0.75; 3,2: 1;
-- main = goSep "crcPK-rt3-rt2" 1 (crcP polyD :: RTree N3 Bool -> RTree N2 Bool)

matMatMultS :: (GS (f a), Foldable f, Applicative f, Num a) => Mealy (Bool, f a) a
matMatMultS = Mealy h (pure 0)
 where
   h ((new,w),row) = (row <.> w, if new then w else row)

-- -- 2:0.75; 3:1.0; 4:1.5, 5:2.5
-- main = goMSep "matMatMultS-rt4" 1.5 (matMatMultS :: Mealy (Bool, RTree N4 Int) Int)

-- main = go "foo" (\ (a,b::Int,c::Int) -> if not a then b else c)

revRT :: (IsNat n, Ord a) => Unop (RT.Tree n a)
revRT = RT.butterfly reverse

-- -- Butterfly swap, i.e., reversal
-- -- 1:0.5,2:1,3:2
-- main = goSep "butterfly-swap-rt2" 1 (revRT :: Unop (RTree N2 Bool))

-- main = goSep "sortP" 0.75 (sortP :: Unop (Pair Int))

-- -- 2,3,4:0.75
-- main = goSep "bitonic-3" 0.75 (bsort :: Unop (RTree N3 Int))

-- mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)

iotaT :: (Traversable t, Applicative t, Num a) => t a
iotaT = snd (mapAccumL (\ n () -> dup (n+1)) 0 (pure ()))

iotaT4 :: RTree N4 Int
iotaT4 = iotaT

-- main = go "foo" (True,3 :: Int)

-- main = go "foo" (True,iotaT :: RTree N1 Int)

-- -- Evokes unboxed Int, which the reifier can't handle.
-- main = go "foo" (min 3 :: Int -> Int)

-- main = go "foo" (||)

-- main = go "foo" (\ a b c -> a || b && c)

-- main = goM "foo" (scanl (\ b () -> not b) True)

-- main = goM "foo" (scanl (\ (a,b) () -> (b,a)) (True,False))

-- main = goM "iterate-not" (iterateU not False)

-- main = goM "foo" (iterateU swap (True,False))

-- main = goM "foo" (snd <$> iterateU swap (True,False))

-- Recursive.
-- main = goM "foo" (iterateU rotateR iotaT4)
-- main = goM "foo" (iterateU rotateR (vec1 True))
-- main = go "foo" (rotateR :: Unop (Vec N1 Bool))

-- main = goM "sumS" (sumS :: Mealy Int Int)

-- main = goM "double-sumS" (double (sumS :: Mealy Int Int))

-- main = goM "double-2-sumS" (double (double (sumS :: Mealy Int Int)))

-- main = goM "countS" (iterateU (+1) (0 :: Int))

-- main = go "foo" (RS.oneTree :: Bits N2 -> RTree N2 Int)

-- -- 1,2:0.75; 2,3:1.5; 1,4:0.75
-- main = goSep "histogramFold-1-4" 1.5 (RS.histogramFold :: RTree N4 (Bits N1) -> RTree N1 Int)

-- -- 1,2:0.75; 2,3:1.5; 1,4:1.5
-- main = goSep "histogramScan-1-4" 1.5 (RS.histogramScan :: RTree N4 (Bits N1) -> (RTree N4 (RTree N1 Int), RTree N1 Int))

-- -- 1,2:0.5; 2,3:2; 1,4:1.5
-- main = goSep "countSortPermutation-1-4" 1.5 (RS.positions :: RTree N4 (Bits N1) -> RTree N4 Int)

-- -- 1,2:0.5; 2,3:2; 1,4:1.5
-- main = goSep "countSortPermutationp-1-2" 0.5 (RS.positions :: RTree N2 (Bits N1) -> RTree N2 Int)


{--------------------------------------------------------------------
    Polynomial evaluation
--------------------------------------------------------------------}

powers :: (LScan f, Applicative f, Num a) => a -> f a
powers = fst . lproducts . pure

-- -- 1,2:0.5,3:1; 4:1.5; 5:2;
-- main = goSep "powers-rt4" 1.5 (powers :: Int -> RTree N4 Int)

-- -- 1,2:0.5,3:1; 4:1.5; 5:2;
-- main = goSep "powers-lt4" 1.5 (powers :: Int -> LTree N4 Int)

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "foo-rt3" (3/2) (fst . lproducts :: Unop (RTree N3 Int))

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "foo-lt3" (3/2) (fst . lproducts :: Unop (LTree N3 Int))

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "bar-rt3" (3/2) (fst . lproducts . pure :: Int -> RTree N3 Int)

-- -- 2:1; 3:1.5; 4:2; 5:2.5
-- main = goSep "bar-lt3" (3/2) (fst . lproducts . pure :: Int -> LTree N3 Int)


evalPoly :: (LScan f, Applicative f, Foldable f, Num a) => f a -> a -> a
evalPoly coeffs x = coeffs <.> powers x

-- -- -- 1,2:0.5,3:1; 4:2; 5:3;
-- main = goSep "evalPoly-rt4" 2 (evalPoly :: RTree N4 Int -> Int -> Int)

-- -- 1,2:0.5,3:1; 4:2; 5:3;

-- main = goSep "evalPoly-lt5" 3 (evalPoly :: LTree N5 Int -> Int -> Int)

-- Linear versions for comparison

#if 0
op :: b -> a -> b
e :: b
mapAccumL :: Traversable t => (b -> a -> (b, c)) -> b -> t a -> (b, t c)
(fmap.fmap) dup op :: b -> a -> (b,b)
mapAccumL ((fmap.fmap) dup op) e :: t a -> (b, t b)
swap . mapAccumL ((fmap.fmap) dup op) e :: t a -> (b, t b)
#endif

lproductsl :: (Traversable f, Num a) => f a -> (f a, a)
lproductsl = scanlT (*) 1

powersl :: (Traversable f, Applicative f, Num a) => a -> f a
powersl = fst . lproductsl . pure

-- main = go "powersl-rt3" (powersl :: Int -> RTree N3 Int)

evalPolyl :: (Traversable f, Applicative f, Foldable f, Num a) => f a -> a -> a
evalPolyl coeffs x = coeffs <.> powersl x

-- To do: switch `evalPolyl` to use a linear dot product, and retry.

-- main = go "evalPolyl-rt3" (evalPolyl :: RTree N3 Int -> Int -> Int)

-- Infix binary dot product, foldl version
infixl 7 `dotL`
dotL :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u `dotL` v = foldl (+) 0 (liftA2 (*) u v)

-- Infix binary dot product, foldr version
infixl 7 `dotR`
dotR :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u `dotR` v = foldr (+) 0 (liftA2 (*) u v)

-- main = go "dotl-rt3" (dotL :: RTree N3 Int -> RTree N3 Int -> Int)

-- main = go "dotr-rt3" (dotR :: RTree N3 Int -> RTree N3 Int -> Int)

evalPolyAddL :: (Traversable f, Applicative f, Foldable f, Num a) => f a -> a -> a
evalPolyAddL coeffs x = coeffs `dotL` powersl x

-- main = go "evalPolyAddL-rt3" (evalPolyAddL :: RTree N3 Int -> Int -> Int)

-- Serial version

-- First argument is a dummy, to allow inferring f.
-- Ignore the first p outputs, while the polynomial is loading.
evalPolyS :: forall f a. (GS (f a), LScan f, Traversable f, Applicative f, Num a) =>
             f () -> Mealy a a
evalPolyS _ = Mealy h (pure 0 :: f a,0)
 where
   p = sizeA (undefined :: f ())
   h (a,(poly,i)) = (evalPoly poly a,(poly',i+1))
    where
      poly' | i < p     = shiftR' poly a
            | otherwise = poly

-- main = goM "evalPolyS-rt5" (evalPolyS (undefined :: RTree N5 ()) :: Mealy Int Int)

-- Linear version
evalPolyAddLS :: forall f a. (GS (f a), LScan f, Traversable f, Applicative f, Num a) =>
               f () -> Mealy a a
evalPolyAddLS _ = Mealy h (pure 0 :: f a,0)
 where
   p = sizeA (undefined :: f ())
   h (a,(poly,i)) = (evalPolyAddL poly a,(poly',i+1))
    where
      poly' | i < p     = shiftR' poly a
            | otherwise = poly

-- main = goM "evalPolyAddLS-rt3" (evalPolyAddLS (undefined :: RTree N3 ()) :: Mealy Int Int)

evalPolyAddR :: (Traversable f, Applicative f, Foldable f, Num a) => f a -> a -> a
evalPolyAddR coeffs x = coeffs `dotR` powersl x

-- main = go "evalPolyAddR-rt3" (evalPolyAddR :: RTree N3 Int -> Int -> Int)

-- Linear version
evalPolyAddRS :: forall f a. (GS (f a), LScan f, Traversable f, Applicative f, Num a) =>
               f () -> Mealy a a
evalPolyAddRS _ = Mealy h (pure 0 :: f a,0)
 where
   p = sizeA (undefined :: f ())
   h (a,(poly,i)) = (evalPolyAddR poly a,(poly',i+1))
    where
      poly' | i < p     = shiftR' poly a
            | otherwise = poly

-- main = goM "evalPolyAddRS-rt3" (evalPolyAddRS (undefined :: RTree N3 ()) :: Mealy Int Int)

{--------------------------------------------------------------------
    Counters
--------------------------------------------------------------------}

-- main = go "lAlls-rt2" (lAlls :: Counter (RTree N2 Bool))

-- main = goSep "upL-rt3" 1 (upL :: Counter (RTree N3 Bool))

upL' :: (Applicative f, Traversable f) => Unop (f Bool)
upL' = fst . upL

-- main = goSep "upLp-rt3" 1 (upL' :: Unop (RTree N3 Bool))

-- main = goSep "upLp-2-rt2" 1 (upL' . upL' :: Unop (RTree N2 Bool))

-- main = goSep "nax-a" 1 (\ (a,b) -> not a && (a `xor` b))

upF' :: (Applicative f, LScan f) => Unop (f Bool)
upF' = fst . upF

-- main = goSep "upFp-rt3" 1 (upF' :: Unop (RTree N3 Bool))

-- main = goSep "upFp-2-rt1" 1 (upF' . upF' :: Unop (RTree N1 Bool))

-- main = goM "upCounterL-rt3" (upCounterL :: MStream (RTree N3 Bool))

-- -- 2:1, 3:2, 4:3
-- main = goSep "upF-rt2" (2-1) (upF :: Counter (RTree N2 Bool))

-- main = goM "upCounter-rt1" (upCounter :: MStream (RTree N3 Bool))

----

-- main = goM "foo" (scanl (\ _ () -> False) False)

-- main = goM "foo" (iterateU (const False) False)

-- main = go "delay-False-False" (delay False False)

-- main = go "foo" (scanlT (&&) True :: RTree N1 Bool -> (RTree N1 Bool, Bool))

-- upL bs = (liftA2 toggleIf alls bs, all')
--  where
--    (alls,all') = scanlT (&&) True bs

-- Question: Suppose I use adders, partially applied to 1.
-- Do I get the same circuits as with the up-counters?
-- Yes, as shown below.

-- type Adder  f =         f (Pair Bool) -> f Bool :* Bool
-- type Adder' f = Bool :* f (Pair Bool) -> f Bool :* Bool

-- Apply an Adder' to carry-in of 1 and a zero summand
adder'1 :: Functor f => Adder' f -> Counter f
adder'1 h bs = h (True, (False :#) <$> bs)

-- main = goSep "adder-state-c0-rt3" 1 (adder'1 adderState :: Counter (RTree N3))

-- -- GHC panic.
-- main = goSep "adder-state-trie-c0-rt3" 1 (adder'1 adderStateTrie :: Counter (RTree N3))

-- -- 2:1, 3:2, 4:3
-- main = goSep "scan-adder-c0-rt4" (4-1) (adder'1 scanAdd' :: Counter (RTree N4))

foldMap' :: (Foldable t, Monoid m) => (a -> m) -> t a -> m
foldMap' f = foldl (\ m a -> mappend (f a) m) mempty

-- foldMap' f = foldr (mappend . f) mempty

-- f :: a -> m
-- mappend . f :: a -> m -> m

-- \ a -> mappend (f a)
-- \ a m -> mappend (f a) m

-- \ m -> mappend m . f


-- foldMap' f = foldr (mappend . f) mempty

-- main = go "foo" (\ x y -> (x+y,x-y :: Complex Int))

-- main = go "foo" ((-) :: Binop (Complex Int))
-- main = go "foo" ((*) :: Binop (Complex Int))

-- main = go "foo" (+ negate (5 :: Int))

-- main = go "foo" (== (5 :: Int))

-- main = go "foo" (> (5 :: Int))

-- main = goSep "foo" 1.5 (\ (x :: Int) -> ((x+3,x-3,x*3,-x),(x==3,x>3)))

-- main = go "foo" (\ (x :: Int) -> (x+3,x==3))

-- main = go "foo" ((+) :: Binop Int)

-- main = go "foo" ((>) :: Int -> Int -> Bool)

-- main = go "foo" (\ (x :: Int) y -> (x + negate y, y - negate x))

-- main = go "foo" (negate . negate :: Unop Int)

-- main = go "foo" (negate . negate . negate . negate . negate :: Unop Int)

-- main = go "foo" (\ x (y :: Int) -> (x + negate y, negate x + y, x - negate y, negate x - y))

-- main = go "foo" (3.0 :: Double)

-- main = go "foo" (\ (x :: Double) -> x + 1)

-- main = go "foo" (\ (x :: Int) -> x + 1)

-- main = go "foo" ((+) :: Binop (Complex Double))

-- main = go "foo" ((*) :: Binop (Complex Double))

-- main = go "foo" ((+) :: Binop Double)

-- main = go "foo" ((+) :: Binop Int)

-- phasor :: (IsNat n, RealFloat a, Enum a) => Nat n -> RTree n (Complex a)
-- phasor n = scanlTEx (*) 1 (pure phaseDelta)
--     where phaseDelta = cis ((-pi) / 2 ** natToZ n)

-- main = go "foo" (phasor (nat :: Nat N1))

-- main = go "foo" (1 :: Complex Double)

-- main = go "foo" (fromInteger 1 :: Double)

-- main = go "foo" (fromIntegral :: Int -> Double)
