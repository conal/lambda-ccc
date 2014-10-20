{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment
{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds, GADTs #-}  -- for TU
{-# LANGUAGE LambdaCase #-}

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

import Prelude hiding (foldl,foldr,sum,product,zipWith,reverse,and,or)

import Data.Monoid (Monoid(..),Sum,Product)
import Data.Functor ((<$>))
import Control.Applicative -- (Applicative(..),liftA2,liftA3)
import Data.Foldable (Foldable(..),sum,product,and,or)
import Data.Traversable (Traversable(..))
import Data.Tuple (swap)
import Data.Maybe (fromMaybe,maybe)

-- transformers
import Data.Functor.Identity

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)
import TypeUnary.Vec hiding (transpose)

import LambdaCCC.Misc (dup,Unop,Binop,transpose,(:*))
import LambdaCCC.Adder

import Circat.Misc (Unop,Reversible(..))
import Circat.Rep (bottom)
import Circat.Pair (Pair(..))
import qualified Circat.RTree as RT
import qualified Circat.LTree as LT
import qualified Circat.RaggedTree as Ra
import Circat.RaggedTree (TU(..), R1, R2, R3, R4, R5, R8, R11, R13)
import Circat.Shift
import Circat.Scan
import Circat.Mealy
import Circat.Circuit (GenBuses,Attr,systemSuccess)

-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import Circat.Classes (IfT)
import LambdaCCC.Lambda (EP,reifyEP,xor)

import LambdaCCC.Run (run) -- go

-- Experiment for Typeable resolution in reification
import qualified Data.Typeable

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
no .@ mn = transpose ((no $@) <$> transpose mn)

{--------------------------------------------------------------------
    CRC
--------------------------------------------------------------------}

-- crcStep :: (Traversable t, Zippable t) =>
--            t Bool -> Bool -> Unop (Bool :* t Bool)

-- crcStep poly bit (s0,seg) = shiftR (seg',bit)
--  where
--    seg' = if s0 then zipWith xor poly seg else seg

-- crcStep poly bit (s0,seg) = shiftR (tweak seg,bit)
--  where
--    tweak = if s0 then zipWith xor poly else id

-- crcStep poly bit (s0, seg) =
--   shiftR ((if s0 then zipWith xor poly else id) seg, bit)

-- crcStep poly bit (s0, seg) =
--   shiftR (if s0 then zipWith xor poly seg else seg, bit)

-- Oops. The state should be just poly. Also, drop Zippable.

crcStep :: (Traversable poly, Applicative poly) =>
           poly Bool -> poly Bool :* Bool -> poly Bool
crcStep poly (shiftR -> (b0,seg')) = (if b0 then liftA2 xor poly else id) seg'

-- crcStep poly (shiftR -> (b0,seg')) = liftA2 tweak poly seg'
--  where
--    tweak c a = (b0 && c) `xor` a

#if 0
   tweak c a
== if b then (c `xor` a) else a
== if b then (c `xor` a) else (False `xor` a)
== (if b then c else False) `xor` a
== (b && c) `xor` a
#endif

-- crcStep poly (shiftR -> (b0,seg')) =
--   liftA2 (\ c a -> (b0 && c) `xor` a) poly seg'

-- crcStep poly (shiftR -> (b0,seg')) = liftA2 tweak poly seg'
--  where
--    tweak c a = (b0 && c) `xor` a

crc :: (Traversable poly, Applicative poly, Traversable msg) =>
       poly Bool -> msg Bool :* poly Bool -> poly Bool
crc poly = foldlQ (crcStep poly) . shiftRF

-- Equivalently,
--
-- crc poly (shiftRF -> (seg',msg')) = foldlQ (crcStep poly) (seg',msg')
--                                   = foldl (curry (crcStep poly)) seg' msg'

crcEncode :: (Traversable poly, Applicative poly, Traversable msg) =>
             poly Bool -> msg Bool -> poly Bool
crcEncode poly msg = crc poly (msg, pure False)

-- | Uncurried variant of 'foldl'
foldlQ :: Foldable f => (b :* a -> b) -> (b :* f a -> b)
foldlQ = uncurry . foldl . curry

-- Curried versions (for consideration):

crcStep' :: (Traversable poly, Applicative poly) =>
            poly Bool -> poly Bool -> Bool -> poly Bool
crcStep' poly seg b = (if b0 then liftA2 xor poly else id) seg'
 where
   (b0,seg') = shiftR (seg,b)

crc' :: (Traversable poly, Applicative poly, Traversable msg) =>
        poly Bool -> msg Bool -> poly Bool -> poly Bool
crc' poly msg pad = foldl (crcStep' poly) seg0 msg0
 where
   (seg0,msg0) = shiftRF (msg,pad)

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

go' :: GenBuses a => String -> [Attr] -> (a -> b) -> IO ()
go' name attrs f = run name attrs (reifyEP f)

go :: GenBuses a => String -> (a -> b) -> IO ()
go name f = run name [] (reifyEP f)

-- TODO: Try using go from Run instead. I was getting inlining failures earlier.

ranksep :: Double -> Attr
ranksep n = ("ranksep",show n)

goSep :: GenBuses a => String -> Double -> (a -> b) -> IO ()
goSep name s = go' name [ranksep s]

inTest :: String -> IO ()
inTest cmd = systemSuccess ("cd ../test; " ++ cmd) -- (I run ghci in ../src)

doit :: IO ()
doit = inTest "make"

make :: IO ()
make = systemSuccess "cd ../..; make"

figureSvg :: String -> IO ()
figureSvg str = systemSuccess ("cd ../test; ./figure-svg " ++ str)

latestSvg :: IO ()
latestSvg = systemSuccess "cd ../test; ./latest-svg"

do1 :: IO ()
do1 = inTest "hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTreeNoReify.hss"

do2 :: IO ()
do2 = inTest "hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTree.hss"

-- Only works when compiled with HERMIT
main :: IO ()

-- main = go "map-not-v5" (fmap not :: Vec N5 Bool -> Vec N5 Bool)

-- main = go "map-square-v5" (fmap square :: Vec N5 Int -> Vec N5 Int)

-- main = go "map-t3" (fmap not :: Unop (RTree N3 Bool))

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

-- main = goSep "pure-rt3" 1 (\ () -> (pure False :: RTree N3 Bool))

-- main = go "foo" (\ (_ :: RTree N3 Bool) -> False)

-- main = go "sum-p" (sum :: Pair Int -> Int)

-- main = go "sumSquare-p" (sumSquare :: Pair Int -> Int)

main = go "sumSquare-t3" (sumSquare :: RTree N3 Int -> Int)

-- main = go "sum-v8" (sum :: Vec N8 Int -> Int)

-- main = go "and-v5" (and :: Vec N5 Bool -> Bool)

-- main = go "sum-t2" (sum :: RTree N2 Int -> Int)

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

-- main = goSep "applyLin-v23" 1 (uncurry (($@) :: Matrix N2 N3 Int -> Vec N2 Int -> Vec N3 Int))

-- main = goSep "applyLin-v42" 1 (uncurry (($@) :: Matrix N4 N2 Int -> Vec N4 Int -> Vec N2 Int))

-- main = goSep "applyLin-v45" 1 (uncurry (($@) :: Matrix N4 N5 Int -> Vec N4 Int -> Vec N5 Int))

-- main = goSep [ranksep 2] -t21 (uncurry (($@) :: MatrixT N2 N1 Int -> RTree N2 Int -> RTree N1 Int))

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

-- -- Shift examples are identities on bit representations
-- main = go "shiftR-v4" (shiftR :: Vec N4 Bool :* Bool -> Bool :* Vec N4 Bool)

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

-- main = go "lsumsp-lt3" (lsums' :: Unop (LTree N3 Int))

-- main = go "lsums-rt5" (lsums :: RTree N5 Int -> (RTree N5 Int, Int))

-- main = go "lsums-lt2" (lsums :: LTree N2 Int -> (LTree N2 Int, Int))

-- main = go "foo" (\ a -> not a)

-- main = go "foo" not

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

-- main = go "applyLin-gt45" (uncurry (($@) :: MatrixG R4 R5 Int -> Ragged R4 Int -> Ragged R5 Int))

-- main = go "composeLin-gt234" (uncurry ((.@) :: MatrixG R3 R4 Int -> MatrixG R2 R3 Int -> MatrixG R2 R4 Int))

-- -- Linear map composition mixing ragged trees, top-down perfect trees, and vectors.
-- main = go "composeLin-gt3rt2v2"
--           (uncurry ((.@) :: Vec N2 (RTree N2 Int) -> RTree N2 (Ragged R3 Int) -> Vec N2 (Ragged R3 Int)))

-- main = go "composeLin-gt1rt0v1"
--           (uncurry ((.@) :: Vec N1 (RTree N0 Int) -> RTree N0 (Ragged R1 Int) -> Vec N1 (Ragged R1 Int)))

-- Note: some of the scan examples redundantly compute some additions.
-- I suspect that they're only the same *after* the zero simplifications.
-- These zero additions are now removed in the circuit generation back-end.

-- ranksep: 8=1.5, 11=2.5
-- main = goSep "lsumsp-gt3" =1.5 (lsums' :: Unop (Ragged Ra.R3 Int))

-- main = go "foo" (lsums' :: Unop (Ragged Ra.R3 Int))

-- main = go "add3" (\ (x :: Int) -> x + 3)

-- main = go "foo" (not . not)

-- main = go "foo" (\ (a,b :: Int) -> if a then b else b)

-- -- Equivalently: a `xor` not b
-- main = go "foo" (\ (a,b) -> if a then b else not b)

-- main = go "foo" (\ (a, (b :: Int :* Int)) -> (if a then id else swap) b)

-- main = goSep "foo" 2.5 (\ (a, b::Int, c::Int, d::Int) -> if a then (b,c,d) else (c,d,b))

-- main = go "foo" (\ (a,b) -> ( if a then b else False --     a && b
--                             , if a then True  else b --     a || b
--                             , if a then False else b -- not a && b
--                             , if a then b else True  -- not a || b
--                             ))

-- -- Equivalently, (&& not a) <$> b
-- main = goSep "foo" 2 (\ (a, b :: Vec N4 Bool) -> if a then pure False else b)

-- -- Equivalently, (|| a) <$> b
-- main = goSep "foo" 2 (\ (a, b :: Vec N4 Bool) -> if a then pure True  else b)

-- -- Equivalently, (&& not a) <$> b
-- main = goSep "foo" 2 (\ (a, b :: RTree N3 Bool) -> if a then pure False else b)

-- -- Equivalently, (a `xor`) <$> b
-- main = go "foo" (\ (a, b :: Vec N3 Bool) -> (if a then not else id) <$> b)

-- main = goSep "foo" 2 (\ (a, b :: RTree N2 Bool) -> (if a then reverse else id) b)

-- -- Equivalent to \ a -> (a,not a)
-- main = go "foo" (\ a -> if a then (True,False) else (False,True))

-- crcStep :: (Traversable poly, Applicative poly) =>
--            poly Bool -> poly Bool :* Bool -> poly Bool

-- main = goSep "crcStep-v4" 1
--         (uncurry (crcStep :: Vec N4 Bool -> Vec N4 Bool :* Bool -> Vec N4 Bool))

-- -- ranksep: rt2=1, rt3=2, rt4=4.5
-- main = goSep "crcStep-rt3" 2 (uncurry (crcStep :: RTree N3 Bool -> RTree N3 Bool :* Bool -> RTree N3 Bool))

polyV2 :: Vec N2 Bool
polyV2 = vec2 True False

polyV3 :: Vec N3 Bool
polyV3 = vec3 True False True

polyV4 :: Vec N4 Bool
polyV4 = vec4 True False False True

polyV5 :: Vec N5 Bool
polyV5 = polyV3 <+> polyV2

-- main = go "crcStepK-v4" (crcStep polyV4)

polyRT1 :: RTree N1 Bool
polyRT1 = RT.tree1 True False

polyRT2 :: RTree N2 Bool
polyRT2 = RT.tree2 True False False True

polyRT3 :: RTree N3 Bool
polyRT3 = RT.tree3 True False False True True False True False

polyRT4 :: RTree N4 Bool
polyRT4 = RT.tree4 True False False True True False True False
                   False True True False True False True False

-- main = goSep "crcStepK-rt3" 1 (crcStep polyRT3)

-- main = goSep "crcStepK-g5" 1
--         (crcStep (ra5 True False False True False))

-- crc :: (Traversable poly, Applicative poly, Traversable msg) =>
--        poly Bool -> msg Bool :* poly Bool -> poly Bool

-- main = go "crc-v3v5" (uncurry (crc :: Vec N3 Bool -> Vec N5 Bool :* Vec N3 Bool -> Vec N3 Bool))

-- main = go "crcK-v3v5" (crc polyV3 :: Vec N5 Bool :* Vec N3 Bool -> Vec N3 Bool)

-- main = go "crc-v4rt3" (uncurry (crc :: Vec N4 Bool -> RTree N3 Bool :* Vec N4 Bool -> Vec N4 Bool))

-- main = go "crc-rt3rt5" (uncurry (crc :: RTree N3 Bool -> RTree N5 Bool :* RTree N3 Bool -> RTree N3 Bool))

-- main = go "crcK-rt2rt4" (crc polyRT2 :: RTree N4 Bool :* RTree N2 Bool -> RTree N2 Bool)

-- main = go "crcK-v5rt4" (crc polyV5 :: RTree N4 Bool :* Vec N5 Bool -> Vec N5 Bool)

-- main = go "crc-encode-v3v5" (uncurry (crcEncode :: Vec N3 Bool -> Vec N5 Bool -> Vec N3 Bool))

-- main = go "crc-encode-v3rt2" (uncurry (crcEncode :: Vec N3 Bool -> RTree N2 Bool -> Vec N3 Bool))

-- main = go "crc-encode-rt2rt4" (uncurry (crcEncode :: RTree N2 Bool -> RTree N4 Bool -> RTree N2 Bool))

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

-- main = go "gpCarry" (uncurry gpCarry)

-- main = go "mappend-gpr" (uncurry (mappend :: Binop GenProp))

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
-- main = go "foo" (\ (b,a) -> not a || not b)

-- main = go "foo" (\ (a::Int,x::Bool) -> if x then (square a,True) else (bottom,False))

-- main = go "foo" (\ x -> if x then True else bottom)

-- main = go "foo" (\ () -> bottom :: Bool)

-- main = go "foo" (\ () -> (bottom::Int,False))

-- main = go "foo" (\ () -> (bottom::Bool, bottom::Int, bottom::Bool))

-- main = go "foo" (\ x -> if x then bottom else bottom :: Bool)

-- main = goSep "if-maybe" 0.75 (\ (a,b :: Maybe Bool,c) -> if a then b else c)

-- main = go "fmap-maybe-square" (fmap square :: Unop (Maybe Int))

-- main = go "fmap-maybe-not" (fmap not :: Unop (Maybe Bool))

-- main = go "foo" (\ (a,b) -> if b then (not a,True) else (bottom,False))

-- main = go "fromMaybe-bool" (uncurry (fromMaybe :: Bool -> Maybe Bool -> Bool))

-- main = goSep "fromMaybe-v3" 1.5 (uncurry (fromMaybe :: Vec N3 Bool -> Maybe (Vec N3 Bool) -> Vec N3 Bool))

-- main = goSep "liftA2-maybe" 0.8 (\ (a,b) -> liftA2 (*) a b :: Maybe Int)

-- main = goSep "liftA3-maybe" 0.8 (\ (a,b,c) -> liftA3 f a b c :: Maybe Int)
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

-- main = go "foo" (Mealy (\ (old,a::Int) -> dup (old+a)) 0)

-- main = go "foo" (\ (old,a::Int) -> dup (old+a))

-- main = go "foo" (Mealy (\ (old,a::Int) -> dup (old+a)) 0)
