{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitForAll, ConstraintKinds, FlexibleContexts #-}  -- For :< experiment
{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds, GADTs #-}  -- for TU

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

import Prelude hiding (foldl,foldr,sum,product,and,or,zipWith,reverse)

import Data.Monoid (Monoid(..),Sum,Product)
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)
import Data.Foldable (Foldable(..),sum,product,and,or)
import Data.Traversable (Traversable(..))
import Data.Tuple (swap)

-- transformers
import Data.Functor.Identity

import TypeUnary.TyNat
import TypeUnary.Nat (IsNat)
import TypeUnary.Vec hiding (transpose)

import LambdaCCC.Misc (Unop,Binop,transpose,(:*))
import LambdaCCC.Adder

import Circat.Misc (Unop,Reversible(..))
import Circat.Pair (Pair(..))
import qualified Circat.RTree as RT
import qualified Circat.LTree as LT
import qualified Circat.RaggedTree as Ra
import Circat.RaggedTree (TU(..))
import Circat.Shift
import Circat.Scan
import Circat.Circuit (GenBuses,Attrs,systemSuccess)

-- Strange -- why needed? EP won't resolve otherwise. Bug?
import qualified LambdaCCC.Lambda
import LambdaCCC.Lambda (EP,reifyEP,xor)

import LambdaCCC.Run (run) -- go

-- Experiment for Typeable resolution in reification
import qualified Data.Typeable

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

---- CRC

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


-- Utilities for constant structures

-- TypeUnary.Vec already defines vec1,...,vec8

rt0 :: a -> RT.Tree N0 a
rt0 = RT.L

rt1 :: a -> a -> RT.Tree N1 a
rt1 a b = RT.B (rt0 a :# rt0 b)

rt2 :: a -> a -> a -> a -> RT.Tree N2 a
rt2 a b c d = RT.B (rt1 a b :# rt1 c d)

rt3 :: a -> a -> a -> a -> a -> a -> a -> a -> RT.Tree N3 a
rt3 a b c d e f g h = RT.B (rt2 a b c d :# rt2 e f g h)

rt4 :: a -> a -> a -> a -> a -> a -> a -> a
    -> a -> a -> a -> a -> a -> a -> a -> a
    -> RT.Tree N4 a
rt4 a b c d e f g h i j k l m n o p =
  RT.B (rt3 a b c d e f g h :# rt3 i j k l m n o p)

lt0 :: a -> LT.Tree N0 a
lt0 = LT.L

lt1 :: a -> a -> LT.Tree N1 a
lt1 a b = LT.B (lt0 (a :# b))

lt2 :: a -> a -> a -> a -> LT.Tree N2 a
lt2 a b c d = LT.B (lt1 (a :# b) (c :# d))

lt3 :: a -> a -> a -> a -> a -> a -> a -> a -> LT.Tree N3 a
lt3 a b c d e f g h = LT.B (lt2 (a :# b) (c :# d) (e :# f) (g :# h))

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

ra1 :: a -> Ra.Tree R1 a
ra1 a = Ra.L a

ra2 :: a -> a -> Ra.Tree R2 a
ra2 a b = Ra.B (ra1 a) (ra1 b)

ra3 :: a -> a -> a -> Ra.Tree R3 a
ra3 a b c = Ra.B (ra2 a b) (ra1 c)

ra4 :: a -> a -> a -> a -> Ra.Tree R4 a
ra4 a b c d = Ra.B (ra2 a b) (ra2 c d)

ra5 :: a -> a -> a -> a -> a -> Ra.Tree R5 a
ra5 a b c d e = Ra.B (ra3 a b c) (ra2 d e)

ra8 :: a -> a -> a -> a -> a -> a -> a -> a -> Ra.Tree R8 a
ra8 a b c d e f g h = Ra.B (ra3 a b c) (ra5 d e f g h)

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

go' :: GenBuses a => String -> Attrs -> (a -> b) -> IO ()
go' name attrs f = run name attrs (reifyEP f)

go :: GenBuses a => String -> (a -> b) -> IO ()
go name f = run name [] (reifyEP f)

inTest :: String -> IO ()
inTest cmd = systemSuccess ("cd ../test; " ++ cmd) -- (I run ghci in ../src)

doit :: IO ()
doit = inTest "./test"

make :: IO ()
make = systemSuccess "cd ../..; make"

do1 :: IO ()
do1 = inTest "hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTreeNoReify.hss"

do2 :: IO ()
do2 = inTest "hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTree.hss"

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

-- main = go' "pure-rt3" [("ranksep","1")] (\ () -> (pure False :: RTree N3 Bool))

-- main = go "foo" (\ (_ :: RTree N3 Bool) -> False)

-- main = go "sum-p" (sum :: Pair Int -> Int)

-- main = go "sumSquare-p" (sumSquare :: Pair Int -> Int)

-- main = go "sumSquare-t3" (sumSquare :: RTree N3 Int -> Int)

-- main = go "sum-v5" (sum :: Vec N5 Int -> Int)

-- main = go "and-v5" (and :: Vec N5 Bool -> Bool)

-- main = go "sum-t2" (sum :: RTree N2 Int -> Int)

-- main = go "sum-foldl-v5" (foldl (+) 0 :: Vec N5 Int -> Int)

-- main = go "sum-foldr-v5" (foldr (+) 0 :: Vec N5 Int -> Int)

-- main = go "sum-foldl-t3" (foldl (+) 0 :: RTree N3 Int -> Int)

-- main = go "sum-foldr-t3" (foldr (+) 0 :: RTree N3 Int -> Int)

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

-- -- Shows an abandoned component
-- main = go "test-or-true-constant-fold" (\ a -> not a || True)

-- -- not a
-- main = go "test-xor-true-with-constant-fold" (\ a -> a `xor` True)

-- -- a
-- main = go "test-xor-false-with-constant-fold" (\ a -> a `xor` False)

-- main = go "fmap-gt1" (fmap not :: Unop (Ragged R1 Bool))

-- main = go "sum-gt5" (sum :: Ragged R5 Int -> Int)

-- main = go "sum-gt13p" (sum :: Ragged R13' Int -> Int)

-- main = go "dotsp-gt8" (dotsp :: Pair (Ragged R8 Int) -> Int)

-- main = go "applyLin-gt45" (uncurry (($@) :: MatrixG R4 R5 Int -> Ragged R4 Int -> Ragged R5 Int))

-- main = go "composeLin-gt234" (uncurry ((.@) :: MatrixG R3 R4 Int -> MatrixG R2 R3 Int -> MatrixG R2 R4 Int))

-- -- Linear map composition mixing ragged trees, top-down perfect trees, and vectors.
-- main = go "composeLin-gt3rt2v2"
--           (uncurry ((.@) :: Vec N2 (RTree N2 Int) -> RTree N2 (Ragged R3 Int) -> Vec N2 (Ragged R3 Int)))

-- Oops -- Core Lint error.
-- Simplifying

-- main = go "composeLin-gt1rt0v1"
--           (uncurry ((.@) :: Vec N1 (RTree N0 Int) -> RTree N0 (Ragged R1 Int) -> Vec N1 (Ragged R1 Int)))

-- Note: some of the scan examples redundantly compute some additions.
-- I suspect that they're only the same *after* the zero simplifications.

-- main = go "lsumsp-gt11" (lsums' :: Unop (Ragged R11 Int))

-- main = go "foo" (lsums' :: Unop (Ragged R3 Int))

-- main = go "add3" (\ (x :: Int) -> x + 3)

-- main = go "foo" (not . not)

-- main = go "foo" (\ (a,b :: Int) -> if a then b else b)

-- main = go "foo" (\ (a,b) -> if a then b else not b)

-- main = go "foo" (\ (a, (b :: Int :* Int)) -> (if a then id else swap) b)

-- main = go "foo" (\ (a, b::Int, c::Int, d::Int) -> if a then (b,c,d) else (c,d,b))

-- main = go "boo" (\ (a,b) -> ( if a then b else False
--                             , if a then True  else b
--                             , if a then False else b
--                             , if a then b else True ))

-- main = go "foo" (\ (a, b :: Vec N2 Bool) -> if a then pure False else b)

-- main = go "foo" (\ (a, b :: RTree N2 Bool) -> if a then pure False else b)

-- main = go "foo" (\ (a, b :: Vec N3 Bool) -> (if a then not else id) <$> b)

-- main = go "foo" (\ (a, b :: RTree N2 Bool) -> (if a then reverse else id) b)

-- -- Equivalent to \ a -> (a,not a)
-- main = go "foo" (\ a -> if a then (True,False) else (False,True))

-- crcStep :: (Traversable poly, Applicative poly) =>
--            poly Bool -> poly Bool :* Bool -> poly Bool

-- main = go "crcStep-v4" (uncurry (crcStep :: Vec N4 Bool -> Vec N4 Bool :* Bool -> Vec N4 Bool))

-- main = go "crcStep-rt3" (uncurry (crcStep :: RTree N3 Bool -> RTree N3 Bool :* Bool -> RTree N3 Bool))

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
polyRT1 = rt1 True False

polyRT2 :: RTree N2 Bool
polyRT2 = rt2 True False False True

polyRT3 :: RTree N3 Bool
polyRT3 = rt3 True False False True True False True False

polyRT4 :: RTree N4 Bool
polyRT4 = rt4 True False False True True False True False
              False True True False True False True False

-- main = go "crcStepK-rt3-unopt" (crcStep polyRT3)

-- main = go "crcStepK-g5" (crcStep (ra5 True False False True False))

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

-- Scan Adders

-- main = go "mappend-gpr" (uncurry (mappend :: Binop GenProp))

main = go "adder-rt2" (scanAdd :: Adder (RTree N2))

-- main = go "foo" (\ ((gy,py),(gx,px)) -> (gx || gy && px, px && py))

