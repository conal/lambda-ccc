{-# LANGUAGE TypeOperators, TypeFamilies, ViewPatterns, TupleSections, CPP #-}
{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, ConstraintKinds, UndecidableInstances #-} -- for Uncurriable

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Adder
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Scan-based adder
----------------------------------------------------------------------

#define Testing

module LambdaCCC.Adder where

-- TODO: explicit exports

import Prelude hiding (mapM)

import Data.Monoid (Monoid(..))
import Control.Applicative (Applicative,liftA2,(<$>))
import Data.Traversable (Traversable(..))

-- import Control.Monad.Trans.State
import Control.Monad.State (MonadState(..),runState) -- mtl

#ifdef Testing
import TypeUnary.TyNat (N2,N4)
import TypeUnary.Vec (Vec,vec4)

import Circat.Misc (transpose)
import Circat.RTree (RTree)
import qualified Circat.RTree as RT
#endif

import Circat.Rep
import Circat.Scan
import Circat.Pair
import Circat.Shift (accumL)
import Circat.Category (OkayArr,Uncurriable(..))
import Circat.Classes (BottomCat(..),IfCat(..),repIf)
import Circat.Circuit (GenBuses(..),(:>),genBusesRep',delayCRep,tyRep,bottomRep)

import Circat.Misc (xor)

import LambdaCCC.Misc ((:*))
import LambdaCCC.StateTrie

type Adder t = t (Pair Bool) -> t Bool :* Bool

type Adder' t = Bool :* t (Pair Bool) -> t Bool :* Bool

-- NOTE: the INLINE pragmas below preserve the original definitions for
-- inlining. Otherwise, we sometimes get the GHC-optimized versions, in which
-- operations like 'not', '(&&)', and '(||)' have been inlined to conditionals.

{--------------------------------------------------------------------
    One-bit adders
--------------------------------------------------------------------}

halfAdd :: Pair Bool -> Bool :* Bool
halfAdd (a :# b) = (a `xor` b,a && b)
{-# INLINE halfAdd #-}

add1 :: Bool :* Pair Bool -> Bool :* Bool
add1 (ci, a :# b) = (s,co)
 where
   q  = a `xor` b
   s  = q `xor` ci
   co = (a && b) || (ci && q)
{-# INLINE add1 #-}

-- Equivalently,
add1' :: Bool :* Pair Bool -> Bool :* Bool
add1' (ci, ab) = (s',co || co')
 where
   (s ,co ) = halfAdd ab
   (s',co') = halfAdd (s :# ci)
{-# INLINE add1' #-}

-- accumL :: Traversable t => (a :* b -> c :* a) -> (a :* t b -> t c :* a)

{--------------------------------------------------------------------
    mapM
--------------------------------------------------------------------}

add1State :: MonadState Bool m => Pair Bool -> m Bool
add1State p = state (flip (curry add1) p)
{-# INLINE add1State #-}

adderSt :: (MonadState Bool m, Traversable t) =>
           (m (t Bool) -> Bool -> (t Bool, Bool)) -> Adder' t
adderSt run (ci,ps) = run (mapM add1State ps) ci
{-# INLINE adderSt #-}

adderState :: Traversable t => Adder' t
adderState = adderSt runState
{-# INLINE adderState #-}

adderStateTrie :: Traversable t => Adder' t
adderStateTrie = adderSt runStateTrie
{-# INLINE adderStateTrie #-}

{--------------------------------------------------------------------
    traverse-based
--------------------------------------------------------------------}

-- type Adder' t = Bool :* t (Pair Bool) -> t Bool :* Bool

-- sequenceA :: (Traversable t, Applicative f) => t (f a) -> f (t a)
-- traverse  :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)


{--------------------------------------------------------------------
    accum-based
--------------------------------------------------------------------}

adderAccumL :: Traversable t => Adder' t
adderAccumL = accumL add1
{-# INLINE adderAccumL #-}

-- Operationally (and denotationally) equivalent to adderState, unsurprisingly,
-- since they both use State.

{--------------------------------------------------------------------
    Scan-based
--------------------------------------------------------------------}

-- | Generate and propagate carries
data GenProp = GenProp { gpGen :: Bool, gpProp :: Bool }

type instance Rep GenProp = Bool :* Bool
instance HasRep GenProp where
  repr (GenProp g p) = (g,p)
  abst (g,p) = GenProp g p

-- MSB on left
instance Monoid GenProp where
  mempty = GenProp False True
  GenProp gy py `mappend` GenProp gx px =
    GenProp (gx || gy && px) (px && py)
  -- {-# INLINE mempty #-}
  -- {-# INLINE mappend #-}

genProp :: Pair Bool -> GenProp
genProp (a :# b) = GenProp (a && b) (a `xor` b)
-- {-# INLINE genProp #-}

gpCarry :: GenProp -> Bool -> Bool
gpCarry (GenProp g p) cin = g || p && cin -- TODO: consolidate with mappend
-- {-# INLINE gpCarry #-}

scanAdd :: (Applicative t, LScan t) => Adder t
scanAdd ts = (liftA2 h gprs cs, co)
 where
   gprs = genProp <$> ts
   (cs,co) = gpGen <*$> lscan gprs
   h (GenProp _ p) ci = p `xor` ci
-- {-# INLINE scanAdd #-}

-- Just for testing
scanGPs :: (Applicative t, LScan t) => t (Pair Bool) -> t GenProp :* GenProp
scanGPs ts = lscan (genProp <$> ts)
-- {-# INLINE scanGPs #-}

scanAdd' :: (Applicative t, LScan t) => Adder' t
scanAdd' (ci0,ts) = (liftA2 h gprs cs, co)
 where
   gprs = genProp <$> ts
   (cs,co) = flip gpCarry ci0 <*$> lscan gprs
   h (GenProp _ p) ci = p `xor` ci
-- {-# INLINE scanAdd' #-}

-- TODO: perhaps define a variant of lscan that takes an initial and tweaks all
-- values accordingly.

-- scanAdd via scanAdd'
scanAdd'' :: (Applicative t, LScan t) => Adder t
scanAdd'' = carryIn False scanAdd'

-- carryIn :: Bool -> Adder' t -> Adder t
carryIn :: c -> (c :* a -> b) -> a -> b
carryIn cin f = f . (cin,)

instance GenBuses GenProp where
  genBuses' = genBusesRep'
  delay = delayCRep
  ty = tyRep

instance BottomCat (:>) GenProp where bottomC = bottomRep

instance IfCat (:>) (Rep GenProp) => IfCat (:>) GenProp where ifC = repIf 

instance OkayArr k a GenProp => Uncurriable k a GenProp a GenProp where uncurries = id

--     Illegal constraint ‘OkayArr
--                           k a GenProp’ in a superclass/instance context
--       (Use UndecidableInstances to permit this)

-- Handy operations

(<$*>), mapr :: Functor t => (a -> b) -> (a :* t a) -> (b :* t b)
f <$*> (a,as) = (f a, f <$> as)
mapr = (<$*>)

(<*$>), mapl :: Functor t => (a -> b) -> (t a :* a) -> (t b :* b)
f <*$> (as,a) = (f <$> as, f a)
mapl = (<*$>)

#ifdef Testing

{--------------------------------------------------------------------
    Testing addition
--------------------------------------------------------------------}

v4a, v4b :: Vec N4 Bool
v4a = vec4 True False True True
v4b = vec4 True True False True

rt2a, rt2b :: RTree N2 Bool
rt2a = RT.tree2 True False True True
rt2b = RT.tree2 True True False True

-- type Adder' t = Bool :* t (Pair Bool) -> t Bool :* Bool

-- (elemsV [False,False,False,True],True)
addStateV4F :: Vec N4 Bool :* Bool
addStateV4F = adderState (False,transpose (v4a :# v4b))

-- (elemsV [True,False,False,True],True)
addStateV4T :: Vec N4 Bool :* Bool
addStateV4T = adderState (True,transpose (v4a :# v4b))

addStateTrieV4F :: Vec N4 Bool :* Bool
addStateTrieV4F = adderStateTrie (False,transpose (v4a :# v4b))

addStateTrieV4T :: Vec N4 Bool :* Bool
addStateTrieV4T = adderStateTrie (True,transpose (v4a :# v4b))

-- (elemsV [False,False,False,True],True)
scanAddV4F :: RTree N2 Bool :* Bool
scanAddV4F = scanAdd' (False,transpose (rt2a :# rt2b))

-- (elemsV [True,False,False,True],True)
scanAddV4T :: RTree N2 Bool :* Bool
scanAddV4T = scanAdd' (True,transpose (rt2a :# rt2b))

#endif
