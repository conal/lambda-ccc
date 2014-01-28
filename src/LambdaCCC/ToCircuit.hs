{-# LANGUAGE TypeOperators, GADTs, KindSignatures, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ToCircuit
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert from CCC form to a circuit
----------------------------------------------------------------------

module LambdaCCC.ToCircuit
  ( expToCircuit, cccToCircuit
  -- , PSourceJt(..), tyPSource, tyPSource2
  ) where

import Prelude hiding (id,(.),not,and,or,curry,uncurry)

import LambdaCCC.Ty
import LambdaCCC.Prim hiding (xor)
import LambdaCCC.CCC hiding ((&&&),(|||),second,(***))
import LambdaCCC.Lambda (E)
import LambdaCCC.ToCCC (toCCC)

import Circat.Circuit
import Circat.Category
import Circat.Classes

expToCircuit :: HasTy2 a b => E (a -> b) -> (a :> b)
expToCircuit = cccToCircuit . toCCC

#define TS (tyPSource -> PSource)
#define CP (cccPS -> (PSource, PSource))

cccToCircuit :: (a :-> b) -> (a :> b)

-- Category
cccToCircuit Id                 = id
cccToCircuit (g :. f)           = cccToCircuit g . cccToCircuit f
-- Primitives
cccToCircuit (Prim p)           = primToSource p
cccToCircuit k@(Const (LitP b)) | CP <- k
                                = constC b
cccToCircuit (Const p)          = constS (primToSource p) -- Combine
-- cccToCircuit (Const p)          = primToConst p
-- Product
cccToCircuit Exl                = exl
cccToCircuit Exr                = exr
cccToCircuit (f :&&& g)         = cccToCircuit f &&& cccToCircuit g
-- Coproduct
cccToCircuit k@Inl              | (_, TS :+ TS) <- cccTys k
                                = inlC
cccToCircuit k@Inr              | (_, TS :+ TS) <- cccTys k
                                = inrC
cccToCircuit k@(f :||| g)       | (TS :+ TS, TS) <- cccTys k
                                = cccToCircuit f |||* cccToCircuit g
-- Exponential
cccToCircuit Apply              = apply
cccToCircuit (Curry h)          = curry (cccToCircuit h)
cccToCircuit (Uncurry h)        = uncurry (cccToCircuit h)

cccToCircuit ccc = error $ "cccToCircuit: not yet handled: " ++ show ccc

#define TH (tyHasTy -> HasTy)

-- TODO: I don't know whether to keep add. We'll probably want to build it from
-- simpler pieces.
--
-- TODO: Maybe implement all primitives (other than exl & exr) with namedC. I
-- could even use this PrimC type in circat, though it'd be the first dependency
-- of circat on lambda-ccc.

-- Prove that IsSource (Pins a), IsSource (Pins b)
cccPS :: (a :-> b) -> (PSourceJt a, PSourceJt b)
cccPS = tyPSource2 . cccTys

{--------------------------------------------------------------------
    Prim conversion
--------------------------------------------------------------------}

primToSource :: forall t. HasTy t => Prim t -> Pins t
primToSource = flip toS typ
 where
   toS :: Prim t -> Ty t -> Pins t
   toS NotP  _                = not
   toS AndP  _                = curry and
   toS OrP   _                = curry or
   toS XorP  _                = curry xor
   toS ExlP  _                = exl
   toS ExrP  _                = exr
   toS PairP _                = curry id
   toS InlP  (_ :=> TS :+ TS) = inlC
   toS InrP  (_ :=> TS :+ TS) = inrC
   toS AddP  (_ :=> _ :=> TS) = curry (namedC "add")
   toS CondP (_ :=> t)        = condC t
   toS p _                    = error $ "primToSource: not yet handled: " ++ show p

condC :: Ty a -> (Bool :* (a :* a) :> a)
condC (u :* v) = condPair u v
condC TS       = muxC

condPair :: Ty a -> Ty b -> Bool :* ((a :* b) :* (a :* b)) :> (a :* b)
condPair a b = half a exl &&& half b exr
 where
   half :: Ty c -> (u :> c) -> (Bool :* (u :* u) :> c)
   half t f = condC t . second (f *** f)

-- condPair a b =
--   condC a . second (exl *** exl) &&& condC b . second (exr *** exr)

-- Here's a variation
#if 0
#if 0

primToConst :: forall a b. HasTy b => Prim b -> (a :> b)
primToConst p = toS p typ
 where
   toS :: Prim b -> Ty b -> (a :> b)
   toS (LitP b) TS            = constC    b
   toS NotP  _                = constFun  not
   toS AndP  _                = constFun2 and
   toS OrP   _                = constFun2 or
   toS XorP  _                = constFun2 xor
   toS ExlP  _                = constFun  exl
   toS ExrP  _                = constFun  exr
   toS PairP _                = constFun2 id
   toS InlP  (_ :=> TS :+ TS) = constFun  inlC
   toS InrP  (_ :=> TS :+ TS) = constFun  inrC
   toS AddP  (_ :=> _ :=> TS) = constFun2 (namedC "add")
   toS CondP (_ :=> t)        = constFun  (condC t)
   -- The rest are unreachable, but GHC doesn't know.
   toS InlP  _                = oops
   toS InrP  _                = oops
   toS AddP  _                = oops
   toS CondP _                = oops
   oops :: a :> b
   oops = error $ "primToSource: bad op/type: " ++ show (p, typ :: Ty b)

#else

primToConst :: forall a b. HasTy b => Prim b -> (a :> b)
primToConst p = toS p
 where
   tb = typ :: Ty b
   toS :: Prim b -> (a :> b)
   toS (LitP b) | TS <- tb            = constC    b
   toS NotP                           = constFun  not
   toS AndP                           = constFun2 and
   toS OrP                            = constFun2 or
   toS XorP                           = constFun2 xor
   toS ExlP                           = constFun  exl
   toS ExrP                           = constFun  exr
   toS PairP                          = constFun2 id
   toS InlP  | (_ :=> TS :+ TS) <- tb = constFun  inlC
   toS InrP  | (_ :=> TS :+ TS) <- tb = constFun  inrC
   toS AddP  | (_ :=> _ :=> TS) <- tb = constFun2 (namedC "add")
   toS CondP | (_ :=> t)        <- tb = constFun  (condC t)
   -- The rest are unreachable, but GHC doesn't know.
   toS InlP  = oops
   toS InrP  = oops
   toS AddP  = oops
   toS CondP = oops
   oops :: a :> b
   oops = error $ "primToSource: bad op/type: " ++ show (p,tb)

#endif

-- Yet another go

primToConst :: forall a b. HasTy b => Prim b -> (a :> b)
primToConst = flip toS typ
 where
   toS :: Prim b -> Ty b -> (a :> b)
   toS (LitP b) TS = constC b
   toS p (_ :=> _) = constFun (primToSource p)
   toS p t         = error $ "primToConst: bad (prim/type) combo: " ++ show (p,t)

#endif


{--------------------------------------------------------------------
    Proofs
--------------------------------------------------------------------}

-- | Judgment (proof) that @'IsSource' ('Pins' a)@
data PSourceJt :: * -> * where
  PSource :: IsSourceP a => PSourceJt a

-- TODO: shorter descriptive name

-- TODO: Consider a generic replacement for types like this one. Try the generic
-- Dict type from Edward K's "constraints" package. Replace PSourceJt t
-- with Dict (Pins t).

-- | Proof of @'IsSource' ('Pins' a)@ from @'Ty' a@
tyPSource :: Ty a -> PSourceJt a
tyPSource Unit       = PSource
tyPSource Bool       = PSource
tyPSource (TS :* TS) = PSource
tyPSource (TS :+ TS) = PSource
tyPSource ty         = error $ "tyPSource: Oops -- not yet handling " ++ show ty

-- TODO: a :=> b

tyPSource2 :: (Ty a,Ty b) -> (PSourceJt a, PSourceJt b)
tyPSource2 (a,b) = (tyPSource a,tyPSource b)

-- tyPSource2 = tyPSource *** tyPSource
