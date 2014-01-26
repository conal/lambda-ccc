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
import LambdaCCC.CCC hiding ((&&&),(|||))
import LambdaCCC.Lambda (E)
import LambdaCCC.ToCCC (toCCC)

import Circat.Circuit
import Circat.Category
import Circat.Classes

expToCircuit :: HasTy2 a b => E (a -> b) -> (a :> b)
expToCircuit = cccToCircuit . toCCC

cccToCircuit :: (a :-> b) -> (a :> b)
cccToCircuit k@(Prim CondP) | Just k' <- expand k = cccToCircuit k'
-- Category
cccToCircuit Id                       = id
cccToCircuit (g :. f)                 = cccToCircuit g . cccToCircuit f
-- Primitives
cccToCircuit (Prim ExlP)              = exl -- TODO: Drop the redundant Exl/ExlP ??
cccToCircuit (Prim ExrP)              = exr
cccToCircuit (Prim NotP)              = not
cccToCircuit (Uncurry (Prim AndP))    = and
cccToCircuit (Uncurry (Prim OrP))     = or
cccToCircuit (Uncurry (Prim XorP))    = xor
cccToCircuit k@(Uncurry (Prim AddP))  | (PSource, PSource) <- cccPS k
                                      = namedC "add"

-- Useful when CCC optimization is off
cccToCircuit (Uncurry (Prim PairP))   = id

cccToCircuit k@(Prim CondP)           | (PSource, PSource) <- cccPS k
                                      = namedC "mux"

cccToCircuit k@(Const (LitP b))       | (PSource, PSource) <- cccPS k
                                      = constC b
cccToCircuit (Const p)                = constS (primToSource p)
-- TODO: How to combine Const cases?
-- Product
cccToCircuit Exl                      = exl
cccToCircuit Exr                      = exr

cccToCircuit (f :&&& g)               = cccToCircuit f &&& cccToCircuit g
-- Coproduct
cccToCircuit k@Inl                    | (a, _ :+ b) <- cccTys k
                                      , PSource <- tyPSource a
                                      , PSource <- tyPSource b
                                      = inlC
cccToCircuit k@Inr                    | (b, a :+ _) <- cccTys k
                                      , PSource <- tyPSource a
                                      , PSource <- tyPSource b
                                      = inrC
cccToCircuit k@(f :||| g)             | (a :+ b, c) <- cccTys k
                                      , PSource <- tyPSource a
                                      , PSource <- tyPSource b
                                      , PSource <- tyPSource c
                                      = cccToCircuit f |||* cccToCircuit g
-- Exponential
cccToCircuit Apply                    = apply
cccToCircuit (Curry h)                = curry (cccToCircuit h)
cccToCircuit (Uncurry h)              = uncurry (cccToCircuit h)

cccToCircuit ccc = error $ "cccToCircuit: not yet handled: " ++ show ccc

expand :: HasTy2 a b => (a :-> b) -> Maybe (a :-> b)
expand k@(Prim CondP) | (_,u :* v) <- cccTys k
                      , HasTy <- tyHasTy u, HasTy <- tyHasTy v
                      = Just condPair
expand _ = Nothing

-- TODO: tweak condPair to expand one step at a time.
-- Remove condC if I can't find a way to use it.

--     (_,u :* v) -> cccToCircuit condPair
--     _          -> namedC "cond"

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

#define TS (tyPSource -> PSource)

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
   toS CondP (_ :=> TS)       = namedC "mux"
   toS p _                    = error $ "primToSource: not yet handled: " ++ show p

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
