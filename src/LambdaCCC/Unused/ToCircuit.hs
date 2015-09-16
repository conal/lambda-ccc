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
  ) where

import Prelude hiding (id,(.),curry,uncurry)
import Data.Constraint (Dict(..))

import Circat.Prim hiding (xor)
import LambdaCCC.CCC
import LambdaCCC.Lambda (E)
import LambdaCCC.ToCCC (toCCC)

import Circat.Circuit
import Circat.Category
import Circat.Classes

expToCircuit :: E Prim (a -> b) -> (a :> b)
expToCircuit = cccToCircuit . toCCC

#define TS (tyPSource -> Dict)
#define CP (cccPS -> (Dict, Dict))
#define TC (tyHasCond -> Dict)

#define LS (litSS -> Dict)

cccToCircuit :: (a :-> b) -> (a :> b)

-- Category
cccToCircuit Id              = id
cccToCircuit (g :. f)        = cccToCircuit g . cccToCircuit f
-- Primitives
cccToCircuit (Prim p)        = primToSource p
cccToCircuit (Lit l@LS)      = constC (eval l)
-- Product
cccToCircuit Exl             = exl
cccToCircuit Exr             = exr
cccToCircuit (f :&&& g)      = cccToCircuit f &&& cccToCircuit g
-- Coproduct
cccToCircuit Inl             = inl
cccToCircuit Inr             = inr
-- cccToCircuit k@(f :||| g) = cccToCircuit f |||* cccToCircuit g
-- Exponential
cccToCircuit Apply           = apply
cccToCircuit (Curry h)       = curry (cccToCircuit h)
cccToCircuit (Uncurry h)     = uncurry (cccToCircuit h)

cccToCircuit ccc = error $ "cccToCircuit: not yet handled: " ++ show ccc

#define TH (tyHasTy -> HasTy)

-- TODO: I don't know whether to keep add. We'll probably want to build it from
-- simpler pieces.
--
-- TODO: Maybe implement all primitives (other than exl & exr) with namedC. I
-- could even use this PrimC type in circat, though it'd be the first dependency
-- of circat on lambda-ccc.

{--------------------------------------------------------------------
    Prim conversion
--------------------------------------------------------------------}

primToSource :: Prim t -> Pins t
primToSource NotP  = not
primToSource AndP  = curry and
primToSource OrP   = curry or
primToSource XorP  = curry xor
primToSource ExlP  = exl
primToSource ExrP  = exr
primToSource PairP = curry id
primToSource InlP  = inl
primToSource InrP  = inr
-- primToSource CondP = condC
-- primToSource AddP  = curry (namedC "add")
primToSource p     = error $ "primToSource: not yet handled: " ++ show p

#if 0

-- Prove that IsSource (Pins a), IsSource (Pins b)
cccPS :: (a :-> b) -> (PSourceJt a, PSourceJt b)
cccPS = tyPSource2 . cccTys

{--------------------------------------------------------------------
    Proofs
--------------------------------------------------------------------}

type PSourceJt a = Dict (IsSourceP a)

-- | Proof of @'IsSource' ('Pins' a)@ from @'Ty' a@
tyPSource :: Ty a -> PSourceJt a
tyPSource Unit       = Dict
tyPSource Bool       = Dict
tyPSource (TS :* TS) = Dict  -- still needed?
tyPSource ty         = error $ "tyPSource: Oops -- not yet handling " ++ show ty

-- That product case gets used for my CRC example when I turn off the
-- xor/constant rewrite rules.

tyPSource2 :: (Ty a,Ty b) -> (PSourceJt a, PSourceJt b)
tyPSource2 (a,b) = (tyPSource a,tyPSource b)

-- tyPSource2 = tyPSource *** tyPSource

-- | Proof of @'HasCond t@ from @'Ty' t@
tyHasCond :: Ty t -> Dict (HasCond t)
tyHasCond Unit       = Dict
tyHasCond Bool       = Dict
tyHasCond (TC :* TC) = Dict
tyHasCond (_  :+ _ ) = Dict
tyHasCond (_ :=> TC) = Dict
tyHasCond Int  = error "tyHasCond: Int not yet handled."

#endif