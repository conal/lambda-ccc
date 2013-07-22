{-# LANGUAGE TypeOperators, GADTs, KindSignatures, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
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

import Prelude hiding (id,(.),fst,snd,not,and,or,curry,uncurry)

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
cccToCircuit (Prim FstP)              = fst -- TODO: Drop the redundant Fst/FstP ??
cccToCircuit (Prim SndP)              = snd
cccToCircuit (Prim NotP)              = not
cccToCircuit (Uncurry (Prim AndP))    = and
cccToCircuit (Uncurry (Prim OrP))     = or
cccToCircuit (Uncurry (Prim XorP))    = xor
cccToCircuit k@(Uncurry (Prim AddP))  | (PSource, PSource) <- cccPS k
                                      = namedC "add"

cccToCircuit k@(Prim CondP)           | (PSource, PSource) <- cccPS k
                                      = namedC "mux"

cccToCircuit k@(Prim (ConstP (LitP b))) | (PSource, PSource) <- cccPS k
                                      = constC b
-- Product
cccToCircuit Fst                      = fst
cccToCircuit Snd                      = snd

cccToCircuit (f :&&& g)               = cccToCircuit f &&& cccToCircuit g
-- Coproduct
cccToCircuit k@Lft                    | (a, _ :+ b) <- cccTys k
                                      , PSource <- tyPSource a
                                      , PSource <- tyPSource b
                                      = lftC
cccToCircuit k@Rht                    | (b, a :+ _) <- cccTys k
                                      , PSource <- tyPSource a
                                      , PSource <- tyPSource b
                                      = rhtC
cccToCircuit k@(f :||| g)             | (a :+ b, c) <- cccTys k
                                      , PSource <- tyPSource a
                                      , PSource <- tyPSource b
                                      , PSource <- tyPSource c
                                      = cccToCircuit f |||* cccToCircuit g
-- Exponential
-- cccToCircuit Apply                    = apply
-- cccToCircuit (Curry h)                = curry (cccToCircuit h)
-- cccToCircuit (Uncurry h)              = uncurry (cccToCircuit h)

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

{- Incompleteness notes: 

Not handing sums or exponentials yet. The commented-out definitions above
erroneously assume that Pins distributes over sums and (I think) exponentials,
which is not the case. I think it would be the case with categorical products
and coproducts, so that the coproduct needn't coincide with sum.

-}

-- TODO: I don't know whether to keep add. We'll probably want to build it from
-- simpler pieces.
--
-- TODO: Maybe implement all primitives (other than fst & snd) with namedC. I
-- could even use this PrimC type in circat, though it'd be the first dependency
-- of circat on lambda-ccc.

-- Prove that IsSource (Pins a), IsSource (Pins b)
cccPS :: (a :-> b) -> (PSourceJt a, PSourceJt b)
cccPS = tyPSource2 . cccTys

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
tyPSource UnitT = PSource
tyPSource BoolT = PSource
tyPSource (a :* b) | (PSource,PSource) <- tyPSource2 (a,b) = PSource
tyPSource ty = error $ "tyPSource: Oops -- not yet handling " ++ show ty

-- TODO: IntT, a :+ b, a :=> b.
-- 
-- I guess I'll use nested pairs for Int, a product-plus-mux encoding for sums,
-- and some sort of memoization and/or closure for functions.

tyPSource2 :: (Ty a,Ty b) -> (PSourceJt a, PSourceJt b)
tyPSource2 (a,b) = (tyPSource a,tyPSource b)
