{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, PatternGuards #-}
{-# LANGUAGE MagicHash, ConstraintKinds #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Lambda
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Lambda expressions -- phantom variable type edition
----------------------------------------------------------------------

module LambdaCCC.Lambda
  ( Name
  , V, Pat(..), E(..)
  , varTy, patTy, expTy
  , var, lamv
  , varT, constT
  , reifyE, evalE
  , vars, vars2
  ) where

import Control.Arrow ((&&&))
import Data.Maybe (fromMaybe,catMaybes,listToMaybe)
import Debug.Trace (trace)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.ShowUtils
import LambdaCCC.Prim
import LambdaCCC.Ty

-- Whether to fold simple definitions during show
#define ShowFolded

-- | Variable names
type Name = String

-- | Typed variable
data V a = V Name (Ty a)

instance Show (V a) where
  -- showsPrec p (V n ty) = showString n . showString " :: " . showsPrec p ty
  showsPrec _ (V n _) = showString n

instance IsTy V where
  V na tya `tyEq` V nb tyb | nb == na  = tya `tyEq` tyb
                           | otherwise = Nothing

varTy :: V a -> Ty a
varTy (V _ ty) = ty

-- | Lambda patterns
data Pat :: * -> * where
  UnitPat :: Pat Unit
  VarPat  :: V a -> Pat a
  PairPat :: Pat a -> Pat b -> Pat (a :* b)

instance Show (Pat a) where
  showsPrec _ UnitPat       = showString "()"
  showsPrec p (VarPat v)    = showsPrec p v
  showsPrec p (PairPat a b) = showsPair p a b

patTy :: Pat a -> Ty a
patTy UnitPat       = UnitT
patTy (VarPat v)    = varTy v
patTy (PairPat a b) = patTy a :* patTy b

infixl 9 :^

-- infix 1 :#

-- | Lambda expressions
data E :: * -> * where
  Var   :: forall a   . V a -> E a
  Const :: forall a   . Prim a -> Ty a -> E a
--  (:#)  :: forall a b . E a -> E b -> E (a :* b)
  (:^)  :: forall b a . E (a :=> b) -> E a -> E b
  Lam   :: forall a b . Pat a -> E b -> E (a :=> b)

expTy :: E a -> Ty a
expTy (Var v)      = varTy v
expTy (Const _ ty) = ty
expTy (f :^ _)     = case expTy f of _ :=> b -> b
expTy (Lam p e)    = patTy p :=> expTy e

-- I've placed the quantifiers explicitly to reflect what I learned from GHCi
-- (In GHCi, use ":set -fprint-explicit-foralls" and ":ty (:^)".)
-- When I said "forall a b" in (:^), GHC swapped them back. Oh well.

-- TODO: Replace the Const Ty argument with a HasTy constraint for ease of use.
-- I'm waiting until I know how to construct the required dictionaries in Core.
-- 
-- Meanwhile,

varT :: HasTy a => Name -> E a
varT nm = Var (V nm typ)

constT :: HasTy a => Prim a -> E a
constT p = Const p typ

var :: forall a. Name -> Ty a -> E a
var name ty = Var (V name ty)

lamv :: forall a b. Name -> Ty a -> E b -> E (a -> b)
lamv name ty body = Lam (VarPat (V name ty)) body

instance Show (E a) where
#ifdef ShowFolded
--   showsPrec p (Const prim :^ (u :# v)) | Just (OpInfo op fixity) <- opInfo prim =
--     showsOp2' op fixity p u v
  showsPrec p (Const PairP _ :^ u :^ v) = showsPair p u v
  showsPrec p (Const prim _ :^ u :^ v) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2' op fixity p u v
#endif
  showsPrec _ (Var (V n _))  = showString n
  showsPrec p (Const c _) = showsPrec p c
--  showsPrec p (u :# v)  = showsPair p u v
  showsPrec p (u :^ v)  = showsApp p u v
  showsPrec p (Lam q e) = showParen (p > 0) $
                          showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e

data OpInfo = OpInfo String Fixity

opInfo :: Prim a -> Maybe OpInfo
opInfo AddP = Just $ OpInfo "+"     (6,AssocLeft )
opInfo AndP = Just $ OpInfo "&&&"   (3,AssocRight)
opInfo OrP  = Just $ OpInfo "|||"   (2,AssocRight)
opInfo XorP = Just $ OpInfo "`xor`" (2,AssocRight)
opInfo _   = Nothing

-- | Single variable binding
data Bind = forall a. Bind (V a) a
-- | Variable environment
type Env = [Bind]

reifyE :: a -> Ty a -> E a
reifyE = error "reifyE: Not implemented. I hoped all uses would disappear."

{-# RULES

"reify/eval" forall t e. reifyE (evalE e) t = e
"eval/reify" forall t x. evalE (reifyE x t) = x

  #-}

-- We evaluate *closed* expressions (no free variables)
instance Evalable (E a) where
  type ValT (E a) = a
  eval = evalE

evalE :: E a -> a
evalE e = trace ("evalE: " ++ show e) $
          eval' e []  -- provide empty environment

-- TODO: Rework so that eval' can work independently of env. Will save repeated
-- evals.

-- Expression evaluation requires a binding environment. In other words,
-- expressions evaluate to a function from environments.

eval' :: E a -> Env -> a
eval' (Var v)   env = fromMaybe (error $ "eval': unbound variable: " ++ show v) $
                      lookupVar v env
eval' (Const p _) _   = eval p
-- eval' (u :# v)  env = (eval' u env, eval' v env)
eval' (u :^ v)  env = (eval' u env) (eval' v env)
eval' (Lam p e) env = \ x -> eval' e (extendEnv p x env)

extendEnv :: Pat b -> b -> Env -> Env
extendEnv UnitPat       ()    = id
extendEnv (VarPat vb)   b     = (Bind vb b :)
extendEnv (PairPat p q) (a,b) = extendEnv q b . extendEnv p a

lookupVar :: forall a. V a -> Env -> Maybe a
lookupVar va = listToMaybe . catMaybes . map check
 where
   check :: Bind -> Maybe a
   check (Bind vb b) | Just Refl <- va `tyEq` vb = Just b
                     | otherwise                 = Nothing

-- Oh, hm. I'm using a difference (Hughes) list representation. extendEnv maps
-- UnitPat, VarPat, and PairPat to mempty, singleton, and mappend, respectively.
-- 
-- TODO: adopt another representation, such as Seq. Replace the explicit
-- recursion in lookupVar with a fold or something. It's almost a mconcat.

vars :: HasTy a => Name -> (Pat a, E a)
vars = (VarPat &&& Var) . flip V typ

-- vars n = (VarPat v, Var v) where v = V n typ

vars2 :: HasTy2 a b =>
         (Name,Name) -> (Pat (a,b), (E a,E b))
vars2 (na,nb) = (PairPat ap bp, (ae,be))
 where
   (ap,ae) = vars na
   (bp,be) = vars nb

{--------------------------------------------------------------------
    Rules
--------------------------------------------------------------------}

{-# RULES
 
"reify/not"  reifyE not  = Const NotP
"reify/(&&)" reifyE (&&) = Const AndP
"reify/(||)" reifyE (||) = Const OrP
"reify/xor"  reifyE xor  = Const XorP
"reify/(+)"  reifyE (+)  = Const AddP
"reify/fst"  reifyE fst  = Const FstP
"reify/snd"  reifyE snd  = Const SndP
"reify/pair" reifyE (,)  = Const PairP
 
  #-}
