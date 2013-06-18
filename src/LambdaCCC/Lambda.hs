{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE ExistentialQuantification, PatternGuards #-}
{-# LANGUAGE MagicHash #-}
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
  , var, lamv
  , reifyE, evalE
  , (#), notE, (||*), (&&*), xor, (+@)
  , vars, vars2
  ) where

import Control.Arrow ((&&&))
import Data.Maybe (fromMaybe)
import Unsafe.Coerce (unsafeCoerce)  -- for eval (unnecessary)

import LambdaCCC.Misc
import LambdaCCC.ShowUtils
import LambdaCCC.Prim

-- Whether to fold simple definitions during show
#define ShowFolded

-- | Variable names
type Name = String

-- | Typed variable
type V a = Name

-- | Lambda patterns
data Pat :: * -> * where
  UnitP :: Pat Unit
  VarP  :: V a -> Pat a
  PairP :: Pat a -> Pat b -> Pat (a :* b)

instance Show (Pat a) where
  showsPrec _ UnitP       = showString "()"
  showsPrec p (VarP v)    = showsPrec p v
  showsPrec p (PairP a b) = showsPair p a b

infixl 9 :^

infix 1 :#

-- | Lambda expressions
data E :: * -> * where
  Var   :: forall a   . V a -> E a
  Const :: forall a   . Prim a -> E a
  (:#)  :: forall a b . E a -> E b -> E (a :* b)
  (:^)  :: forall b a . E (a :=> b) -> E a -> E b
  Lam   :: forall a b . Pat a -> E b -> E (a :=> b)

-- I've placed the quantifiers explicitly to reflect what I learned from GHCi
-- (In GHCi, use ":set -fprint-explicit-foralls" and ":ty (:^)".)
-- When I said "forall a b" in (:^), GHC swapped them back. Oh well.

-- TODO: Consider replacing (:#) with a Pair Prim and simplifying the
-- implementation accordingly. (Note that Fst and Snd are prims.)

var :: forall a. Name -> E a
var = Var

lamv :: forall a b. Name -> E b -> E (a -> b)
-- lamv = Lam . VarP
lamv name body = Lam (VarP name) body

instance Show (E a) where
#ifdef ShowFolded
  showsPrec p (Const prim :^ (u :# v)) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2' op fixity p u v
#endif
  showsPrec p (Var v)   = showsPrec p v
  showsPrec p (Const c) = showsPrec p c
  showsPrec p (u :# v)  = showsPair p u v
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


{--------------------------------------------------------------------
    Convenient notation for expression building
--------------------------------------------------------------------}

-- TODO: Maybe eliminate this notation or move it elsewhere, since we're mainly
-- translating automatically rather than hand-coding. I'm using this vocabulary
-- for tests.

infixr 1 #
(#) :: E a -> E b -> E (a :* b)
-- (Const Fst :^ p) # (Const Snd :^ p') | ... = ...
a # b = a :# b

notE :: Unop (E Bool)
notE b = Const NotP :^ b

infixr 2 ||*, `xor`
infixr 3 &&*

binop :: Prim (a :* b :=> c) -> E a -> E b -> E c
binop op a b = Const op :^ (a # b)

(&&*), (||*), xor :: Binop (E Bool)
(&&*) = binop AndP
(||*) = binop OrP
xor   = binop XorP

infixl 6 +@
(+@) :: Num a => Binop (E a)
(+@) = binop AddP

-- TODO: Use Num and Boolean classes

-- | Single variable binding
data Bind = forall a. Bind Name a
-- | Variable environment
type Env = [Bind]

reifyE :: a -> E a
reifyE = error "reifyE: Not implemented. I hoped the uses would all disappear."

-- We evaluate *closed* expressions (no free variables)
instance Evalable (E a) where
  type ValT (E a) = a
  eval = evalE

evalE :: E a -> a
evalE e = eval' e []  -- provide empty environment

-- TODO: Rework so that eval' can work independently of env. Will save repeated
-- evals.

-- Expression evaluation requires a binding environment. In other words,
-- expressions evaluate to a function from environments.

eval' :: E a -> Env -> a
eval' (Var v)   env = fromMaybe (error $ "eval': unbound variable: " ++ show v) $
                      lookupVar v env
eval' (Const p) _   = eval p
eval' (u :# v)  env = (eval' u env, eval' v env)
eval' (u :^ v)  env = (eval' u env) (eval' v env)
eval' (Lam p e) env = \ x -> eval' e (extendEnv p x env)

extendEnv :: Pat b -> b -> Env -> Env
extendEnv UnitP       ()    = id
extendEnv (VarP nb)   b     = (Bind nb b :)
extendEnv (PairP p q) (a,b) = extendEnv q b . extendEnv p a

lookupVar :: V a -> Env -> Maybe a
lookupVar na = look
 where
   look []                             = Nothing
   look (Bind nb b : env') | nb == na  = Just (unsafeCoerce b)  -- !
                           | otherwise = look env'

-- Oh, hm. I'm using a difference (Hughes) list representation. extendEnv maps
-- UnitP, VarP, and PairP to mempty, singleton, and mappend, respectively.
-- 
-- TODO: adopt another representation, such as Seq. Replace the explicit
-- recursion in lookupVar with a fold or something. It's almost a mconcat. Could
-- use toList and catMaybes.

vars :: Name -> (Pat a, E a)
vars = VarP &&& Var

vars2 :: (Name,Name) -> (Pat (a,b), (E a,E b))
vars2 (na,nb) = (PairP ap bp, (ae,be))
 where
   (ap,ae) = vars na
   (bp,be) = vars nb

{--------------------------------------------------------------------
    Rules
--------------------------------------------------------------------}

{-# RULES

"var/xor"  var "xor" = Const XorP
"var/and"  var "and" = Const AndP
"var/pair" forall a b. var "(,)" :^ a :^ b = a :# b
"var/fst"  var "fst" = Const FstP
"var/snd"  var "snd" = Const SndP

  #-}
