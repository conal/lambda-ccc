{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE ExistentialQuantification, PatternGuards #-}
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
-- Lambda expressions
----------------------------------------------------------------------

module LambdaCCC.Lambda
  ( Name, Pat(..), E(..)
  , (#), notE, (||*), (&&*), xor, (+@)
  , vars, vars2
  ) where

import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.ShowUtils
import LambdaCCC.Prim
import LambdaCCC.Ty

-- Whether to simply (fold) during show
#define ShowFolded

-- | Variable names
type Name = String

-- | Lambda patterns
data Pat :: * -> * where
  UnitP :: Pat Unit
  VarP  :: Name -> Ty a -> Pat a
  PairP :: Pat a -> Pat b -> Pat (a :* b)

showsVar :: Prec -> Name -> Ty a -> ShowS
showsVar p n ty = showString n . showString " :: " . showsPrec p ty

instance Show (Pat a) where
  showsPrec _ UnitP       = showString "()"
  showsPrec p (VarP n ty) = showsVar p n ty
  showsPrec p (PairP a b) = showsPair p a b

infixl 9 :^

infix 1 :#

-- | Lambda expressions
data E :: * -> * where
  Var   :: Name -> Ty a -> E a
  Const :: Prim a -> E a
  (:#)  :: E a -> E b -> E (a :* b)
  (:^)  :: E (a :=> b) -> E a -> E b
  Lam   :: Pat a -> E b -> E (a :=> b)

-- | Single variable binding
data Bind = forall a. Bind Name (Ty a) a
-- | Variable environment
type Env = [Bind]

instance Show (E a) where
#ifdef ShowFolded
  showsPrec p (Const prim :^ (u :# v)) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2' op fixity p u v
--   showsPrec p (Const Add :^ (u :# v)) = showsOp2' "+"     (6,AssocLeft ) p u v
--   showsPrec p (Const And :^ (u :# v)) = showsOp2' "&&&"   (3,AssocRight) p u v
--   showsPrec p (Const Or  :^ (u :# v)) = showsOp2' "|||"   (2,AssocRight) p u v
--   showsPrec p (Const Xor :^ (u :# v)) = showsOp2' "`xor`" (2,AssocRight) p u v
#endif
  -- showsPrec p (Var n ty) = showsVar p n ty
  showsPrec _ (Var n _) = showString n
  showsPrec p (Const c) = showsPrec p c
  showsPrec p (u :# v)  = showsPair p u v
  showsPrec p (u :^ v)  = showsApp p u v
  showsPrec p (Lam q e) = showParen (p > 0) $
                          showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e

data OpInfo = OpInfo String Fixity

opInfo :: Prim a -> Maybe OpInfo
opInfo Add = Just $ OpInfo "+"     (6,AssocLeft )
opInfo And = Just $ OpInfo "&&&"   (3,AssocRight)
opInfo Or  = Just $ OpInfo "|||"   (2,AssocRight)
opInfo Xor = Just $ OpInfo "`xor`" (2,AssocRight)
opInfo _   = Nothing


{--------------------------------------------------------------------
    Convenient notation for expression building
--------------------------------------------------------------------}

infixr 1 #
(#) :: E a -> E b -> E (a :* b)
-- (Const Fst :^ p) # (Const Snd :^ p') | ... = ...
a # b = a :# b

notE :: Unop (E Bool)
notE b = Const Not :^ b

infixr 2 ||*, `xor`
infixr 3 &&*

(&&*) :: Binop (E Bool)
a &&* b = Const And :^ (a # b)

(||*) :: E Bool -> E Bool -> E Bool
a ||* b = Const Or  :^ (a # b)

xor :: E Bool -> E Bool -> E Bool
a `xor` b = Const Xor :^ (a # b)

infixl 6 +@
(+@) :: Num a => E a -> E a -> E a
a +@ b = Const Add :^ (a # b)

-- TODO: Use Num and Boolean classes

-- We evaluate *closed* expressions (no free variables)
instance Evalable (E a) where
  type ValT (E a) = a
  eval e = eval' e []  -- provide empty environment

-- TODO: Rework so that eval can work independently of env. Will save repeated
-- evals.

-- Expression evaluation requires a binding environment. In other words,
-- expressions evaluate to a function from environments.

eval' :: E a -> Env -> a
eval' (Var name ty) env = fromMaybe (error $ "eval': unbound name: " ++ name) $
                          lookupVar name ty env
eval' (Const p)     _   = eval p
eval' (u :# v)      env = (eval' u env, eval' v env)
eval' (u :^ v)      env = (eval' u env) (eval' v env)
eval' (Lam p e)     env = \ x -> eval' e (extendEnv p x env)


extendEnv :: Pat b -> b -> Env -> Env
extendEnv UnitP         ()    = id
extendEnv (VarP nb tyb) b     = (Bind nb tyb b :)
extendEnv (PairP p q)   (a,b) = extendEnv q b . extendEnv p a

lookupVar :: Name -> Ty a -> Env -> Maybe a
lookupVar na tya = look
 where
   look [] = Nothing
   look (Bind nb tyb b : env')
     | nb == na, Just Refl <- tya `tyEq` tyb = Just b
     | otherwise = look env'

-- Oh, hm. I'm using a difference (Hughes) list representation. extendEnv maps
-- UnitP, VarP, and PairP to mempty, singleton, and mappend, respectively.
-- 
-- TODO: adopt another representation, such as Seq. Replace the explicit
-- recursion in lookupVar with a fold or something. It's almost a mconcat. Could
-- use toList and catMaybes.

vars :: HasTy a => Name -> (Pat a, E a)
vars n = (VarP n t, Var n t) where t = typ

vars2 :: (HasTy a, HasTy b) =>
         (Name,Name) -> (Pat (a,b), (E a,E b))
vars2 (na,nb) = (PairP ap bp, (ae,be))
 where
   (ap,ae) = vars na
   (bp,be) = vars nb
