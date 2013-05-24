{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE PatternGuards, ExistentialQuantification #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.AsCCC
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert lambda expressions to CCC combinators
----------------------------------------------------------------------

module LambdaCCC.AsCCC 
  ( (:->)(..), (&&&), (***), (+++), (|||)
  , Prim(..)
  , first, second, left, right
  , Name, E(..), Pat(..)
  , asCCC, asCCC'
  ) where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.ShowUtils
import LambdaCCC.Prim
import LambdaCCC.Ty
import LambdaCCC.CCC

{--------------------------------------------------------------------
    Lambda expressions
--------------------------------------------------------------------}

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

-- | Lambda expressions
data E :: * -> * where
  Var   :: Name -> Ty a -> E a
  Const :: Prim a -> E a
  (:^)  :: E (a :=> b) -> E a -> E b
  Lam   :: Pat a -> E b -> E (a :=> b)

data Bind = forall a. Bind Name (Ty a) a
type Env = [Bind]

instance Show (E a) where
#ifdef SimplifyShow
  showsPrec p (Const Add :^ (Const Pair :^ u :^ v)) = showsOp2' "+"     (6,AssocLeft ) p u v
  showsPrec p (Const And :^ (Const Pair :^ u :^ v)) = showsOp2' "&&&"   (3,AssocRight) p u v
  showsPrec p (Const Or  :^ (Const Pair :^ u :^ v)) = showsOp2' "|||"   (2,AssocRight) p u v
  showsPrec p (Const Xor :^ (Const Pair :^ u :^ v)) = showsOp2' "`xor`" (2,AssocRight) p u v
  showsPrec p (Const Pair :^ u :^ v) = showsPair p u v
#endif
  -- showsPrec p (Var n ty) = showsVar p n ty
  showsPrec _ (Var n _) = showString n
  showsPrec p (Const c) = showsPrec p c
  showsPrec p (Lam q e) = showParen (p > 0) $
                          showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e
  showsPrec p (u :^ v) = showsApp p u v

-- TODO: Refactor add/and/or/xor/pair

infixr 1 #
(#) :: E a -> E b -> E (a :* b)
a # b = Const Pair :^ a :^ b

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

instance Evalable (E a) where
  type ValT (E a) = Env -> a
  eval (Var name ty) env = fromMaybe (error $ "eval: unbound name: " ++ name) $
                           lookupVar name ty env
  eval (Const p)     _   = eval p
  eval (u :^ v)      env = (eval u env) (eval v env)
  eval (Lam p e)     env = \ x -> eval e (extendEnv p x env)

-- TODO: Rework so that eval can work independently of env. Will save repeated
-- evals.

evalE :: E a -> a
evalE e = eval e []

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

etaExpand :: HasTy a => E (a :=> b) -> E (a :=> b)
etaExpand (Lam{}) = error "etaExpand: did you mean to expand a lambda?"
etaExpand e = Lam vp (e :^ ve)
 where
   (vp,ve) = vars "ETA"

vars :: HasTy a => Name -> (Pat a, E a)
vars n = (VarP n t, Var n t) where t = typ

vars2 :: (HasTy a, HasTy b) =>
         (Name,Name) -> (Pat (a,b), (E a,E b))
vars2 (na,nb) = (PairP ap bp, (ae,be))
 where
   (ap,ae) = vars na
   (bp,be) = vars nb

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

-- | Rewrite a lambda expression via CCC combinators
asCCC :: E a -> (Unit :-> a)
asCCC = convert UnitP

asCCC' :: HasTy a => E (a :=> b) -> (a :-> b)
asCCC' (Lam p e) = convert p e
asCCC' e = asCCC' (etaExpand e)

-- | Convert @\ p -> e@ to CCC combinators
convert :: Pat a -> E b -> (a :-> b)
convert _ (Const o)  = Konst o
convert k (Var n t)  = fromMaybe (error $ "unbound variable: " ++ n) $
                       convertVar k n t
convert k (u :^ v)   = Apply @. (convert k u &&& convert k v)
convert k (Lam p e)  = Curry (convert (PairP k p) e)

-- Convert a variable in context
convertVar :: Pat a -> Name -> Ty b -> Maybe (a :-> b)
convertVar (VarP x a) n b | x == n, Just Refl <- a `tyEq` b = Just Id
                          | otherwise = Nothing
convertVar UnitP _ _ = Nothing
convertVar (PairP p q) n b = 
  ((@. Snd) <$> convertVar q n b) `mplus` ((@. Fst) <$> convertVar p n b)

-- Note that we try q before p. This choice cooperates with uncurrying and
-- shadowing.

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

va,vb,vc :: E Int
va = Var "a" IntT
vb = Var "b" IntT
vc = Var "c" IntT

ty1 :: Ty (Int :=> Int)
ty1 = IntT :=> IntT

ty2 :: Ty ((Int :=> Int) :* Bool)
ty2 = (IntT :=> IntT) :* BoolT

e1 :: E Bool
e1 = Const (Lit False)

e2 :: E Bool
e2 = notE e1

infixr 1 :+>
type a :+> b = E (a :=> b)

-- \ x -> not
e3 :: Bool :+> Bool
e3 = Const Not

-- \ x -> x
e4 :: Int :+> Int
e4 = Lam p x
 where
   (p,x) = vars "x"

-- \ x -> x + x
e5 :: Int :+> Int
e5 = Lam p (x +@ x)
 where
   (p,x) = vars "x"

-- \ x -> (x,x)
e6 :: Int :+> Int :* Int
e6 = Lam p (x # x)
 where
   (p,x) = vars "x"

-- \ (a,b) -> not (not a && not b)
e7 :: Bool :* Bool :+> Bool
e7 = Lam p (notE (notE a &&* notE b))
 where
   (p,(a,b)) = vars2 ("a","b")

-- \ (a,b) -> (b,a)
e8 :: Bool :* Bool :+> Bool :* Bool
e8 = Lam p (b # a) where (p,(a,b)) = vars2 ("a","b")

-- Half adder: \ (a,b) -> (a `xor` b, a && b)
e9 :: Bool :* Bool :+> Bool :* Bool
e9 = Lam p ((a `xor` b) # (a &&* b))   -- half-adder
 where
   (p,(a,b)) = vars2 ("a","b")


{- Evaluations:

> evalE e1
False
> evalE e2
True
> evalE e3 True
False
> evalE e4 5
5
> evalE e5 10
20
> evalE e6 10
(10,10)
> evalE e8 (True,False)
(False,True)
-}

{- Conversions:

> asCCC e1
konst False
> asCCC e2
prim not . konst False
> asCCC e3
konst not
> asCCC e4
curry snd
> asCCC e5
curry (prim add . apply . (prim (,) . snd &&& snd))
> asCCC e6
curry (apply . (prim (,) . snd &&& snd))

-- TODO: try auto-refactoring to get 
--   curry (dup . snd)

-}

{- Without extra unit context:

> asCCC' e3
prim not
> asCCC' e4
id
> asCCC' e5
prim add . dup
> asCCC' e6
dup
> asCCC' e7
prim not . prim and . apply . (prim (,) . prim not . fst &&& prim not . snd)
> asCCC' e8
apply . (prim (,) . snd &&& fst)
> asCCC' e9
apply . (prim (,) . prim xor . apply . first (prim (,)) &&& prim and . apply . first (prim (,)))

-}
