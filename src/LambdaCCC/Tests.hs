{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- For tests

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Tests
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Test conversion from Lambda to CCC
----------------------------------------------------------------------

module LambdaCCC.Tests where

import LambdaCCC.Misc
import LambdaCCC.Prim
import LambdaCCC.Ty (Ty(..))
import LambdaCCC.Lambda
import LambdaCCC.AsCCC

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

> eval e1
False
> eval e2
True
> eval e3 True
False
> eval e4 5
5
> eval e5 10
20
> eval e6 10
(10,10)
> eval e8 (True,False)
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
apply . (prim (,) . prim xor . apply . (prim (,) . fst &&& snd) &&& prim and . apply . (prim (,) . fst &&& snd))

-}
