{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- For tests

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Tests
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
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

{- Conversions (with Simplify and ShowFolded, though ShowFolded isn't helping):

> asCCC e1
konst False
> asCCC e2
prim not . konst False
> asCCC e3
konst not
> asCCC e4
curry snd
> asCCC e5
curry (prim add . (snd &&& snd))
> asCCC e6
curry (snd &&& snd)
> asCCC e7
curry (prim not . prim and . (prim not . fst . snd &&& prim not . snd . snd))
> asCCC e8
curry (snd . snd &&& fst . snd)
> asCCC e9
curry (prim xor . (fst . snd &&& snd . snd) &&& prim and . (fst . snd &&& snd . snd))

-}

{- Examples e3 through e9, without extra unit context, i.e., with asCCC':

Without Simplify and without ShowFolded:

> apply . (konst not &&& id)
> id
> apply . (konst add &&& id &&& id)
> id &&& id
> apply . (konst not &&& apply . (konst and &&& apply . (konst not &&& id . fst) &&& apply . (konst not &&& id . snd)))
> id . snd &&& id . fst
> apply . (konst xor &&& id . fst &&& id . snd) &&& apply . (konst and &&& id . fst &&& id . snd)

With Simplify:

> prim not
> id
> prim add . (id &&& id)
> id &&& id
> prim not . prim and . (prim not . fst &&& prim not . snd)
> snd &&& fst
> prim xor &&& prim and

With Simplify and ShowFolded:

> prim not
> id
> prim add . dup
> dup
> prim not . prim and . (prim not *** prim not)
> swapP
> prim xor &&& prim and

-}
