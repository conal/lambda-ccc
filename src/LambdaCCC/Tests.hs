{-# LANGUAGE TypeOperators, ConstraintKinds #-}
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
import LambdaCCC.Lambda
import LambdaCCC.CCC
import LambdaCCC.ToCCC

{--------------------------------------------------------------------
    Convenient notation for expression building
--------------------------------------------------------------------}

-- TODO: Maybe eliminate this notation or move it elsewhere, since we're mainly
-- translating automatically rather than hand-coding. I'm using this vocabulary
-- for tests.

notE :: Unop (E Bool)
notE b = ConstE NotP :^ b

infixr 2 ||*, `xorE`
infixr 3 &&*

binop :: Prim (a -> b -> c) -> E a -> E b -> E c
binop op a b = ConstE op :^ a :^ b

(&&*), (||*), xorE :: Binop (E Bool)
(&&*) = binop AndP
(||*) = binop OrP
xorE  = binop XorP

infixl 6 +@
(+@) :: Num a => Binop (E a)
(+@) = binop AddP

-- TODO: Use Num and Boolean classes


{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

var :: Name -> E a
var = Var . V

va,vb,vc :: E Int
va = var "a"
vb = var "b"
vc = var "c"

e1 :: E Bool
e1 = ConstE (LitP (BoolL False))

e2 :: E Bool
e2 = notE e1

infixr 1 :+>
type a :+> b = E (a -> b)

-- \ x -> not
e3 :: Bool :+> Bool
e3 = ConstE NotP

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
e9 = Lam p ((a `xorE` b) # (a &&* b))   -- half-adder
 where
   (p,(a,b)) = vars2 ("a","b")

-- e10 :: Bool :* ((Int :=> Bool) :* (Int :=> Bool)) -> (Int :=> Bool)
-- e10 = \ (p,(f,g)) a -> cond (p,(f a,g a))

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

{- toCCC applied to examples e3 through e9:

Without Simplify and without ShowFolded:

> apply . (konst not &&& id)
> id
> apply . (apply . (konst add &&& id) &&& id)
> id &&& id
> apply . (konst not &&& apply . (apply . (konst (&&) &&& apply . (konst not &&& id . exl)) &&& apply . (konst not &&& id . exr)))
> id . exr &&& id . exl
> apply . (apply . (konst xor &&& id . exl) &&& id . exr) &&& apply . (apply . (konst (&&) &&& id . exl) &&& id . exr)

With Simplify:

> not
> id
> apply . (add &&& id)
> id &&& id
> not . uncurry (&&) . (not . exl &&& not . exr)
> exr &&& exl
> uncurry xor &&& uncurry (&&)

With Simplify and ShowFolded:

> not
> id
> uncurry add . dup
> dup
> not . uncurry (&&) . (not *** not)
> swapP
> uncurry xor &&& uncurry (&&)

-}
