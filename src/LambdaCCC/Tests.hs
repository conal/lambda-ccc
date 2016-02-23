{-# LANGUAGE TypeOperators, ConstraintKinds, CPP #-}
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

import Prelude hiding (id,(.),curry,uncurry,not)

import LambdaCCC.Misc
import LambdaCCC.Lambda
-- import LambdaCCC.CCC
import LambdaCCC.ToCCC

import Circat.Category
import Circat.Classes

import LambdaCCC.Prim

{--------------------------------------------------------------------
    Convenient notation for expression building
--------------------------------------------------------------------}

-- TODO: Maybe eliminate this notation or move it elsewhere, since we're mainly
-- translating automatically rather than hand-coding. I'm using this vocabulary
-- for tests.

notE :: Unop (EP Bool)
notE b = ConstE NotP :^ b

infixr 2 ||*, `xorE`
infixr 3 &&*

binop :: Prim (a -> b -> c) -> EP a -> EP b -> EP c
binop op a b = ConstE op :^ a :^ b

(&&*), (||*), xorE :: Binop (EP Bool)
(&&*) = binop AndP
(||*) = binop OrP
xorE  = binop XorP

infixl 6 +@, -@
(+@), (-@) :: Binop (EP Int)
(+@) = binop AddP
(-@) = binop SubP

-- TODO: Use Num and Boolean classes

{--------------------------------------------------------------------
    CCC conversion
--------------------------------------------------------------------}

#if 0

toCU :: EP (a :=> b) -> (Unit :-> (a :=> b))
toCU = toCCC

toC :: EP (a :=> b) -> (a :-> b)
toC = toCCC'

--     No instance for (HasUnitArrow (:->) Prim)

#endif

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

var :: Name -> EP a
var = Var . V

va,vb,vc :: EP Int
va = var "a"
vb = var "b"
vc = var "c"

e1 :: EP Bool
e1 = ConstE (LitP (BoolL False))

e2 :: EP Bool
e2 = notE e1

infixr 1 :+>
type a :+> b = EP (a -> b)

-- not
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

{- 

Without Simplify and without Sugared:

  > toC e3
  apply . (curry (not . exr) . it &&& id)
  > toC e4
  id
  > toC e5
  apply . (apply . (*** Exception: unitArrow: not yet handled: add
  > toC e6
  apply . (apply . (curry (curry id . exr) . it &&& id) &&& id)
  > toC e7
  apply . (curry (not . exr) . it &&& apply . (apply . (curry (curry (uncurry (&&)) . exr) . it &&& apply . (curry (not . exr) . it &&& id . exl)) &&& apply . (curry (not . exr) . it &&& id . exr)))
  > toC e8
  apply . (apply . (curry (curry id . exr) . it &&& id . exr) &&& id . exl)
  > toC e9
  apply . (apply . (curry (curry id . exr) . it &&& apply . (apply . (curry (curry (uncurry xor) . exr) . it &&& id . exl) &&& id . exr)) &&& apply . (apply . (curry (curry (uncurry (&&)) . exr) . it &&& id . exl) &&& id . exr))
  > 

With Simplify:

  > toC e3
  not
  > toC e4
  id
  > toC e5
  *** Exception: unitArrow: not yet handled: add
  > toC e6
  id &&& id
  > toC e7
  not . uncurry (&&) . (not . exl &&& not . exr)
  > toC e8
  exr &&& exl
  > toC e9
  uncurry xor &&& uncurry (&&)

With Simplify and Sugared:

  > toC e3
  not
  > toC e4
  id
  > toC e5
  *** Exception: unitArrow: not yet handled: add
  > toC e6
  dup
  > toC e7
  not . uncurry (&&) . twiceP not
  > toC e8
  swapP
  > toC e9
  uncurry xor &&& uncurry (&&)

-}

#if 0

---- Tracking down a looping bug in optimized CCC construction

x1 :: (a :* (b :* c)) :-> c
x1 = apply . (curry (exr . exr) &&& exr)

-- x2 :: p :-> q
-- x2 = uncurry not

-- x :: p :-> q
-- x = apply . (curry (uncurry not . (it &&& id) . exr) &&& apply . (curry (exr . exr) &&& exr)) . (it &&& id)


----

-- z = apply . (curry (apply . (apply . (curry (add . exr) &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr))) &&& apply . (curry (apply . (apply . (curry (curry id . exr) &&& exl . exr) &&& exr . exr)) &&& apply . (curry (unPair . exr) &&& apply . (curry (apply . (apply . (curry (toPair . exr) &&& apply . (curry (unL . exr) &&& exl . exr)) &&& apply . (curry (unL . exr) &&& exr . exr))) &&& apply . (curry (unPair . exr) &&& apply . (curry (unB . exr) &&& apply . (curry (toB . exr) &&& apply . (curry (apply . (apply . (curry (toPair . exr) &&& apply . (curry (toL . exr) &&& apply . (apply . (curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)) &&& apply . (curry (unL . exr) &&& exl . exr)))) &&& apply . (curry (toL . exr) &&& apply . (apply . (curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)) &&& apply . (curry (unL . exr) &&& exr . exr))))) &&& apply . (curry (unPair . exr) &&& apply . (curry (unB . exr) &&& exr)))))))))) . (it &&& id)


-- okay
z1 :: a :* (d :* b) :-> ((Int :* Int) :=> Int) :* d
z1 = curry (add . exr) &&& apply . (curry (exl . exr) &&& exr)

-- -- doesn't type
-- z2 :: q
-- z2 = apply . (apply . z1 &&& apply . (curry (exr . exr) &&& exr))

-- okay
z3 :: a1 :* (a0 :* c0) :-> c0
z3 = apply . (curry (exr . exr) &&& exr)

z4 :: a0 :-> (a2 :* a1) :=> (a2 :* a1)
z4 = curry (apply . (apply . (curry (curry id . exr) &&& exl . exr) &&& exr . exr))

z5 :: a0 :-> (Pair a1 :=> (a1 :* a1))
z5 = curry (unPair . exr)

z6 :: (a1 :* (Tree Z (a0 :* a0) :* Tree Z d0)) :-> (Pair a0 :* d0)
z6 = apply . (curry (toPair . exr) &&& apply . (curry (unL . exr) &&& exl . exr)) &&& apply . (curry (unL . exr) &&& exr . exr)

z7 :: a1 :-> (((a2 :=> (a0 :=> c0)) :=> ((a2 :* a0) :=> c0)) :* ((Int :* Int) :=> Int))
z7 = curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)

-- z7 :: a1 :-> (((a2 :=> (a0 :=> c0)) :=> ((a2 :* a0) :=> c0)) :* ((Int :* Int) :=> Int))
z7' = curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)

z8 :: (a1 :* (a0 :* Tree Z c0)) :-> c0
z8 = apply . (curry (unL . exr) &&& exr . exr)

-- z9 = apply . (curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)) &&& apply . (curry (unL . exr) &&& exr . exr)

-- -- num ->
-- z7 :: (a2 :* (a1 :* Tree Z (((a0 :=> b0) :* (a0 :=> b0)) :* a0))) :-> (Tree Z b0)
-- z7 = apply . (curry (toL . exr) &&& apply . (apply . (curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)) &&& apply . (curry (unL . exr) &&& exr . exr)))

-- z7 = apply . (curry (unPair . exr) &&& apply . (curry (unB . exr) &&& apply . (curry (toB . exr) &&& apply . (curry (apply . (apply . (curry (toPair . exr) &&& apply . (curry (toL . exr) &&& apply . (apply . (curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)) &&& apply . (curry (unL . exr) &&& exl . exr)))) &&& apply . (curry (toL . exr) &&& apply . (apply . (curry (curry (apply . (apply . (exr . exl &&& apply . (curry (exl . exr) &&& exr)) &&& apply . (curry (exr . exr) &&& exr)))) &&& curry (mul . exr)) &&& apply . (curry (unL . exr) &&& exr . exr))))) &&& apply . (curry (unPair . exr) &&& apply . (curry (unB . exr) &&& exr))))))

#endif
