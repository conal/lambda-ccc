{-# LANGUAGE TypeOperators, GADTs #-}
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

module LambdaCCC.AsCCC (asCCC, asCCC') where

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.Prim
import LambdaCCC.Ty
import LambdaCCC.CCC
import LambdaCCC.Lambda

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
