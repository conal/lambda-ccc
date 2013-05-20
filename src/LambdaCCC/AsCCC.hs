{-# LANGUAGE TypeOperators, GADTs, KindSignatures, PatternGuards #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.AsCCC
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert lambda expressions to CCC combinators
----------------------------------------------------------------------

module LambdaCCC.AsCCC 
  ( (:->)(..), (&&&), (***), (+++), (|||), konst
  , first, second, left, right
  , Name, Op(..), E(..), Pat(..)
  , asCCC
  ) where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.Type

{--------------------------------------------------------------------
    CCC combinator form
--------------------------------------------------------------------}

infix  0 :->
infixr 3 &&&, ***
infixr 3 |||, +++

-- | CCC combinator expressions. Although we use standard Haskell unit,
-- cartesian product, and function types here, the intended interpretation is as
-- the categorical counterparts (terminal object, categorical products, and
-- coproducts).
data (:->) :: * -> * -> * where
  Id       :: a :-> a
  (:.)     :: (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Unit
  Terminal :: a :-> Unit
  UKonst   :: b -> (Unit :-> b)
  -- Products
  OutL     :: a :* b :-> a
  OutR     :: a :* b :-> b
  Dup      :: a :-> a :* a
  (:***)   :: (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
  -- Coproducts
  InL      :: a :-> a :+ b
  InR      :: b :-> a :+ b
  Jam      :: a :+ a :-> a
  (:+++)   :: (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
  -- Exponentials
  Apply    :: ((a :=> b) :* a) :-> b
  Curry    :: (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry  :: (a :-> (b :=> c)) -> (a :* b :-> c)
  -- Primitive arrows. Do we want exponentials instead?
  AddA     :: Num a => (a :* a) :-> a
  -- and more primitives ...

-- Constant morphism (more generally than 'UKonst' or 'Terminal')
konst :: b -> (a :-> b)
konst b = UKonst b :. Terminal

(***) :: (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
(***) = (:***)

(&&&) :: (a :-> c) -> (a :-> d) -> (a :-> c :* d)
f &&& g = (f *** g) :. Dup

first :: (a :-> c) -> (a :* b :-> c :* b)
first f = f *** Id

second :: (b :-> d) -> (a :* b :-> a :* d)
second g = Id *** g

(+++) :: (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
(+++) = (:+++)

(|||) :: (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
f ||| g = Jam :. (f +++ g)

left :: (a :-> c) -> (a :+ b :-> c :+ b)
left f = f +++ Id

right :: (b :-> d) -> (a :+ b :-> a :+ d)
right g = Id +++ g

{--------------------------------------------------------------------
    Lambda expressions
--------------------------------------------------------------------}

-- | Variable names
type Name = String

-- | Primitives
data Op :: * -> * where
  Lit :: Show a => a -> Op a
  Add :: Num a => Op (a :* a :=> a)

-- | Lambda expressions
data E :: * -> * where
  Var   :: Name -> Ty a -> E a
  Const :: Op a -> E a
  App   :: E (a :=> b) -> E a -> E b
  Lam   :: Pat a -> E b -> E (a :=> b)

-- | Lambda patterns
data Pat :: * -> * where
  UnitP :: Pat Unit
  VarP  :: Name -> Ty a -> Pat a
  PairP :: Pat a -> Pat b -> Pat (a :* b)

-- | Variable binding context
type Context = Pat

-- | Rewrite a lambda expression via CCC combinators
asCCC :: E a -> (Unit :-> a)
asCCC = convert UnitP

-- | Convert @\ p -> e@ to CCC combinators
convert :: Pat a -> E b -> (a :-> b)
convert _ (Const o) = konst (evalOp o)
convert k (Var n t) = fromMaybe (error $ "unbound variable: " ++ n) $
                      convertVar k n t
convert k (App u v) = Apply :. (convert k u &&& convert k v)
convert k (Lam p e) = Curry (convert (PairP k p) e)

evalOp :: Op b -> b
evalOp (Lit c) = c
evalOp Add     = uncurry (+)

convertVar :: Context q -> Name -> Ty a -> Maybe (q :-> a)
convertVar (VarP x q) n a | x == n, Just Refl <- q `tyEq` a = Just Id
                          | otherwise = Nothing
convertVar UnitP _ _ = Nothing
convertVar (PairP q r) n a = 
  ((:. OutL) <$> convertVar q n a) `mplus` ((:. OutR) <$> convertVar r n a)
