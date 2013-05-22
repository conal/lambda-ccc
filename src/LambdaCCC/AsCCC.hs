{-# LANGUAGE TypeOperators, GADTs, KindSignatures, PatternGuards #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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
  , Prim(..)
  , first, second, left, right
  , Name, E(..), Pat(..)
  , asCCC
  ) where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Control.Applicative (liftA2)
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.ShowUtils

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

infixr 1 :=>
infixl 6 :+
infixl 7 :*

-- TODO: Perhaps replace these definitions with a GADT to emphasize the
-- distinction between standard Haskell unit, cartesian product, and function
-- types, vs the categorical counterparts (terminal object, categorical
-- products, and coproducts).

type Unit  = ()
type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

-- | Primitives
data Prim :: * -> * where
  Lit  :: Show a => a -> Prim a
  Pair :: Prim (a :=> b :=> a :* b)
  Add  :: Num a => Prim (a :* a :=> a)
  -- More here

instance Show (Prim a) where
  showsPrec p (Lit a) = showsPrec p a
  showsPrec _ Add     = showString "add"
  showsPrec _ Pair    = showString "(#)"

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
  UKonst   :: Prim b -> (Unit :-> b)
  -- Products
  Fst      :: a :* b :-> a
  Snd      :: a :* b :-> b
  Dup      :: a :-> a :* a
  (:***)   :: (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
  -- Coproducts
  Lft      :: a :-> a :+ b
  Rht      :: b :-> a :+ b
  Jam      :: a :+ a :-> a
  (:+++)   :: (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
  -- Exponentials
  Apply    :: ((a :=> b) :* a) :-> b
  Curry    :: (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry  :: (a :-> (b :=> c)) -> (a :* b :-> c)

-- Constant morphism (more generally than 'UKonst' or 'Terminal')
konst :: Prim b -> (a :-> b)
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

instance Show (a :-> b) where
  showsPrec p (f :*** Id) = showsApp1 "first"  p f
  showsPrec p (Id :*** g) = showsApp1 "second" p g
  showsPrec _ Id          = showString "id"
  showsPrec _ Terminal    = showString "terminal"
  showsPrec p (UKonst x)  = showsApp1 "ukonst" p x
  showsPrec p (g :. f)    = showsOp2 False  "."  (9,AssocRight) p g f
  showsPrec p (f :*** g)  = showsOp2 False "***" (3,AssocRight) p f g
  showsPrec p (f :+++ g)  = showsOp2 False "+++" (2,AssocRight) p f g
  showsPrec _ Fst         = showString "fst"
  showsPrec _ Snd         = showString "snd"
  showsPrec _ Dup         = showString "dup"
  showsPrec _ Lft         = showString "lft"
  showsPrec _ Rht         = showString "rht"
  showsPrec _ Jam         = showString "jam"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry f)   = showsApp1  "curry" p f
  showsPrec p (Uncurry h) = showsApp1  "Uncurry" p h

{--------------------------------------------------------------------
    Types
--------------------------------------------------------------------}

-- | Typed type representation
data Ty :: * -> * where
  UnitT :: Ty Unit
  IntT  :: Ty Int
  BoolT :: Ty Bool
  PairT :: Ty a -> Ty b -> Ty (a :* b)
  FunT  :: Ty a -> Ty b -> Ty (a :=> b)

instance Show (Ty a) where
  showsPrec _ UnitT       = showString "Unit"
  showsPrec _ IntT        = showString "Int"
  showsPrec _ BoolT       = showString "Bool"
  showsPrec p (PairT a b) = showsOp2 extraParens ":*"  (7,AssocLeft ) p a b
  showsPrec p (FunT a b)  = showsOp2 extraParens ":=>" (1,AssocRight) p a b

extraParens :: Bool
extraParens = True

instance IsTy Ty where
  UnitT     `tyEq` UnitT       = Just Refl
  IntT      `tyEq` IntT        = Just Refl
  BoolT     `tyEq` BoolT       = Just Refl
  PairT a b `tyEq` PairT a' b' = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  FunT  a b `tyEq` FunT  a' b' = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  _         `tyEq` _           = Nothing

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

-- | Lambda expressions
data E :: * -> * where
  Var   :: Name -> Ty a -> E a
  Const :: Prim a -> E a
  App   :: E (a :=> b) -> E a -> E b
  Lam   :: Pat a -> E b -> E (a :=> b)

instance Show (E a) where
  -- showsPrec p (Var n ty) = showsVar p n ty
  showsPrec _ (Var n _) = showString n
  showsPrec p (Const c) = showsPrec p c
  showsPrec p (Lam q e) = showParen (p > 0) $
                          showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e
  showsPrec p (App (App (Const Pair) u) v) = showsPair p u v
  showsPrec p (App u v) = showsApp p u v

infixl 9 @^
(@^) :: E (a :=> b) -> E a -> E b
(@^) = App

infixr 1 #
(#) :: E a -> E b -> E (a :* b)
a # b = Const Pair @^ a @^ b

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

-- | Rewrite a lambda expression via CCC combinators
asCCC :: E a -> (Unit :-> a)
asCCC = convert UnitP

-- | Convert @\ p -> e@ to CCC combinators
convert :: Pat a -> E b -> (a :-> b)
convert _ (Const o)  = konst o
convert k (Var n t)  = fromMaybe (error $ "unbound variable: " ++ n) $
                       convertVar k n t
convert k (App u v)  = Apply :. (convert k u &&& convert k v)
convert k (Lam p e)  = Curry (convert (PairP k p) e)

-- Convert a variable in context
convertVar :: Pat a -> Name -> Ty b -> Maybe (a :-> b)
convertVar (VarP x a) n b | x == n, Just Refl <- a `tyEq` b = Just Id
                          | otherwise = Nothing
convertVar UnitP _ _ = Nothing
convertVar (PairP p q) n b = 
  ((:. Snd) <$> convertVar q n b) `mplus` ((:. Fst) <$> convertVar p n b)

-- Note that we try q before p in case of shadowing.


{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

va,vb,vc :: E Int
va = Var "a" IntT
vb = Var "b" IntT
vc = Var "c" IntT

e1 :: E Int
e1 = Const Add @^ (va # vb)

e2 :: E (Int :* Int)
e2 = va # vb
