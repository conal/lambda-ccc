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
import qualified Control.Arrow as A
import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.ShowUtils

-- Whether to simply (fold) during show
-- #define SimplifyShow

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

showsOp2' :: (Show a, Show b) =>
             String -> Fixity -> Prec -> a -> b -> ShowS
showsOp2' = showsOp2 False -- no extra parens

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

class Evalable e where
  type ValT e
  eval :: e -> ValT e

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

-- | Primitives
data Prim :: * -> * where
  Lit  :: Show a => a -> Prim a
  Pair :: Prim (a :=> b :=> a :* b)
  Not  :: Prim (Bool :=> Bool)
  Add  :: Num a => Prim (a :* a :=> a)
  -- More here

instance Show (Prim a) where
  showsPrec p (Lit a) = showsPrec p a
  showsPrec _ Pair    = showString "(,)"
  showsPrec _ Add     = showString "add"
  showsPrec _ Not     = showString "not"

instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (Lit x) = x
  eval Pair    = (,)
  eval Add     = uncurry (+)
  eval Not     = not

{--------------------------------------------------------------------
    CCC combinator form
--------------------------------------------------------------------}

infix  0 :->
infixr 3 &&&, ***
infixr 2 |||, +++
infixr 9 :.

-- | CCC combinator expressions. Although we use standard Haskell unit,
-- cartesian product, and function types here, the intended interpretation is as
-- the categorical counterparts (terminal object, categorical products, and
-- coproducts).
data (:->) :: * -> * -> * where
  Id       :: a :-> a
  (:.)     :: (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Primitives. I'm unsure of this one. It's closer to UKonst than I like.
  Prim     :: Prim (a :=> b) -> (a :-> b)
  -- Unit
  Terminal :: a :-> Unit
  UKonst   :: Prim b -> (Unit :-> b)
  -- Products
  Fst      :: a :* b :-> a
  Snd      :: a :* b :-> b
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

instance Evalable (a :-> b) where
  type ValT (a :-> b) = a :=> b
  eval Id          = id
  eval (g :. f)    = eval g . eval f
  eval (Prim p)    = eval p
  eval Terminal    = const ()
  eval (UKonst b)  = const (eval b)
  eval Fst         = fst
  eval Snd         = snd
  eval Dup         = \ x -> (x,x)
  eval (f :*** g)  = eval f A.*** eval g
  eval InL         = Left
  eval InR         = Right
  eval Jam         = id A.||| id
  eval (f :+++ g)  = eval f A.+++ eval g
  eval Apply       = uncurry ($)
  eval (Curry h)   = curry (eval h)
  eval (Uncurry f) = uncurry (eval f)

infixr 9 @.
-- | Optimizing arrow composition
(@.) :: (b :-> c) -> (a :-> b) -> (a :-> c)
Id @. f  = f
g  @. Id = g
g  @. f  = g :. f

-- Constant morphism (more generally than 'UKonst' or 'Terminal')
konst :: Prim b -> (a :-> b)
konst b = UKonst b @. Terminal

(***) :: (a :-> c) -> (b :-> d) -> (a :* b :-> c :* d)
(***) = (:***)

(&&&) :: (a :-> c) -> (a :-> d) -> (a :-> c :* d)
f &&& g = (f *** g) @. Dup

first :: (a :-> c) -> (a :* b :-> c :* b)
first f = f *** Id

second :: (b :-> d) -> (a :* b :-> a :* d)
second g = Id *** g

(+++) :: (a :-> c) -> (b :-> d) -> (a :+ b :-> c :+ d)
(+++) = (:+++)

(|||) :: (a :-> c) -> (b :-> c) -> (a :+ b :-> c)
f ||| g = Jam @. (f +++ g)

left :: (a :-> c) -> (a :+ b :-> c :+ b)
left f = f +++ Id

right :: (b :-> d) -> (a :+ b :-> a :+ d)
right g = Id +++ g

instance Show (a :-> b) where
#ifdef SimplifyShow
  showsPrec p (UKonst b :. Terminal) = showsApp1 "konst" p b
  showsPrec p (f :*** Id) = showsApp1 "first"  p f
  showsPrec p (Id :*** g) = showsApp1 "second" p g
  showsPrec p ((f :*** g) :. Dup) = showsOp2' "&&&" (3,AssocRight) p f g
  showsPrec p (f :+++ Id) = showsApp1 "left"   p f
  showsPrec p (Id :+++ g) = showsApp1 "right"  p g
  showsPrec p (Jam :. (f :+++ g)) = showsOp2' "|||" (2,AssocRight) p f g
#endif
  showsPrec _ Id          = showString "id"
  showsPrec _ Terminal    = showString "terminal"
  showsPrec p (Prim f)    = showsPrec p f
  showsPrec p (UKonst x)  = showsApp1 "ukonst" p x
  showsPrec p (g :. f)    = showsOp2'  "."  (9,AssocRight) p g f
  showsPrec p (f :*** g)  = showsOp2' "***" (3,AssocRight) p f g
  showsPrec p (f :+++ g)  = showsOp2' "+++" (2,AssocRight) p f g
  showsPrec _ Fst         = showString "fst"
  showsPrec _ Snd         = showString "snd"
  showsPrec _ Dup         = showString "dup"
  showsPrec _ InL         = showString "inL"
  showsPrec _ InR         = showString "inR"
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
  (:*)  :: Ty a -> Ty b -> Ty (a :* b)
  (:=>) :: Ty a -> Ty b -> Ty (a :=> b)

instance Show (Ty a) where
  showsPrec _ UnitT     = showString "Unit"
  showsPrec _ IntT      = showString "Int"
  showsPrec _ BoolT     = showString "Bool"
  showsPrec p (a :*  b) = showsOp2' ":*"  (7,AssocLeft ) p a b
  showsPrec p (a :=> b) = showsOp2' ":=>" (1,AssocRight) p a b

instance IsTy Ty where
  UnitT     `tyEq` UnitT       = Just Refl
  IntT      `tyEq` IntT        = Just Refl
  BoolT     `tyEq` BoolT       = Just Refl
  (a :*  b) `tyEq` (a' :*  b') = liftA2 liftEq2 (tyEq a a') (tyEq b b')
  (a :=> b) `tyEq` (a' :=> b') = liftA2 liftEq2 (tyEq a a') (tyEq b b')
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
  showsPrec p (Const Add :^ (Const Pair :^ u :^ v)) = showsOp2' "+" (6,AssocLeft) p u v
  showsPrec p (Const Pair :^ u :^ v) = showsPair p u v
#endif
  -- showsPrec p (Var n ty) = showsVar p n ty
  showsPrec _ (Var n _) = showString n
  showsPrec p (Const c) = showsPrec p c
  showsPrec p (Lam q e) = showParen (p > 0) $
                          showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e
  showsPrec p (u :^ v) = showsApp p u v

infixr 1 #
(#) :: E a -> E b -> E (a :* b)
a # b = Const Pair :^ a :^ b

notE :: E Bool -> E Bool
notE b = Const Not :^ b

infixl 6 +@
(+@) :: Num a => E a -> E a -> E a
a +@ b = Const Add :^ (a # b)

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
convert k (u :^ v)   = Apply @. (convert k u &&& convert k v)
convert k (Lam p e)  = Curry (convert (PairP k p) e)

-- Convert a variable in context
convertVar :: Pat a -> Name -> Ty b -> Maybe (a :-> b)
convertVar (VarP x a) n b | x == n, Just Refl <- a `tyEq` b = Just Id
                          | otherwise = Nothing
convertVar UnitP _ _ = Nothing
convertVar (PairP p q) n b = 
  ((@. Snd) <$> convertVar q n b) `mplus` ((@. Fst) <$> convertVar p n b)

-- Note that we try q before p in case of shadowing.


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

e3 :: E (Bool :=> Bool)
e3 = Const Not

e4 :: E (Int :=> Int)
e4 = Lam (VarP "x" IntT) (Var "x" IntT)

e5 :: E (Int :=> Int)
e5 = Lam (VarP "x" IntT) (x +@ x)
 where
   x = Var "x" IntT

-- > evalE e1
-- False
-- > evalE e2
-- True
-- > evalE e3 True
-- False
-- > evalE e4 5
-- 5
-- > evalE e5 10
-- 20

-- > asCCC e1
-- konst False
-- > asCCC e2
-- apply . (konst not &&& konst False)
-- > asCCC e3
-- konst not
-- > asCCC e4
-- curry snd
-- > asCCC e5
-- curry (apply . (konst add &&& apply . (apply . (konst (#) &&& snd) &&& snd)))
