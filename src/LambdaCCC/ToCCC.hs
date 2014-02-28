{-# LANGUAGE TypeOperators, GADTs, PatternGuards, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds, RankNTypes, CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ToCCC
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert lambda expressions to CCC combinators
----------------------------------------------------------------------

module LambdaCCC.ToCCC (toCCC, toCCC' {-, HasLambda(..) -}) where

import Prelude hiding (id,(.),curry,uncurry,const,not,and,or)

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.Proof.EQ

-- #define PlainConvert

import LambdaCCC.Misc
import LambdaCCC.Lambda (E(..),V,Pat(..))
import Circat.Category

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

#ifdef PlainConvert

-- | Rewrite a lambda expression via CCC combinators
toCCC :: BiCCCC k p => E p a -> (Unit `k` a)
toCCC e = convert e UnitPat

-- | Convert @\ p -> e@ to CCC combinators
convert :: forall a b prim k. BiCCCC k prim =>
           E prim b -> Pat a -> (a `k` b)
convert (ConstE x)   _ = unitArrow x . it
convert (Var v)      p = convertVar v p
convert (u :^ v)     p = apply . (convert u p &&& convert v p)
convert (Lam q e)    p = curry (convert e (p :# q))
convert (Either f g) p = curry ((convert' f ||| convert' g) . ldistribS)
 where
   convert' :: E prim (c :=> d) -> ((a :* c) `k` d)
   convert' h = uncurry (convert h p)

#else

infixl 9 @@
infixr 2 ||||

class HasLambda e where
  type PrimT e :: * -> *
  constL :: PrimT e a -> e a
  varL   :: V a -> e a
  (@@)   :: e (a :=> b) -> e a -> e b
  lamL   :: Pat a -> e b -> e (a :=> b)
  (||||) :: e (a -> c) -> e (b -> c) -> e (a :+ b -> c)

instance HasLambda (E p) where
  type PrimT (E p) = p
  constL = ConstE
  varL   = Var
  (@@)   = (:^)
  lamL   = Lam
  (||||) = Either

-- | Generation of CCC terms in a binding context
newtype MkC prim b =
  MkC { unMkC :: forall a k. BiCCCC k prim => Pat a -> (a `k` b) }

instance HasLambda (MkC prim) where
  type PrimT (MkC prim) = prim
  constL x         = MkC (\ _ -> unitArrow x . it)
  varL y           = MkC (\ p -> convertVar y p)
  MkC u @@ MkC v   = MkC (\ p -> apply . (u p &&& v p))
  lamL q (MkC u)   = MkC (\ p -> curry (u (p :# q)))
  MkC f |||| MkC g =
    MkC (\ p -> curry ((uncurry (f p) ||| uncurry (g p)) . distl))

-- | Convert from 'E' to another 'HasLambda' with the same primitives:
convert :: HasLambda ex => E (PrimT ex) b -> ex b
convert (ConstE o)   = constL o
convert (Var v)      = varL v
convert (s :^ t)     = convert s @@ convert t
convert (Lam p e)    = lamL p (convert e)
convert (Either f g) = convert f |||| convert g

-- | Rewrite a lambda expression via CCC combinators
toCCC :: BiCCCC k p => E p a -> (Unit `k` a)
toCCC e = unMkC (convert e) UnitPat

-- A universal instance of 'HasLambda', with 'PrimT' @p@.
newtype Lambda p a = L (forall f . (HasLambda f, PrimT f ~ p) => f a)

instance HasLambda (Lambda p) where
  type PrimT (Lambda p) = p
  constL o     = L (constL o)
  varL x       = L (varL x)
  L u @@ L v   = L (u @@ v)
  lamL p (L u) = L (lamL p u)
  L f |||| L g = L (f |||| g)

#endif

-- | Variant on 'toCCC'
toCCC' :: BiCCCC k p => E p (a :=> b) -> (a `k` b)
toCCC' = unUnitFun . toCCC

-- TODO: Handle constants in a generic manner, so we can drop the constraint that k ~ (:->).

-- convert k (Case (a,p) (b,q) ab) =
--   (convert (k :# a) p ||| convert (k :# b) q) . ldistribS . (Id &&& convert k ab)

-- Convert a variable in context
convertVar :: forall b a k. ProductCat k =>
              V b -> Pat a -> (a `k` b)
convertVar u = fromMaybe (error $ "convert: unbound variable: " ++ show u) .
               conv
 where
   conv :: forall c. Pat c -> Maybe (c `k` b)
   conv (VarPat v) | Just Refl <- v ===? u = Just id
                   | otherwise             = Nothing
   conv UnitPat  = Nothing
   conv (p :# q) = ((. exr) <$> conv q) `mplus` ((. exl) <$> conv p)
   conv (p :@ q) = conv q `mplus` conv p

-- Note that we try q before p. This choice cooperates with uncurrying and
-- shadowing.

-- Alternatively,
-- 
--    conv (p :# q) = descend exr q `mplus` descend exl p
--     where
--       descend :: (c `k` d) -> Pat d -> Maybe (c `k` b)
--       descend sel r = (. sel) <$> conv r

