{-# LANGUAGE TypeOperators, GADTs, PatternGuards, ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds, Rank2Types, CPP #-}
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

module LambdaCCC.ToCCC (toCCC, HasLambda(..)) where

import Prelude hiding (id,(.),curry,uncurry,const)

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.Prim (Prim)
import LambdaCCC.Lambda
import LambdaCCC.CCC ((:->)(Const))     -- Remaining dependency

import Circat.Category

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

-- toCCC' :: E a -> (Unit :-> a)
-- toCCC' = convert UnitPat

-- | Rewrite a lambda expression via CCC combinators
toCCC :: E (a :=> b) -> (a :-> b)
toCCC (Lam p e) = convert e p
toCCC e = toCCC (Lam vp (e :^ ve))
 where
   (vp,ve) = vars "ETA"

#if 0

-- | Convert @\ p -> e@ to CCC combinators
convert :: forall a b k. (BiCCC k, k ~ (:->))  =>
           E b -> Pat a -> (a `k` b)
convert (ConstE o)   _ = Const o
convert (Var v)      k = convertVar v k
convert (u :^ v)     k = apply . (convert u k &&& convert v k)
convert (Lam p e)    k = curry (convert e (k :# p))
convert (Either f g) k = curry ((convert' f ||| convert' g) . ldistribS)
 where
   convert' :: E (p :=> q) -> ((a :* p) `k` q)
   convert' h = uncurry (convert h k)

#else

-- | Generation of CCC terms in a binding context
type Ex b = forall a. Pat a -> (a :-> b)

-- TODO:
-- 
--   type Ex b = forall a k. BiCCC k => Pat a -> (a `k` b)

constEx  :: Prim a -> Ex a
varEx    :: V a -> Ex a
appEx    :: Ex (a :=> b) -> Ex a -> Ex b
lamEx    :: Pat a -> Ex b -> Ex (a :=> b)
eitherEx :: Ex (a -> c) -> Ex (b -> c) -> Ex (a :+ b -> c)

constEx o    _ = Const o
varEx x      k = convertVar x k
appEx u v    k = apply . (u k &&& v k)
lamEx p e    k = curry (e (k :# p))
eitherEx f g k = curry ((uncurry (f k) ||| uncurry (g k)) . ldistribS)

-- | Convert @\ p -> e@ to CCC combinators
convert :: E b -> Ex b
convert (ConstE o)   = constEx o
convert (Var v)      = varEx v
convert (s :^ t)     = convert s `appEx` convert t
convert (Lam p e)    = lamEx p (convert e)
convert (Either f g) = convert f `eitherEx` convert g

-- instance HasLambda Ex where
--   constE  = constEx
--   varE    = varEx
--   appE    = appEx
--   lamE    = lamEx
--   eitherE = eitherEx

-- Oops. Ex is a type synonym, not a constructor. I'd have to use a newtype.

#endif

class HasLambda expr where
  constE  :: Prim a -> expr a
  varE    :: V a -> expr a
  appE    :: expr (a :=> b) -> expr a -> expr b
  lamE    :: Pat a -> expr b -> expr (a :=> b)
  eitherE :: expr (a -> c) -> expr (b -> c) -> expr (a :+ b -> c)

instance HasLambda E where
  constE  = ConstE
  varE    = Var
  appE    = (:^)
  lamE    = Lam
  eitherE = Either

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
   conv (VarPat v) | Just Refl <- v ==? u = Just id
                   | otherwise            = Nothing
   conv UnitPat  = Nothing
   conv (p :# q) = ((. exr) <$> conv q) `mplus` ((. exl) <$> conv p)
   conv (p :@ q) = conv q `mplus` conv p

-- Alternatively,
-- 
--    conv (p :# q) = descend Exr q `mplus` descend Exl p
--     where
--       descend :: (c `k` d) -> Pat d -> Maybe (c `k` b)
--       descend sel r = (@. sel) <$> conv r

-- Note that we try q before p. This choice cooperates with uncurrying and
-- shadowing.
