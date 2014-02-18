{-# LANGUAGE TypeOperators, GADTs, PatternGuards, ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
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

module LambdaCCC.ToCCC (toCCC) where

import Prelude hiding (id,(.),curry,uncurry,const)

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.Proof.EQ

import LambdaCCC.Misc
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
toCCC (Lam p e) = convert p e
toCCC e = toCCC (Lam vp (e :^ ve))
 where
   (vp,ve) = vars "ETA"

-- | Convert @\ p -> e@ to CCC combinators
convert :: forall a b k. (CCCC k, k ~ (:->))  =>
           Pat a -> E b -> (a `k` b)
convert _ (ConstE o)   = Const o
convert k (Var v)      = convertVar v k
convert k (u :^ v)     = apply . (convert k u &&& convert k v)
convert k (Lam p e)    = curry (convert (k :# p) e)
convert k (Either f g) = curry ((convert' f ||| convert' g) . ldistribS)
 where
   convert' :: E (p :=> q) -> ((a :* p) `k` q)
   convert' h = uncurry (convert k h)

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
