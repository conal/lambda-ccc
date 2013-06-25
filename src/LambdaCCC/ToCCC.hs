{-# LANGUAGE TypeOperators, GADTs, PatternGuards, ScopedTypeVariables #-}
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

module LambdaCCC.ToCCC (toCCC, toCCC') where

import Data.Functor ((<$>))
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.CCC
import LambdaCCC.Ty
import LambdaCCC.Lambda
import LambdaCCC.Prim (Prim(PairP))

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

-- | Rewrite a lambda expression via CCC combinators
toCCC :: E a -> (Unit :-> a)
toCCC = convert UnitPat

toCCC' :: HasTy a => E (a :=> b) -> (a :-> b)
toCCC' (Lam p e) = convert p e
toCCC' e = toCCC' (Lam vp (e :^ ve))
 where
   (vp,ve) = vars "ETA"

-- | Convert @\ p -> e@ to CCC combinators
convert :: Pat a -> E b -> (a :-> b)
convert _ (Const o _)  = Konst o
convert k (Var v)    = fromMaybe (error $ "unbound variable: " ++ show v) $
                       convertVar v k
-- convert k (u :# v)   = convert k u &&& convert k v
convert k (Const PairP _ :^ u :^ v)  = convert k u &&& convert k v
convert k (u :^ v)   = Apply @. (convert k u &&& convert k v)
                  -- = Apply @. convert k (u # v)
convert k (Lam p e)  = Curry (convert (PairPat k p) e)

-- Convert a variable in context
convertVar :: forall b a. V b -> Pat a -> Maybe (a :-> b)
convertVar b = conv
 where
   conv :: forall c. Pat c -> Maybe (c :-> b)
   conv (VarPat c) | Just Refl <- c `tyEq` b = Just Id
                   | otherwise = Nothing
   conv UnitPat = Nothing
   conv (PairPat p q) = ((@. Snd) <$> conv q) `mplus` ((@. Fst) <$> conv p)

-- Alternatively,
-- 
--    conv (PairPat p q) = descend Snd q `mplus` descend Fst p
--     where
--       descend :: (c :-> d) -> Pat d -> Maybe (c :-> b)
--       descend sel r = (@. sel) <$> conv r

-- Note that we try q before p. This choice cooperates with uncurrying and
-- shadowing.
