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
toCCC a | HasTy <- tyHasTy (expTy a)
        = convert UnitPat a

toCCC' :: E (a :=> b) -> (a :-> b)
toCCC' e | (HasTy,HasTy) <- tyHasTy2 a b = toCCC'' e
 where
   (a,b) = splitFunTy (expTy e)

toCCC'' :: HasTy2 a b => E (a :=> b) -> (a :-> b)
toCCC'' (Lam p e) = convert p e
toCCC'' e = toCCC'' (Lam vp (e :^ ve))
 where
   (vp,ve) = vars "ETA"

-- | Convert @\ p -> e@ to CCC combinators
convert :: HasTy2 a b => Pat a -> E b -> (a :-> b)
convert _ (Const o _) = Konst o
convert k (Var v)    = fromMaybe (error $ "unbound variable: " ++ show v) $
                       convertVar v k
-- convert k (u :# v)   = convert k u &&& convert k v
convert k (Const PairP (tu :=> tv :=> _) :^ u :^ v)
  | (HasTy,HasTy) <- tyHasTy2 tu tv
  = convert k u &&& convert k v
convert k (u :^ v)
  | HasTy <- tyHasTy (domTy (expTy u))
  = Apply @. (convert k u &&& convert k v)

convert k (Lam p e)  | (HasTy,HasTy) <- tyHasTy2 (patTy p) (expTy e)
                     = Curry (convert (PairPat k p) e)

-- Convert a variable in context
convertVar :: forall b a. HasTy2 a b => V b -> Pat a -> Maybe (a :-> b)
convertVar b = conv
 where
   conv :: forall c. HasTy2 c b => Pat c -> Maybe (c :-> b)
   conv (VarPat c) | Just Refl <- c `tyEq` b
                   -- , HasTy <- tyHasTy (varTy c)
                   = Just Id
                   | otherwise = Nothing
   conv UnitPat = Nothing
   conv (PairPat p q) | (HasTy,HasTy) <- tyHasTy2 (patTy p) (patTy q)
                      = ((@. Snd) <$> conv q) `mplus` ((@. Fst) <$> conv p)

-- Alternatively,
-- 
--    conv (PairPat p q) = descend Snd q `mplus` descend Fst p
--     where
--       descend :: (c :-> d) -> Pat d -> Maybe (c :-> b)
--       descend sel r = (@. sel) <$> conv r

-- Note that we try q before p. This choice cooperates with uncurrying and
-- shadowing.
