{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Monomorphize
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Efficient monomorphization
----------------------------------------------------------------------

module LambdaCCC.Monomorphize (monomorphizeE) where

import Prelude hiding (id,(.))

import Data.Traversable (mapAccumL)
import Control.Category (id,(.))
import Control.Arrow (first,second,arr,(>>>))
import Control.Monad ((=<<))
import qualified Data.Set as S
import Control.Monad.IO.Class (MonadIO)

import Language.KURE
import HERMIT.Context
import HERMIT.Core
import HERMIT.Dictionary
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

-- TODO: Tighten imports

import HERMIT.Extras (pattern FunCo, fqVarName)

type Unop a = a -> a
type UnopM m a = a -> m a

repName :: String -> HermitName
repName = mkQualified "Circat.Rep"

type MonadNuff m = ( MonadIO m, MonadCatch m, MonadUnique m, MonadThings m
                   , HasDynFlags m, HasHermitMEnv m, LiftCoreM m, HasLemmas m )

type ContextNuff c = ( ReadPath c Crumb, ExtendPath c Crumb
                     , LemmaContext c
                     , AddBindings c, ReadBindings c, HasEmptyContext c )

type Nuff c m = (ContextNuff c, MonadNuff m)

monomorphizeE :: Nuff c m => Rewrite c m CoreExpr
monomorphizeE = transform (mono [])

type Rew a = forall c m . Nuff c m => c -> a -> m a

type Stack = [CoreExpr]                 -- argument stack

-- Monomorphize in the context of a stack of applications (innermost first).
mono :: Stack -> Rew CoreExpr
mono args c = go
 where
   -- go e | pprTrace "mono/go:" (ppr e) False = error "Wat!"
   go (Var v) | isTyVar v = mpanic (text "type variable: " <+> ppr v)
              | otherwise =
     maybeInline c v >>= maybe (mkCoreApps (Var v) <$> mapM mono0 args) go
   go (Lam v body) =
     case args of
       rhs : args' -> mono args' c (mkCoreLet (NonRec v rhs) body)
       []          -> Lam v <$> go body
   go (App fun arg) = mono (arg : args) c fun
   go e@(Let (NonRec v rhs) body)
     | isTyVar v = go =<< applyT letSubstR c e  -- TODO: make more efficient
     | otherwise = mkCoreLet <$> (NonRec v <$> mono0 rhs) <*> go body
   go (Let (Rec _) _) = spanic "recursive let" 
   go (Case scrut w ty alts) =
     Case <$> mono0 scrut <*> pure w <*> pure ty
          <*> mapM (onAltRhsM go) alts
   go (Cast e co) = mono args' c (mkCast e co')
    where
      (co',args') = dropCoArgs co args
   go (Tick t e) = Tick t <$> go e
   go (Coercion co) = return (Coercion co)
   -- Type, Lit, Coercion
   go e | null args = return e
   go e =
     mpanic (text "Surprisingly argumentative: " <+> ppr (mkCoreApps e args))
   -- All arguments consumed. Retry with empty stack
   mono0 = mono [] c

-- TODO: Prune case expressions to stop recursion.

dropCoArgs :: Coercion -> Stack -> (Coercion,Stack)
dropCoArgs = mapAccumL trim
 where
   trim :: Coercion -> CoreExpr -> (Coercion,CoreExpr)
   trim (FunCo _r dom ran) arg = (ran, mkCast arg (SymCo dom))
   trim (ForAllCo v ran) (Type t) =
     (substCo (extendTvSubst emptySubst v t) ran, Type t)
   trim co _ = mpanic (text "dropCoArgs found odd coercion: " <+> ppr co)

-- TODO: Consider reworking dropCoArgs to return list of coercions (possibly
-- Refl), or even CoreExpr unops.

-- mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)

maybeInline :: Nuff c m => c -> Id -> m (Maybe CoreExpr)
maybeInline c v | isPrim v  = return Nothing
                | otherwise = catchMaybe (applyT inlineR c (Var v))

isPrim :: Id -> Bool
isPrim v = fqVarName v `S.member` primNames

-- Heading here:
-- 
-- Translate function names to cat class and prim
-- primNames :: M.Map String (String,String)

-- See current stdMeths in Reify for list of methods, classes, etc.

primNames :: S.Set String
primNames = S.fromList
   [ "GHC.Num.$fNum"++ty++"_$c"++meth
   | (tys,meths) <- prims , ty <- tys, meth <- meths ]
 where
   prims = [( ["Int","Double"]
            , ["+","-","*","negate","abs","signum","fromInteger"])]
   -- TODO: more primitives, including boolean

--   D:Num @ Int $fNumInt_$c+ $fNumInt_$c- $fNumInt_$c* $fNumInt_$cnegate
--               $fNumInt_$cabs $fNumInt_$csignum $fNumInt_$cfromInteger

catchMaybe :: MonadCatch m => m a -> m (Maybe a)
catchMaybe ma = fmap Just ma <+ return Nothing

onAltRhsM :: Functor m => UnopM m CoreExpr -> UnopM m CoreAlt
onAltRhsM f (con,bs,rhs) = (con,bs,) <$> f rhs

mpanic :: SDoc -> a
mpanic = pprPanic "mono"

spanic :: String -> a
spanic = mpanic . text

stackable :: CoreExpr -> Bool
stackable e = isTypeArg e || dictishTy (exprType e)

dictishTy :: Type -> Bool
dictishTy (coreView -> Just ty) = dictishTy ty
dictishTy (ForAllTy _ ty)       = dictishTy ty
dictishTy (FunTy dom ran)       = dictishTy dom || dictishTy ran
dictishTy ty                    = isDictLikeTy ty
