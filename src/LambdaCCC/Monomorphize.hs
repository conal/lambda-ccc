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

import Control.Category (id,(.))
import Control.Arrow (first,second,arr,(>>>))
import Control.Applicative (liftA2)
import Control.Monad ((=<<),(>=>))
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

import HERMIT.Extras (pattern FunCo, fqVarName, exprType', exprTypeT)

import Monomorph.Stuff (pruneCaseR,standardizeCase,standardizeCon)

type UnopM m a = a -> m a

-- repName :: String -> HermitName
-- repName = mkQualified "Circat.Rep"

type MonadNuff m = ( MonadIO m, MonadCatch m, MonadUnique m, MonadThings m
                   , HasDynFlags m, HasHermitMEnv m, LiftCoreM m, HasLemmas m )

type ContextNuff c = ( ReadPath c Crumb, ExtendPath c Crumb
                     , LemmaContext c
                     , AddBindings c, ReadBindings c, HasEmptyContext c )

type Nuff c m = (ContextNuff c, MonadNuff m)

monomorphizeE :: Nuff c m => Rewrite c m CoreExpr
monomorphizeE = transform (mono [])

type Trans a b = forall c m . Nuff c m => c -> a -> m b

type Rew a = forall c m . Nuff c m => c -> a -> m a

-- type Rew a = Trans a a

type Stack = [CoreExpr]                 -- argument stack

-- Monomorphize in the context of a stack of applications (innermost first).
mono :: Stack -> Rew CoreExpr
mono args c = go
 where
   go e = -- pprTrace "mono/go:" (ppr e) $
          applyT (observeR "mono/go") c e >>
          case e of
     Var v | isTyVar v -> mpanic (text "type variable:" <+> ppr v) -- maybe allow
     Var v -> inlineNonPrim v `rewOr` bail
     Lam v body ->
       case args of
         rhs : args' -> mono args' c (mkCoreLet (NonRec v rhs) body)
         []          -> Lam v <$> go body
     App fun arg -> mono (arg : args) c fun

     Let (NonRec v rhs) body
       | v `notElemVarSet` freeVarsExpr body ->
           pprTrace "go" (text "let-elim" <+> ppr v) $
           go body
       | otherwise ->
          (guardMsg (exprIsTrivial rhs) "non-trivial" >> letSubstR')
           `rewOr` (mkCoreLet <$> (NonRec v <$> mono0 rhs) <*> go body)
       where
         letSubstR' = bracketR "letSubstR" letSubstR

     -- TODO: batch up these eliminations and substitutions. Or have GHC do them at the end.
     -- TODO: Is there a cheaper way to check whether v occurs freely in body
     -- without having to collect all of the free variables in a set?

     Let (Rec _) _ -> bail -- spanic "recursive let"

--      Case scrut w ty alts ->
--        caseReduceUnfoldR' `rewOr`
--        standardizeCase `rewOr`
--          (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)
--       where
--         caseReduceUnfoldR' =
--           {-bracketR "caseReduceUnfoldR"-} (caseReduceUnfoldR False)

     Case scrut w ty alts ->
       caseReduceUnfoldR' `rewOr`
         case alts of
           (_:_:_) -> bracketR "pruneCaseR" pruneCaseR `rewOr` bail
           _       -> (Case <$> mono0 scrut <*> pure w <*> pure ty
                            <*> mapM (onAltRhsM go) alts)
      where
        caseReduceUnfoldR' =
          {-bracketR "caseReduceUnfoldR"-} (caseReduceUnfoldR False)


--      Case scrut w ty alts@[_] ->
--        (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)
--      Case {} -> (bracketR "pruneCaseR" pruneCaseR) `rewOr` bail

--      Case scrut _ _ _  ->
--        (guardMsg (isMono scrut) "Poly" >> caseReduceUnfoldR') `rewOr` bail
--           -- (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)
--       where
--         caseReduceUnfoldR' =
--           {-bracketR "caseReduceUnfoldR"-} (caseReduceUnfoldR False)

     -- Still to address: monomorphic recursion.

     -- Float casts through the implied applications.
     Cast body (FunCo _r dom ran) | arg:more <- args ->
       mono more c (mkCast (mkCoreApp body (mkCast arg (mkSymCo dom))) ran)
     Cast body (ForAllCo v ran) | Type t : more <- args ->
       mono more c (mkCast (mkCoreApp body (Type t))
                           (substCo (extendTvSubst emptySubst v t) ran))
     Cast body co ->
       mkCoreApps <$> (flip mkCast co <$> mono0 body) <*> mapM mono0 args

     Tick t body -> Tick t <$> go body
     Coercion co -> return (Coercion co)
     -- Type, Lit, Coercion
     _ | null args -> return e
     _ ->
       mpanic (text "Surprisingly argumentative: " <+> ppr (mkCoreApps e args))
    where
      -- All arguments consumed. Retry with empty stack
      mono0 = mono [] c
      -- rewOr :: Rewrite c m a -> m a -> a -> m a
      infixl 4 `rewOr`
      rew `rewOr` ma = catchMaybe (applyT rew c e) >>= maybe ma go
      bail = mkCoreApps e <$> mapM mono0 args

-- TODO: Prune case expressions to stop recursion.

isMono :: CoreExpr -> Bool
isMono = isMonoTy . exprType'

isMonoTy :: Type -> Bool
isMonoTy (coreView -> Just ty) = isMonoTy ty
isMonoTy (TyVarTy _)           = False
isMonoTy (AppTy u v)           = isMonoTy u && isMonoTy v
isMonoTy (TyConApp _ tys)      = all isMonoTy tys
isMonoTy (FunTy u v)           = isMonoTy u && isMonoTy v
isMonoTy (ForAllTy {})         = False
isMonoTy (LitTy _)             = True

-- mono/go/case bailing. case scrutinee has poly type RTree N1 Int


inlineNonPrim :: Nuff c m => Var -> Rewrite c m CoreExpr
inlineNonPrim v = bracketR "inlineNonPrim" $
                  guardMsg (not (isPrim v)) "mono inlineNonPrim: primitive" >>
                  inlineR

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
