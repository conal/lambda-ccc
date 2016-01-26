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

module LambdaCCC.Monomorphize (monomorphizeE,externals) where

import Prelude hiding (id,(.))

import Control.Category (id,(.))
import Control.Arrow (first,second,arr,(>>>))
import Control.Applicative (liftA2)
import Control.Monad ((=<<),(>=>))
import qualified Data.Set as S
import Control.Monad.IO.Class (MonadIO)
import Data.Maybe (isJust)

import Language.KURE
import HERMIT.Context
import HERMIT.Core
import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

-- GHC
import Unique (hasKey)
import PrelNames (eqPrimTyConKey,eqReprPrimTyConKey)

-- TODO: Tighten imports

import HERMIT.Extras
  (pattern FunCo, fqVarName, exprType', exprTypeT, ReExpr,($*),externC',onScrutineeR)

-- import Monomorph.Stuff (pruneCaseR,standardizeCase,standardizeCon,hasRepMethodF)

type Unop a = a -> a

watchR :: String -> Unop ReExpr
watchR = bracketR

type UnopM m a = a -> m a

-- repName :: String -> HermitName
-- repName = mkQualified "Circat.Rep"

monomorphizeE :: ReExpr
monomorphizeE = transform (mono [])

type Trans a b = HermitC -> a -> HermitM b

type Rew a = Trans a a

type Stack = [CoreExpr]                 -- argument stack

-- Monomorphize in the context of a stack of applications (innermost first).
mono :: Stack -> Rew CoreExpr
mono args c = go
 where
   go e = -- pprTrace "mono/go:" (ppr e) $
          applyT (observeR "mono/go") c e >>
          case e of
     Var v | not (isId v) -> mpanic (text "not a value variable:" <+> ppr v)
     Var _ -> inlineNonPrim args `rewOr` bail
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
         letSubstR' = {- watchR "letSubstR" -} letSubstR

     -- TODO: batch up these eliminations and substitutions. Or have GHC do them at the end.
     -- TODO: Is there a cheaper way to check whether v occurs freely in body
     -- without having to collect all of the free variables in a set?

     Let (Rec _) _ -> bail -- spanic "recursive let"

     Case scrut w ty alts ->
       (  watchR "pruneCaseR"     pruneCaseR
       <+ watchR "caseFloatCaseR" caseFloatCaseR
       -- <+ watchR "caseReduceR" (caseReduceR False) . (id <+ arr (onScrutineeR altIdOf)) . 
       <+ watchR "caseReduceR" (caseReduceR False)
       ) `rewOr`
         (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)

     -- TODO: Watch duplication. Only push args inside if fewer than two
     -- alternatives or if they're all trivial. We could let-bind the args.

     -- TODO: altId & caseReduceR: (id <+ arr (onScrut altId)) . caseReduceR

--      Case scrut w ty alts ->
--        (watchR "removeCase" removeCase) `rewOr`
--          (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)

--      Case scrut w ty alts ->
--        caseReduceUnfoldR' `rewOr`
--        standardizeCase    `rewOr`
--          (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)
--       where
--         caseReduceUnfoldR' =
--           {-watchR "caseReduceUnfoldR"-} (caseReduceUnfoldR False)

--      Case scrut w ty alts ->
--        caseReduceUnfoldR' `rewOr`
--          case alts of
--            (_:_:_) -> watchR "pruneCaseR" pruneCaseR `rewOr` bail
--            _       -> (Case <$> mono0 scrut <*> pure w <*> pure ty
--                             <*> mapM (onAltRhsM go) alts)
--       where
--         caseReduceUnfoldR' =
--           {-watchR "caseReduceUnfoldR"-} (caseReduceUnfoldR False)


--      Case scrut w ty alts@[_] ->
--        (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)
--      Case {} -> (watchR "pruneCaseR" pruneCaseR) `rewOr` bail

--      Case scrut _ _ _  ->
--        (guardMsg (isMono scrut) "Poly" >> caseReduceUnfoldR') `rewOr` bail
--           -- (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)
--       where
--         caseReduceUnfoldR' =
--           {-watchR "caseReduceUnfoldR"-} (caseReduceUnfoldR False)

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
      infixr 4 `rewOr`
      rewOr :: ReExpr -> HermitM CoreExpr -> HermitM CoreExpr
      rew `rewOr` ma = catchMaybe (applyT rew c e) >>= maybe ma go
      bail = mkCoreApps e <$> mapM mono0 args

-- TODO: Prune case expressions to stop recursion.

isMono :: CoreExpr -> Bool
isMono = isMonoTy . exprType'

-- Is a given type a monotype? Assumes that any type variables are bound to monotypes.
isMonoTy :: Type -> Bool
isMonoTy (coreView -> Just ty) = isMonoTy ty
isMonoTy (TyVarTy _)           = False
isMonoTy (AppTy u v)           = isMonoTy u && isMonoTy v
isMonoTy (TyConApp _ tys)      = all isMonoTy tys
isMonoTy (FunTy u v)           = isMonoTy u && isMonoTy v
isMonoTy (ForAllTy {})         = False
isMonoTy (LitTy _)             = True

-- mono/go/case bailing. case scrutinee has poly type RTree N1 Int

-- Inline variable if (a) it's not a primitive, and (b) the arguments suffice to
-- make the application monomorphic. The implied applications (to args) do not
-- happen here.
inlineNonPrim :: [CoreExpr] -> ReExpr
inlineNonPrim args = watchR "inlineNonPrim" $
  do Var v <- id
     guardMsg (not (isPrim v)) "inlineNonPrim: primitive"
     guardMsg (all isMonoTy [ty | Type ty <- args]) "Non-monotype arguments"  -- [1,2]
     -- pprTrace "inlineNonPrim" (ppr (varType v) $+$ sep (ppr <$> args)) (return ())
     inlineR
   
-- [1] Should I also check that the whole application is monomorphic?
-- 
-- [2] Maybe re-implement more efficiently, without building the application.
-- Note that mkCoreApps type-checks as it goes.

isPrim :: Id -> Bool
isPrim v = fqVarName v `S.member` primNames

-- Heading here:
-- 
-- Translate function names to cat class and prim
-- primNames :: M.Map String (String,String)

-- See current stdMeths in Reify for list of methods, classes, etc.

repMethNames :: S.Set String
repMethNames = S.fromList (("Circat.Rep." ++) <$> ["abst","repr"])

primNames :: S.Set String
primNames = repMethNames `S.union`
  S.fromList
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

#if 0
-- Constructor applied to normalized arguments, with hoisted bindings.
data CtorApp = CtorApp DataCon Stack

-- Transform to constructor-application form, plus outer bindings ready for
-- 'mkCoreLets'. If not already in this form, consider "abst (repr scrut)",
-- i.e., "let v = repr scrut' in abst v", where abst v is monomorphic. Normalize
-- "abst v" to abstv'. The "let v = repr scrut'" gets floated above the case,
-- treating repr as in normal form, leaving the equivalent of "let v = repr
-- scrut' in case abstv' of ...". If it helps, add a continuation argument to
-- apply to the result of case reduction.

toCtorApp :: Trans CoreExpr ([CoreBind],CtorApp)
toCtorApp c = go (10 :: Int) -- number of tries
 where
   go 0 _ = fail "toCtorApp: too many tries"
   go _ (collectArgs -> (Var (isDataConWorkId_maybe -> Just dcon),args)) =
     return $ ([],CtorApp dcon args)
   go n scrut =
     do (abst,repr) <- applyT mkAbstRepr c ty
        v <- newIdH "w" ty
        abstv' <- mono [] c (App abst (Var v))
        first (NonRec v (App repr scrut) :) <$> go (n-1) abstv'
    where
      ty = exprType scrut

mkAbstRepr :: TransformH Type (CoreExpr,CoreExpr)
mkAbstRepr = do f <- hasRepMethodF
                liftA2 (,) (f "abst") (f "repr")

removeCase :: ReExpr
removeCase =
  prefixFailMsg "removeCase failed: " $
  withPatFailMsg (wrongExprForm "Case e v t alts") $
  do Case scrut w ty alts <- id
     (binds, CtorApp con conArgs) <- transform toCtorApp $* scrut
     e' <- watchR "caseReduceDataconR" (caseReduceDataconR False)
             $* (Case (mkCoreConApps con conArgs) w ty alts)
     return $
       mkCoreLets binds e'

#endif

pruneCaseR :: ReExpr
pruneCaseR = prefixFailMsg "pruneCaseR failed: " $
             withPatFailMsg (wrongExprForm "Case scrut v ty alts") $
  do Case scrut wild ty alts <- id
     let alts' = filter (liveAlt (exprType scrut)) alts
     guardMsg (length alts' < length alts) "No impossible alternatives"
     return (Case scrut wild ty alts')

altIdCaseR :: ReExpr
altIdCaseR = watchR "altIdCaseR" $
             prefixFailMsg "altIdCaseR failed: " $
             withPatFailMsg (wrongExprForm "Case scrut v ty [alt]") $
  do Case _ wild _ [alt] <- id
     onScrutineeR (altIdOf wild alt)

-- A single-alternative identity function based on an existing case alternative,
-- applied to a given scrutinee, and using the given wild var.
altIdOf :: Var -> CoreAlt -> ReExpr
altIdOf wild (alt,vs,_) =
  do scrut <- id
     let fun     = mkAltConExpr alt
         scrutTy = exprType' scrut
     Just tyArgs <- return (tyConAppArgs_maybe scrutTy)
     pprTrace "altIdOf" (ppr fun <+> text "::" <+> ppr (exprType' fun)) (return ())
     return (Case scrut wild scrutTy
               [(alt,vs,mkCoreApps fun (map Type tyArgs ++ map varToCoreExpr vs))])
 where
   mkAltConExpr :: AltCon -> CoreExpr
   mkAltConExpr (DataAlt dc) = Var (dataConWorkId dc)
   mkAltConExpr (LitAlt lit) = Lit lit
   mkAltConExpr DEFAULT      = Var wild

-- | Can a given case constructor produce the given type?
liveAlt :: Type -> CoreAlt -> Bool
liveAlt ty (DataAlt dc,_,_) = liveDc ty dc
liveAlt _  _                = True

-- | Can a given case Alt match the given type?
liveDc :: Type -> DataCon -> Bool
liveDc ty dc = isJust (unifyTys ((ty,dcResTy) : coEqns))
 where
   (coEqns,dcResTy) = extractCoEqns (dataConRepType dc)

-- Extract equations from coercion variables bound in a type, along with the
-- final result type.
extractCoEqns :: Type -> ([(Type,Type)], Type)
extractCoEqns = go []
 where
   go acc (ForAllTy _ t)                   = go acc t
   go acc (FunTy u t) | Just eq <- coEqn u = go (eq : acc) t
                      | otherwise          = go acc t
   go acc t                                = (acc,t)

-- Bummed from GHC's coVarKind
coEqn :: Type -> Maybe (Type,Type)
coEqn ty
 | Just (tc, [_kind,ty1,ty2]) <- splitTyConApp_maybe ty
 , tc `hasKey` eqPrimTyConKey || tc `hasKey` eqReprPrimTyConKey
 = Just (ty1,ty2)
 | otherwise = Nothing

unifyTys :: [(Type,Type)] -> Maybe TvSubst
unifyTys = uncurry (tcUnifyTys (const BindMe)) . unzip


{--------------------------------------------------------------------
    Commands for interactive use
--------------------------------------------------------------------}

externals :: [External]
externals =
  [ externC' "prune-case" pruneCaseR
  , externC' "alt-id-case" altIdCaseR
  ]


