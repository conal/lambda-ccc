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
import Data.Maybe (catMaybes,isJust)

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
  (pattern FunCo, fqVarName, exprType', exprTypeT, ReExpr
  , ($*), externC', onScrutineeR, bashExtendedWithE, newIdT
  )

-- import Monomorph.Stuff (pruneCaseR,standardizeCase,standardizeCon,hasRepMethodF)
import Monomorph.Stuff (hasRepMethodF)

type Unop a = a -> a

watchR, nowatchR :: String -> Unop ReExpr
watchR = bracketR
nowatchR = const id

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
     App fun arg ->
       abstReprCon `rewOr`    -- try at Var also?
         mono (arg : args) c fun
     Let (NonRec v rhs) body
       | v `notElemVarSet` freeVarsExpr body ->
           -- pprTrace "go" (text "let-elim" <+> ppr v) $
           go body
       | otherwise ->
          (guardMsg (exprIsTrivial rhs) "non-trivial" >> letSubstR')
           `rewOr` (mkCoreLet <$> (NonRec v <$> mono0 rhs) <*> go body)
       where
         letSubstR' = {- watchR "letSubstR" -} letSubstR

     -- TODO: batch up these eliminations and substitutions. Or have GHC do them at the end.
     -- TODO: Is there a cheaper way to check whether v occurs freely in body
     -- without having to collect all of the free variables in a set?

     -- No. We must at least substitute type bindings, so we can recognize monotypes.

     Let (Rec _) _ -> bail -- spanic "recursive let"

     Case scrut w ty alts ->
       (  nowatchR "caseReduceR False" (caseReduceR False)
       <+ nowatchR "letFloatCaseR" letFloatCaseR
       <+ nowatchR "caseFloatCaseR" caseFloatCaseR
       <+ nowatchR "abstReprCase" abstReprCase
       ) `rewOr`
         (Case <$> mono0 scrut <*> pure w <*> pure ty <*> mapM (onAltRhsM go) alts)

     -- TODO: Watch duplication in the fall-back here. Only push args inside if
     -- fewer than two alternatives or if they're all trivial. We could let-bind
     -- the args.

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
inlineNonPrim args = -- watchR "inlineNonPrim" $
  do Var v <- id
     guardMsg (not (isPrim v)) "inlineNonPrim: primitive"
     guardMsg (all isMonoTy [ty | Type ty <- args]) "Non-monotype arguments"  -- [1,2]
     -- pprTrace "isRepDict test on type" (ppr (varType v)) (return ())
     guardMsg (not (isRepDict (varType v))) "HasRep dictionary"
     -- pprTrace "inlineNonPrim" (ppr (varType v) $+$ sep (ppr <$> args)) (return ())
     inlineR
 where
   isRepDict :: Type -> Bool
   -- isRepDict ty | pprTrace "isRepDict" (ppr ty) False = error "wat"
   isRepDict (coreView -> Just ty) = isRepDict ty
   isRepDict (TyConApp tc _args)   =
     -- pprTrace "isRepDict TyConApp tc name" (text (qualifiedName (tyConName tc))) $
     qualifiedName (tyConName tc) == "Circat.Rep.HasRep"
   isRepDict (ForAllTy _ ty)       = isRepDict ty
   isRepDict (FunTy _dom ran)      = isRepDict ran
   isRepDict _                     = False

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

primNames :: S.Set String
primNames = S.fromList $
     repMeths
  ++ [ "GHC.Num.$fNum"++ty++"_$c"++meth
     | (tys,meths) <- primMeths , ty <- tys, meth <- meths ]
  ++ primFuns
 where
   repMeths  = ("Circat.Rep." ++) <$> ["abst","repr"]
   primMeths = [( ["Int","Double"]
                , ["+","-","*","negate","abs","signum","fromInteger"])]
     -- TODO: more primitives, including boolean
   primFuns =
     [ "GHC.Classes.not", "GHC.Classes.&&", "GHC.Classes.||", "Circat.Misc.xor"
     , "GHC.Tuple.(,)", "GHC.Tuple.fst", "GHC.Tuple.snd"
     , "Data.Either.Left", "Data.Either.Right"
     ]

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

-- *   Replace with `let { v1 = e1 ; ... ; vn = en } in `C v1 ... vn`
-- *   Rewrite the heck out of `repr (C v1 ... vn)`, including inlining everything.
-- *   Wrap with `abst`.

abstReprCon :: ReExpr
abstReprCon = -- watchR "abstReprCon" $
              -- observeR "abstReprCon" >>>
  do (dc,tyArgs,span isTyCoArg -> (tycos,eArgs)) <- callDataConT
     -- pprTrace "abstReprCon un-DC" (ppr (dc,tyArgs,tycos,eArgs)) (return ())
     vs <- mapT (newIdT "v" . exprTypeT) $* eArgs      -- TODO: better/distinct names
     ty <- exprTypeT
     (abst,repr) <- mkAbstRepr $* ty
     repre' <- {- watchR "clobber repre" -} clobber $*
                 App repr (mkCoreConApps dc (map Type tyArgs ++ tycos ++ map Var vs))
     return (mkCoreLets (zipWith NonRec vs eArgs) (mkCoreApp abst repre'))

-- mkCoreConApps :: DataCon -> [CoreExpr] -> CoreExpr

-- Without the let-binding.

abstReprCon' :: ReExpr
abstReprCon' =
  do _ <- callDataConT
     e <- id
     let ty = exprType' e
     (abst,repr) <- mkAbstRepr $* ty
     repre' <- watchR "clobber repre" clobber $* App repr e
     return (mkCoreApp abst repre')

-- callDataConT :: MonadCatch m => Transform c m CoreExpr (DataCon, [Type], [CoreExpr])

abstReprCase :: ReExpr
abstReprCase = onScrutineeR abstReprScrutinee

-- Prepare a scrutinee
abstReprScrutinee :: ReExpr
abstReprScrutinee =
  do scrut <- id
     let ty = exprType' scrut
     -- pprTrace "abstReprScrutinee:" (ppr scrut <+> text "::" <+> ppr ty) (return ())
     (abst,repr) <- mkAbstRepr $* ty
     -- pprTrace "toCtorApp (abst,repr):" (ppr (mkCoreTup [abst,repr])) (return ())
     let reprScrut = mkCoreApp repr scrut
     v <- newIdT "w" $* exprType' reprScrut
     -- abstv' <- mono [] c (App abst (Var v))
     abstv' <- nowatchR "clobber abstv" clobber $* App abst (Var v)
     -- repr scrut gets monomorphized later
     return (Let (NonRec v reprScrut) abstv')

clobber :: ReExpr
clobber = bashExtendedWithE [inlineR]

mkAbstRepr :: TransformH Type (CoreExpr,CoreExpr)
mkAbstRepr = do f <- hasRepMethodF
                liftA2 (,) (f "abst") (f "repr")

#if 0

pruneCaseR :: ReExpr

pruneCaseR = prefixFailMsg "pruneCaseR failed: " $
             withPatFailMsg (wrongExprForm "Case scrut v ty alts") $
  do Case scrut wild ty alts <- id
     let alts' = catMaybes (liveAlt (exprType scrut) <$> alts)
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
liveAlt :: Type -> CoreAlt -> Maybe CoreAlt
liveAlt ty al@(DataAlt dc,_,_)
  | Just _sub <- liveDc ty dc = Just al
  | otherwise                 = Nothing
liveAlt _  al                 = Just al

-- tvSubstToSubst :: TvSubst -> Subst
-- tvSubstToSubst (TvSubst in_scope tenv)  Subst in_scope _ tenv _

-- TODO: Apply substitution in the body of the returned CoreAlt. I may have to
-- write my own pattern matcher that yields coercions for type variables, to
-- include in the Subst. See the notes on the Subst data type in GHC's
-- CoreSubst module.

-- | Can a given case Alt match the given type?
liveDc :: Type -> DataCon -> Maybe TvSubst
liveDc ty dc = unifyTys ((ty,dcResTy) : coEqns)
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

#endif

{--------------------------------------------------------------------
    Commands for interactive use
--------------------------------------------------------------------}

externals :: [External]
externals =
  [
    externC' "abst-repr-case" abstReprCase
  , externC' "abst-repr-con" abstReprCon
  ]

--   , externC' "prune-case" pruneCaseR
--   , externC' "alt-id-case" altIdCaseR

