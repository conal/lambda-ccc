{-# LANGUAGE CPP, TupleSections, ViewPatterns, ConstraintKinds #-}

-- Try removing these extensions later 
{-# LANGUAGE ScopedTypeVariables, MultiWayIf, FlexibleContexts #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

module LambdaCCC.Monomorphize (monomorphize,MonadNuff) where

import Control.Arrow (first)
import Control.Monad.IO.Class (MonadIO)
import Data.Char (isSpace)

-- import GhcPlugins  -- or refine imports
-- import Type (Type(TyConApp))
-- -- import qualified Type as Type
-- import Encoding (zEncodeString)

import Language.KURE
import HERMIT.Core
import HERMIT.Dictionary
import HERMIT.GHC
import HERMIT.Monad
import HERMIT.Name

import HERMIT.Extras (moduledName,normaliseTypeM,apps)

-- TODO: Tighten imports


-- Monomorphism-normalized expressions
newtype Norm = Norm { unNorm :: CoreExpr }

-- Constructor applied to normalized arguments, with hoisted bindings.
data CtorApp = CtorApp DataCon [Norm]

-- TODO: Clarify bindings order. Note:
--
-- -- | Bind a list of binding groups over an expression. The leftmost binding
-- -- group becomes the outermost group in the resulting expression
-- mkCoreLets :: [CoreBind] -> CoreExpr -> CoreExpr
-- mkCoreLets binds body = foldr mkCoreLet body binds

type MonadNuff m = ( MonadIO m, MonadCatch m, MonadUnique m, MonadThings m
                   , HasDynFlags m, HasHermitMEnv m, LiftCoreM m )

-- Transform to constructor-application form, plus outer bindings ready for
-- 'mkCoreLets'. If not already in this form, consider "abst (repr scrut')",
-- i.e., "let v = repr scrut' in abst v", where abst v is monomorphic. Normalize
-- "abst v" to abstv'. The "let v = repr scrut'" gets floated above the case,
-- treating repr as in normal form, leaving the equivalent of "let v = repr
-- scrut' in case abstv' of ...". If it helps, add a continuation argument to
-- apply to the result of case reduction.

toCtorApp :: MonadNuff m => Subst -> Norm -> m ([CoreBind],CtorApp)
toCtorApp sub = go (10 :: Int) -- number of tries
 where
   go 0 _ = fail "toCtorApp: too many tries"
   go _ (Norm (collectArgs -> (Var (isDataConWorkId_maybe -> Just dcon),args))) =
     return $ ([],CtorApp dcon (Norm <$> args))
   go n (Norm scrut) =
     do (abst,repr) <- mkAbstRepr (substTy sub ty)  -- substTy necessary?
        v <- newIdH "w" ty
        abstv' <- mono sub [] (App abst (Var v))
        first (NonRec v (App repr scrut) :) <$> go (n-1) abstv'
    where
      ty = exprType scrut

monomorphize :: MonadNuff m => CoreExpr -> m CoreExpr
monomorphize = fmap unNorm . mono emptySubst []

mono :: MonadNuff m => Subst -> [Norm] -> CoreExpr -> m Norm
mono _ _ e@(Lit _) = return (Norm e)
mono sub args e@(Var v) =
 case lookupIdSubst (text "mono") sub v of
   Var v' | v == v' ->  -- not found, so try unfolding
     maybe (return (Norm e)) (mono sub args) (getUnfolding v)
   e'               -> mono sub args e'  -- revisit. which sub to use?
mono sub args (App fun arg) =
  do arg' <- mono sub args arg
     mono sub (arg':args) fun
mono sub (Norm (Type ty):args) (Lam v body) =
  if isTyVar v then
    mono (extendTvSubst sub v ty) args body
  else
    fail "mono: Lam/Type confusion"
mono sub args (Let binds body) =
  do binds' <- monoBinds sub binds
     body'  <- mono sub args body
     return (Norm (Let binds' (unNorm body')))
mono sub args (Case scrut w ty alts) =
  do scrut' <- mono sub [] scrut
     (binds, CtorApp con conArgs) <- toCtorApp sub scrut'
     e' <- caseReduceDatacon (Case (mkCoreConApps con (unNorm <$> conArgs)) w ty alts)
     return $
       Norm (mkCoreLets binds (mkCoreApps e' (unNorm <$> args)))
mono _ _ _ = error "mono: unhandled case"

-- Warning: I don't type-distinguish between non-normalized and normalized
-- CoreBind.
monoBinds :: MonadNuff m => Subst -> CoreBind -> m CoreBind
monoBinds sub (NonRec b rhs) =
  (NonRec b . unNorm) <$> mono sub [] rhs
monoBinds sub (Rec bs) = Rec <$> mapM mo bs
 where
   mo (b,e) = (b,) . unNorm <$> mono sub [] e

#if 0

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data Expr b
  = Var   Id
  | Lit   Literal
  | App   (Expr b) (Arg b)
  | Lam   b (Expr b)
  | Let   (Bind b) (Expr b)
  | Case  (Expr b) b Type [Alt b]       -- See #case_invariant#
  | Cast  (Expr b) Coercion
  | Tick  (Tickish Id) (Expr b)
  | Type  Type
  | Coercion Coercion
  deriving (Data, Typeable)

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data Bind b = NonRec b (Expr b)
            | Rec [(b, (Expr b))]
  deriving (Data, Typeable)

#endif

mkAbstRepr :: MonadNuff m => Type -> m (CoreExpr,CoreExpr)
mkAbstRepr ty = 
  do -- The following check avoids an old problem in buildDictionary. Still needed?
     guardMsg (not (isEqPred ty)) "Predicate type"  -- still needed?
     guardMsg (closedType ty) "Type has free variables"
     hasRepTc <- findTC (repName "HasRep")
     tyStr <- showPprM ty
     dict  <- prefixFailMsg ("Couldn't build HasRep dictionary for " ++ tyStr) $
              buildDictionaryM (mkTyConApp hasRepTc [ty])
     repTc <- findTC (repName "Rep")
     (mkEqBox -> eq,ty') <- prefixFailMsg "normaliseTypeT failed: "$
                            normaliseTypeM Nominal (TyConApp repTc [ty])
     let mkMeth meth = apps' (repName meth) [ty] [dict,Type ty',eq]
     repr <- mkMeth "repr"
     abst <- mkMeth "abst"
     return (repr,abst)

closedType :: Type -> Bool
closedType = isEmptyVarSet . tyVarsOfType

{--------------------------------------------------------------------
    Misc adaptations of HEMIT operations dropping context
--------------------------------------------------------------------}

-- Apply a named id to type and value arguments.
apps' :: MonadNuff m => HermitName -> [Type] -> [CoreExpr] -> m CoreExpr
apps' nm ts es = (\ i -> apps i ts es) <$> findVar' nm

-- Like hermit's findId, but no context, and don't include constructors
findVar' :: MonadNuff m => HermitName -> m Id
findVar' nm = do
    nmd <- findInNSModGuts varNS nm
    case nmd of
        NamedId i -> return i
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> fail $ "findId': impossible Named returned: " ++ show other

-- Like hermit's findTyCon but doesn't take a context, and assumes not a bound var

findTC :: (LiftCoreM m, HasHermitMEnv m, MonadIO m, MonadThings m)
       => HermitName -> m TyCon
findTC nm = do
    nmd <- findInNSModGuts tyConClassNS nm
    case nmd of
        NamedTyCon tc -> return tc
        other -> fail $ "findTyCon: impossible Named returned: " ++ show other

repName :: String -> HermitName
repName = moduledName "Circat.Rep"

-- | Get a GHC pretty-printing
showPprM :: (HasDynFlags m, Outputable a, Monad m) => a -> m String
showPprM a = do dynFlags <- getDynFlags
                return (showPpr dynFlags a)

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

-- Refactored from HERMIT. Contribute back

#if 0
buildDictionaryT :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadCatch m, MonadIO m, MonadUnique m)
                 => Transform c m Type CoreExpr
buildDictionaryT = prefixFailMsg "buildDictionaryT failed: " $ contextfreeT $ \ ty -> do
    dflags <- getDynFlags
    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary binder
    guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)
#else

_buildDictionaryT :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadCatch m, MonadIO m, MonadUnique m)
                 => Transform c m Type CoreExpr
_buildDictionaryT = prefixFailMsg "buildDictionaryT failed: " $ contextfreeT $ buildDictionaryM

buildDictionaryM :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadCatch m, MonadIO m, MonadUnique m)
                 => Type -> m CoreExpr
buildDictionaryM ty = do
    dflags <- getDynFlags
    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary binder
    guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)

-- TODO: Test buildDictionary and buildDictionaryM, and then replace definition in hermit.

#endif

#if 0
-- | Case of Known Constructor.
--   Eliminate a case if the scrutinee is a data constructor.
--   If first argument is True, perform substitution in RHS, if False, build let expressions.
caseReduceDataconR :: forall c m. ( ExtendPath c Crumb, ReadPath c Crumb, AddBindings c
                                  , ReadBindings c, MonadCatch m, MonadUnique m )
                   => Bool -> Rewrite c m CoreExpr
caseReduceDataconR subst = prefixFailMsg "Case reduction failed: " $
                           withPatFailMsg (wrongExprForm "Case e v t alts") go
    where
        go :: Rewrite c m CoreExpr
        go = do
            Case e bndr _ alts <- idR
            let in_scope = mkInScopeSet (localFreeVarsExpr e)
            case exprIsConApp_maybe (in_scope, idUnfolding) e of
                Nothing                -> fail "head of scrutinee is not a data constructor."
                Just (dc, univTys, es) -> case findAlt (DataAlt dc) alts of
                    Nothing             -> fail "no matching alternative."
                    Just (dc', vs, rhs) -> -- dc' is either DEFAULT or dc
                        -- NB: It is possible that es contains one or more existentially quantified types.
                        let fvss    = map freeVarsExpr $ map Type univTys ++ es
                            shadows = [ v | (v,n) <- zip vs [1..], any (elemVarSet v) (drop n fvss) ]
                        in if | any (elemVarSet bndr) fvss -> alphaCaseBinderR Nothing >>> go
                              | null shadows               -> do let binds = zip (bndr : vs) (e : es)
                                                                 return $ if subst
                                                                          then foldr (uncurry substCoreExpr) rhs binds
                                                                          else flip mkCoreLets rhs $ map (uncurry NonRec) binds
                              | otherwise                  -> caseOneR (fail "scrutinee") (fail "binder") (fail "type") (\ _ -> acceptR (\ (dc'',_,_) -> dc'' == dc') >>> alphaAltVarsR shadows) >>> go
-- WARNING: The alpha-renaming to avoid variable capture has not been tested.  We need testing infrastructure!
#else

-- | Case of Known Constructor.
--   Eliminate a case if the scrutinee is a data constructor.
--   If first argument is True, perform substitution in RHS, if False, build let expressions.
caseReduceDatacon :: forall m. (MonadCatch m, MonadUnique m)
                  => CoreExpr -> m CoreExpr
caseReduceDatacon (Case scrut bndr _ alts) =
  prefixFailMsg "Case reduction failed: " $
  withPatFailMsg (wrongExprForm "Case scrut v t alts") $
  case exprIsConApp_maybe (in_scope, idUnfolding) scrut of
      Nothing                 -> fail "head of scrutinee is not a data constructor."
      Just (dc, _univTys, es) ->
        case findAlt (DataAlt dc) alts of
          Nothing             -> fail "no matching alternative."
          Just (_dc', vs, rhs) ->
            return $ mkCoreLets (zipWith NonRec (bndr : vs) (scrut : es)) rhs
 where
   in_scope = mkInScopeSet (localFreeVarsExpr scrut)
caseReduceDatacon _ = fail "Not a case"

#endif


#if 0
getUnfoldingsT :: (ReadBindings c, MonadCatch m)
               => InlineConfig
               -> Transform c m Id [(CoreExpr, BindingDepth -> Bool)]
getUnfoldingsT config = transform $ \ c i ->
    case lookupHermitBinding i c of
      Nothing -> do requireAllBinders config
                    let uncaptured = (<= 0) -- i.e. is global
                    -- This check is necessary because idInfo panics on TyVars. Type variables should
                    -- ALWAYS be in the context (so we should never be in this branch), but at least this
                    -- will give a reasonable error message if something goes wrong, instead of a GHC panic.
                    guardMsg (isId i) "type variable is not in Env (this should not happen)."
                    case unfoldingInfo (idInfo i) of
                      CoreUnfolding { uf_tmpl = uft } -> single (uft, uncaptured)
                      dunf@(DFunUnfolding {})         -> single . (,uncaptured) =<< dFunExpr dunf
                      _ -> case idDetails i of
                            ClassOpId cls -> do
                              let selectors = zip [ idName s | s <- classAllSelIds cls] [0..]
                                  msg = getOccString i ++ " is not a method of " ++ getOccString cls ++ "."
                              idx <- maybe (fail msg) return $ lookup (idName i) selectors
                              single (mkDictSelRhs cls idx, uncaptured)
                            _             -> fail "cannot find unfolding in Env or IdInfo."
      Just b -> let depth = hbDepth b
                in case hbSite b of
                          CASEBINDER s alt -> let tys             = tyConAppArgs (idType i)
                                                  altExprDepthM   = single . (, (<= depth+1)) =<< alt2Exp tys alt
                                                  scrutExprDepthM = single (s, (< depth))
                                               in case config of
                                                    CaseBinderOnly Scrutinee   -> scrutExprDepthM
                                                    CaseBinderOnly Alternative -> altExprDepthM
                                                    AllBinders                 -> do
                                                        au <- altExprDepthM <+ return []
                                                        su <- scrutExprDepthM
                                                        return $ au ++ su
#else

-- Simplified form of hermit's getUnfoldingT. Doesn't use any context.
-- I'm also ignoring capturing for now. Revisit.

getUnfolding :: Id -> Maybe CoreExpr
getUnfolding i =
  case unfoldingInfo (idInfo i) of
    CoreUnfolding { uf_tmpl = uft } -> return uft
    dunf@(DFunUnfolding {})         ->
      return $ mkCoreLams (df_bndrs dunf) $ mkCoreConApps (df_con dunf) (df_args dunf)
    _ -> case idDetails i of
          ClassOpId cls ->
              mkDictSelRhs cls <$> lookup (idName i) (zip [ idName s | s <- classAllSelIds cls] [0..])
          _             -> fail "cannot find unfolding in Env or IdInfo."  -- though Maybe

#endif
