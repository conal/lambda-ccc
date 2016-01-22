{-# LANGUAGE CPP, TupleSections, ViewPatterns, ConstraintKinds #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module LambdaCCC.Monomorphize where

-- TODO: explicit exports

import Control.Arrow (first)
import Control.Monad.IO.Class (MonadIO)
import Data.Char (isSpace)

-- import GhcPlugins  -- or refine imports
-- import Type (Type(TyConApp))
-- -- import qualified Type as Type
-- import Encoding (zEncodeString)

import Language.KURE
import HERMIT.GHC
import HERMIT.Dictionary
import HERMIT.Name
import HERMIT.Monad

import HERMIT.Extras (moduledName,normaliseTypeM,apps)

-- TODO: Tighten imports


-- Monomorphism-normalized expressions
newtype Norm = Norm { unNorm :: CoreExpr }

-- Constructor applied to normalized arguments, with hoisted bindings.
data CtorApp = CtorApp Id [Norm]

-- TODO: Clarify bindings order. Note:
--
-- -- | Bind a list of binding groups over an expression. The leftmost binding
-- -- group becomes the outermost group in the resulting expression
-- mkCoreLets :: [CoreBind] -> CoreExpr -> CoreExpr
-- mkCoreLets binds body = foldr mkCoreLet body binds

type MonadNuff m = ( MonadIO m, MonadCatch m, MonadUnique m, MonadThings m
                   , HasDynFlags m, HasHermitMEnv m, LiftCoreM m )

toCtorApp :: MonadNuff m => Subst -> Norm -> m ([(Var,CoreExpr)],CtorApp)
toCtorApp sub = go (10 :: Int) -- number of tries
 where
   go 0 _ = fail "toCtorApp: too many tries"
   go _ (Norm (collectArgs -> (Var v,args))) | isDataConName (varName v) =
     return $ ([],CtorApp v (Norm <$> args))
   go n (Norm scrut) =
     do (abst,repr) <- mkAbstRepr (substTy sub ty)  -- substTy necessary?
        v <- newIdH "w" ty
        abstv' <- mono sub [] (App abst (Var v))
        first ((v, App repr scrut) :) <$> go (n-1) abstv'
    where
      ty = exprType scrut

mono :: Monad m => Subst -> [Norm] -> CoreExpr -> m Norm
mono _ _ e@(Lit _) = return (Norm e)
mono sub args e@(Var v) =
 case lookupIdSubst (text "mono") sub v of
   Var v' | v == v' -> return (Norm e)
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

-- mono sub args (Case scrut w ty alts) = ...

mono _ _ _ = error "mono: unhandled case"

-- Warning: I don't type-distinguish between non-normalized and normalized
-- CoreBind.
monoBinds :: Monad m => Subst -> CoreBind -> m CoreBind
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

buildDictionaryT :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadCatch m, MonadIO m, MonadUnique m)
                 => Transform c m Type CoreExpr
buildDictionaryT = prefixFailMsg "buildDictionaryT failed: " $ contextfreeT $ buildDictionaryM

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

#endif
