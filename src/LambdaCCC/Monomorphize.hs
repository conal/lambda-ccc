{-# LANGUAGE CPP, TupleSections, ViewPatterns #-}
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

module LambdaCCC.Monomorphize where

-- TODO: explicit exports

import Control.Arrow (first)

import GhcPlugins  -- or refine imports
-- import qualified Type as Type

import HERMIT.Name (newIdH)

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

toCtorApp :: Subst -> Norm -> CoreM ([(Var,CoreExpr)],CtorApp)
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

mono :: Subst -> [Norm] -> CoreExpr -> CoreM Norm
mono _ _ e@(Lit _) = pure (Norm e)
mono sub args e@(Var v) =
 case lookupIdSubst (text "mono") sub v of
   Var v' | v == v' -> pure (Norm e)
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
monoBinds :: Subst -> CoreBind -> CoreM CoreBind
monoBinds sub (NonRec b rhs) =
  (NonRec b . unNorm) <$> mono sub [] rhs
monoBinds sub (Rec bs) = Rec <$> mapM mo bs
 where
   mo :: (Id,CoreExpr) -> CoreM (Id,CoreExpr)
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

mkAbstRepr :: Type -> CoreM (CoreExpr,CoreExpr)
mkAbstRepr = error "mkAbstRepr not yet implemented"

-- mkAbstRepr ty = 
--   do -- The following check avoids an old problem in buildDictionary. Still needed?
--      -- guardMsg (not (isEqPred ty)) "Predicate type"  -- still needed?
--      -- guardMsg (closedType ty) "Type has free variables"
--      hasRepTc <- findTyConT (repName "HasRep")
--      tyStr <- showPprT $* ty
--      dict  <- prefixFailMsg ("Couldn't build HasRep dictionary for " ++ tyStr) $
--               buildDictionaryT $* TyConApp hasRepTc [ty]
--      repTc <- findTyConT (repName "Rep")
--      (mkEqBox -> eq,ty') <- prefixFailMsg "normaliseTypeT failed: "$
--                             normaliseTypeT Nominal $* TyConApp repTc [ty]
--      return $ \ meth -> prefixFailMsg "apps' failed: " $
--                         apps' (repName meth) [ty] [dict,Type ty',eq]
