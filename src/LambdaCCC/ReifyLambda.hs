{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ReifyLambda
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Reify a Core expression into GADT
----------------------------------------------------------------------

module LambdaCCC.ReifyLambda where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Control.Monad ((<=<),liftM2)
import Control.Arrow (arr,(>>>),(&&&))
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf (printf)

import qualified Language.Haskell.TH as TH (Name,mkName)
import qualified Language.Haskell.TH.Syntax as TH (showName)

-- GHC API
import GhcPlugins hiding (mkStringExpr)
import TypeRep (Type(..))
import PrelNames (unitTyConKey,boolTyConKey,intTyConKey)

import Language.HERMIT.Context
  (ReadBindings,HermitBindingSite(LAM),hermitBindings)
import Language.HERMIT.Core (Crumb(..))
import Language.HERMIT.External
import Language.HERMIT.GHC (uqName,var2String)
import Language.HERMIT.Kure hiding (apply)
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.Primitive.GHC (rule)
import Language.HERMIT.Primitive.Local (letIntro,letFloatArg,letFloatLetTop)
import Language.HERMIT.Primitive.Navigation (rhsOf,parentOf,bindingGroupOf)
import Language.HERMIT.Primitive.Unfold (unfoldNameR,cleanupUnfoldR)

import qualified Language.HERMIT.Kure as Kure

import LambdaCCC.Misc (Unop,Binop)
import qualified LambdaCCC.Ty     as T
import qualified LambdaCCC.Lambda as E
import LambdaCCC.MkStringExpr (mkStringExpr)

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d type arguments but got %d."
                     (var2String f) arity ntys
  | otherwise = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)
 where
   arity = tyArity f
   ntys  = length ts

tyArity :: Id -> Int
tyArity = length . fst . splitForAllTys . varType

listToPair :: [a] -> Maybe (a,a)
listToPair [a,b] = Just (a,b)
listToPair _     = Nothing

unTuple :: CoreExpr -> Maybe [CoreExpr]
unTuple expr@(App {})
  | (Var f, dropWhile isTypeArg -> valArgs) <- collectArgs expr
  , Just dc <- isDataConWorkId_maybe f
  , isTupleTyCon (dataConTyCon dc) && (valArgs `lengthIs` idArity f)
  = Just valArgs
unTuple _ = Nothing

-- tuple :: [CoreExpr] -> CoreExpr
-- tuple es = ... ?
--
-- pair :: Binop CoreExpr
-- pair a b = tuple [a,b]

unPair :: CoreExpr -> Maybe (CoreExpr,CoreExpr)
unPair = listToPair <=< unTuple

-- TODO: Maybe remove unPair and unPairTy, since it's just as easy to use
-- unTuple and pattern-match against Just [a,b].

{-
-- Unsafe way to ppr in pure code.
tr :: Outputable a => a -> a
tr x = trace ("tr: " ++ pretty x) x

pretty :: Outputable a => a -> String
pretty = showPpr tracingDynFlags

pretties :: Outputable a => [a] -> String
pretties = intercalate "," . map pretty
-}

-- | Variant of GHC's 'collectArgs'
collectTypeArgs :: CoreExpr -> (CoreExpr, [Type])
collectTypeArgs expr = go expr []
  where
    go (App f (Type t)) ts = go f (t:ts)
    go e 	        ts = (e, ts)

unTupleTy :: Type -> Maybe [Type]
unTupleTy (TyConApp tc tys)
  | isTupleTyCon tc && tyConArity tc == length tys = Just tys
unTupleTy _ = Nothing

-- unPairTy :: Type -> Maybe (Type,Type)
-- unPairTy = listToPair <=< unTupleTy

{--------------------------------------------------------------------
    KURE utilities
--------------------------------------------------------------------}

-- | Transformation while focused on a path
pathIn :: (Eq crumb, ReadPath c crumb, MonadCatch m, Walker c b) =>
          Translate c m b (Path crumb) -> Unop (Rewrite c m b)
pathIn mkP f = mkP >>= flip pathR f

-- | Transformation while focused on a snoc path
snocPathIn :: ( Eq crumb, Functor m, ReadPath c crumb
              , MonadCatch m, Walker c b ) =>
              Translate c m b (SnocPath crumb) -> Unop (Rewrite c m b)
snocPathIn mkP = pathIn (snocPathToPath <$> mkP)

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

unfoldRules :: [String] -> RewriteH CoreExpr
unfoldRules nms = catchesM (rule <$> nms) >>> cleanupUnfoldR

-- | Translate a pair expression.
pairT :: (Monad m, ExtendPath c Crumb) =>
         Translate c m CoreExpr a -> Translate c m CoreExpr b
      -> (Type -> Type -> a -> b -> z) -> Translate c m CoreExpr z
pairT tu tv f = translate $ \ c ->
  \ case (unPair -> Just (u,v)) ->
           liftM2 (f (exprType u) (exprType v))
                  (Kure.apply tu (c @@ App_Fun @@ App_Arg) u)
                  (Kure.apply tv (c            @@ App_Arg) v)
         _         -> fail "not a pair node."

-- | Translate an n-ary type-instantiation of a variable, where n >= 0.
appVTysT :: (ExtendPath c Crumb, Monad m) =>
            Translate c m Var a -> (a -> [Type] -> b) -> Translate c m CoreExpr b
appVTysT tv h = translate $ \c ->
  \ case (collectTypeArgs -> (Var v, ts)) ->
           liftM2 h (Kure.apply tv (applyN (length ts) (@@ App_Fun) c) v)
                    (return ts)
         _ -> fail "not an application of a variable to types."
  where
    applyN :: Int -> (a -> a) -> a -> a
    applyN n f a = foldr ($) a (replicate n f)


defR :: RewriteH Id -> RewriteH CoreExpr -> RewriteH Core
defR rewI rewE = prunetdR (  promoteDefR (defAllR rewI rewE)
                          <+ promoteBindR (nonRecAllR rewI rewE) )

rhsR :: RewriteH CoreExpr -> RewriteH Core
rhsR = defR idR

unfoldNames :: [TH.Name] -> RewriteH CoreExpr
unfoldNames nms = catchesM (unfoldNameR <$> nms) -- >>> cleanupUnfoldR

-- Just the lambda-bound variables in a HERMIT context
lambdaVars :: ReadBindings c => c -> S.Set Var
lambdaVars = M.keysSet .  M.filter (isLam . snd) . hermitBindings
 where
   isLam LAM = True
   isLam _   = False

-- TODO: Maybe return a predicate instead of a set. More abstract, and allows
-- for efficient construction. Here, we'd probably want to use the underlying
-- map to implement the returned predicate.

-- | Extract just the lambda-bound variables in a HERMIT context
lambdaVarsT :: (ReadBindings c, Applicative m) => Translate c m a (S.Set Var)
lambdaVarsT = contextonlyT (pure . lambdaVars)

type InCoreTC t = Injection t CoreTC

observing :: Bool
observing = False

observeR' :: InCoreTC t => String -> RewriteH t
observeR' | observing = observeR
          | otherwise = const idR

tries :: (InCoreTC a, InCoreTC t) => [(String,TranslateH a t)] -> TranslateH a t
tries = foldr (<+) (observeR' "Other" >>> fail "unhandled")
      . map (uncurry try)

try :: InCoreTC t => String -> Unop (TranslateH a t)
try label = (>>> observeR' label)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

type ReType = TranslateH Type CoreExpr

-- | Translate a Core type t into a core expression that evaluates to a Ty t.
reifyType :: ReType
reifyType =
  do funTId  <- findIdT '(T.:=>)
     pairTId <- findIdT '(T.:*)
     unitTId <- findIdT 'T.UnitT
     intTID  <- findIdT 'T.IntT
     boolTID <- findIdT 'T.BoolT
     let simples :: M.Map Unique Id
         simples = M.fromList [(unitTyConKey,unitTId),(boolTyConKey,boolTID),(intTyConKey,intTID)]
         simpleTId :: TyCon -> Maybe Id
         simpleTId  = flip M.lookup simples . getUnique
         rew :: ReType
         rew = tries [ ("TSimple",rTSimple),("TPair",rTPair), ("TFun",rTFun) ]
         rTSimple, rTPair, rTFun :: ReType
         rTSimple = do TyConApp (simpleTId -> Just tid) [] <- idR
                       return (apps tid [] [])
         rTPair = do Just [_,_] <- unTupleTy <$> idR
                     tyConAppT (pure ()) (const rew) $ \ () [a',b'] ->
                       tyOp2 pairTId a' b'
         rTFun = funTyT rew rew $ tyOp2 funTId
         tyOp2 :: Id -> Binop CoreExpr
         tyOp2 tid a' b' = apps tid [tyTy a',tyTy b'] [a',b']
     rew

-- tyConAppT :: (ExtendPath c Crumb, Monad m) => 
--              Translate c m TyCon a1 -> (Int -> Translate c m KindOrType a2) 
--           -> (a1 -> [a2] -> b) -> Translate c m Type b

-- The type parameter a of an expression of type Ty a.
tyTy :: CoreExpr -> Type
tyTy = dropTyApp1 ''T.Ty . exprType

-- For a given tycon, drop it from a unary type application. Error otherwise.
-- WARNING: I'm not yet checking for a tycon match. TODO: check.
dropTyApp1 :: TH.Name -> Type -> Type
dropTyApp1 _ (TyConApp _ [t]) = t
dropTyApp1 _ _ = error "dropTyApp1: not a unary TyConApp"

type ReExpr = RewriteH CoreExpr

reifyExpr :: ReExpr
reifyExpr =
  do varId   <- findIdT 'E.var
     appId   <- findIdT '(E.:^)
     lamvId  <- findIdT 'E.lamv
     evalId  <- findIdT 'E.evalE
     reifyId <- findIdT 'E.reifyE
     let rew :: ReExpr
         rew = tries [ ("Var",rVar)
                     , ("Reify", rReify)
                     , ("App",rApp)
                     , ("LamT",rLamT), ("Lam",rLam)
                     ]
         rVar, rApp, rLamT, rLam :: ReExpr
         rVar  = do bvars <- lambdaVarsT
                    varT $
                      do v <- idR
                         if S.member v bvars then
                           do (name,ty) <- mkVarName
                              return $ apps varId [ty] [name]
                          else
                           fail "rVar: not a lambda-bound variable"
                            -- return $ apps reifyId [varType v] [Var v]
         -- Reify (non-lambda) variables and their polymorphic instantiations.
         rReify = do e@(collectTypeArgs -> (Var _, _)) <- idR
                     return $ apps reifyId [exprType e] [e]
         rApp  = do App (exprType -> funTy) _ <- idR
                    appT  rew rew $ arr $ \ u' v' ->
                      let (a,b) = splitFunTy funTy in
                        apps appId [b,a] [u', v'] -- note b,a
         rLamT = do Lam (isTyVar -> True) _ <- idR
                    lamT idR rew (arr Lam)
         rLam  = do Lam _ (exprType -> bodyTy) <- idR
                    lamT mkVarName rew $ arr $ \ (name,ty) e' ->
                      apps lamvId [ty, bodyTy] [name,e']
         -- TODO: Literals
     do ty <- arr exprType
        let mkEval e' = apps evalId [ty] [e']
        mkEval <$> rew

mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

reifyRules :: RewriteH Core
reifyRules = tryR $ anybuR $ promoteExprR $ unfoldRules $ map ("reify/" ++)
               ["not","(&&)","(||)","xor","(+)","fst","snd","pair"]

-- TODO: Is there a way not to redundantly specify this rule list?

reifyDef :: RewriteH Core
reifyDef = rhsR reifyExpr

reifyNamed :: TH.Name -> RewriteH Core
reifyNamed nm = snocPathIn (rhsOf nm)
                  (    promoteExprR reifyExpr
                  >>> reifyRules
                  >>> pathR [App_Arg] (promoteExprR (letIntro nm'))
                  >>> promoteExprR letFloatArg )
            >>> snocPathIn (parentOf (bindingGroupOf nm))
                  (promoteProgR letFloatLetTop)
 where
   nm' = TH.mkName (TH.showName nm ++ "_reified")

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-expr"
        (promoteExprR reifyExpr :: RewriteH Core)
        ["Reify a Core expression into a GADT construction"]
    , external "reify-rules"
        (reifyRules :: RewriteH Core)
        ["convert some non-local vars to consts"]
    , external "reify-def"
        (reifyDef :: RewriteH Core)
        ["reify for definitions"]
    , external "reify-expr-cleanup"
        (promoteExprR reifyExpr >>> reifyRules :: RewriteH Core)
        ["reify-core and cleanup for expressions"]
    , external "reify-def-cleanup"
        (reifyDef >>> reifyRules :: RewriteH Core)
        ["reify-core and cleanup for definitions"]
    , external "reify-named"
        (reifyNamed :: TH.Name -> RewriteH Core)
        ["reify via name"]
    ]
