{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module LambdaCCC.ReifyLambda
  ( plugin
  ) where

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
-- import Control.Monad ((<=<),liftM2)
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
  (ReadBindings,AddBindings,HermitBindingSite(..),hermitBindings)
import Language.HERMIT.Core (Crumb(..))
import Language.HERMIT.External
import Language.HERMIT.GHC (uqName,var2String)
import Language.HERMIT.Primitive.Inline (inlineName)
import Language.HERMIT.Kure hiding (apply)
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.AlphaConversion (unshadow)
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.Primitive.GHC (rule,rules,coreExprFreeIds)
import Language.HERMIT.Primitive.Local (letIntro,letFloatArg,letFloatLetTop)
import Language.HERMIT.Primitive.Navigation (rhsOf,parentOf,bindingGroupOf)
import Language.HERMIT.Primitive.New (simplifyR)
import Language.HERMIT.Primitive.Unfold (cleanupUnfoldR) -- unfoldNameR,

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

{-
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

unPair :: CoreExpr -> Maybe (CoreExpr,CoreExpr)
unPair = listToPair <=< unTuple
-}

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

-- For a given tycon, drop it from a unary type application. Error otherwise.
-- WARNING: I'm not yet checking for a tycon match. TODO: check.
dropTyApp1 :: TH.Name -> Type -> Type
dropTyApp1 _ (TyConApp _ [t]) = t
dropTyApp1 _ _ = error "dropTyApp1: not a unary TyConApp"

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

apply' :: Translate c m a b -> a -> Translate c m a' b
apply' tr x = contextonlyT $ \ c -> Kure.apply tr c x

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

{-
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
-}

defR :: RewriteH Id -> RewriteH CoreExpr -> RewriteH Core
defR rewI rewE = prunetdR (  promoteDefR (defAllR rewI rewE)
                          <+ promoteBindR (nonRecAllR rewI rewE) )

rhsR :: RewriteH CoreExpr -> RewriteH Core
rhsR = defR idR

-- unfoldNames :: [TH.Name] -> RewriteH CoreExpr
-- unfoldNames nms = catchesM (unfoldNameR <$> nms) -- >>> cleanupUnfoldR

-- The set of variables in a HERMIT context
isLocal :: ReadBindings c => c -> (Var -> Bool)
isLocal = flip M.member . hermitBindings

-- TODO: Maybe return a predicate instead of a set. More abstract, and allows
-- for efficient construction. Here, we'd probably want to use the underlying
-- map to implement the returned predicate.

-- | Extract just the lambda-bound variables in a HERMIT context
isLocalT :: (ReadBindings c, Applicative m) => Translate c m a (Var -> Bool)
isLocalT = contextonlyT (pure . isLocal)

-- topLevelBindsR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) =>
--                   Rewrite c m CoreBind -> Rewrite c m ModGuts
-- topLevelBindsR r = modGutsR progBindsR
--   where
--     progBindsR = progConsAnyR r progBindsR

-- topLevelBindsR r = modGutsR (fix (progConsAnyR r))

type InCoreTC t = Injection t CoreTC

observing :: Bool
observing = False

observeR' :: InCoreTC t => String -> RewriteH t
observeR' | observing = observeR
          | otherwise = const idR

tries :: (InCoreTC a, InCoreTC t) => [(String,TranslateH a t)] -> TranslateH a t
tries = foldr (<+) (observeR "Unhandled" >>> fail "unhandled")
      . map (uncurry labeled)

labeled :: InCoreTC t => String -> Unop (TranslateH a t)
labeled label = (>>> observeR' label)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

type ReType = TranslateH Type CoreExpr

-- | Translate a Core type t into a core expression that evaluates to a Ty t.
reifyType :: ReType
reifyType =
  do funTId  <- findIdT '(T.:=>)
     pairTId <- findIdT '(T.:*)
     unitTId <- findIdT 'T.Unit
     intTID  <- findIdT 'T.Int
     boolTID <- findIdT 'T.Bool
     let simples :: M.Map Unique Id
         simples = M.fromList [ (unitTyConKey,unitTId),(boolTyConKey,boolTID)
                              , (intTyConKey,intTID) ]
         simpleTId :: TyCon -> Maybe Id
         simpleTId  = flip M.lookup simples . getUnique
         rew :: ReType
         rew = tries [ ("TSimple",rTSimple),("TPair",rTPair)
                     , ("TFun",rTFun), ("TSynonym",rTSyn) ]
         rTSimple, rTPair, rTFun, rTSyn :: ReType
         rTSimple = do TyConApp (simpleTId -> Just tid) [] <- idR
                       return (apps tid [] [])
         rTPair = do Just [_,_] <- unTupleTy <$> idR
                     tyConAppT (pure ()) (const rew) $ \ () [a',b'] ->
                       tyOp2 pairTId a' b'
         rTFun = funTyT rew rew $ tyOp2 funTId
         rTSyn = expandSyn >>> rew
         expandSyn :: RewriteH Type
         expandSyn = do Just t <- tcView <$> idR
                        return t
         tyOp2 :: Id -> Binop CoreExpr
         tyOp2 tid a' b' = apps tid [tyTy a',tyTy b'] [a',b']
     rew

-- TODO: Look up the ids only once in reifyExpr, not every time 'reifyType' is called.

-- tyConAppT :: (ExtendPath c Crumb, Monad m) => 
--              Translate c m TyCon a1 -> (Int -> Translate c m KindOrType a2) 
--           -> (a1 -> [a2] -> b) -> Translate c m Type b

-- The type parameter a of an expression of type Ty a.
tyTy :: CoreExpr -> Type
tyTy = dropTyApp1 ''T.Ty . exprType

type ReExpr = RewriteH CoreExpr

reifyExpr :: ReExpr
reifyExpr =
  do varId#    <- findIdT 'E.var#
     appId     <- findIdT '(E.@^)
     lamvId#   <- findIdT 'E.lamv#
     casevId#  <- findIdT 'E.casev#
     evalId    <- findIdT 'E.evalE
     reifyId   <- findIdT 'E.reifyE'
     letId     <- findIdT 'E.lett
     varPatId# <- findIdT 'E.varPat#
     pairPatId <- findIdT '(E.:#)
     asPatId#  <- findIdT 'E.asPat#
     let rew :: ReExpr
         rew = tries [ ("Var#" ,rVar#)
                     , ("Reify",rReify)
                     , ("App"  ,rApp)
                     , ("LamT" ,rLamT)
                     , ("Lam#" ,rLam#)
                     , ("Let"  ,rLet)
                     , ("Case" ,rCase)
                     ]
         rVar#  = do local <- isLocalT
                     varT $
                       do v <- idR
                          if local v then
                            do let ty = varType v
                               tye <- apply' reifyType ty
                               return $ apps varId# [ty] [varLitE v,tye]
                           else
                            fail "rVar: not a lambda-bound variable"
         -- Reify non-local variables and their polymorphic instantiations.
         rReify = do e@(collectTypeArgs -> (Var v, _)) <- idR
                     let t = exprType e
                     (str,_) <- apply' mkVarName v
                     te <- apply' reifyType t
                     return $ apps reifyId [t] [e,str,te]
         rApp  = do App (exprType -> funTy) _ <- idR
                    appT  rew rew $ arr $ \ u' v' ->
                      let (a,b) = splitFunTy funTy in
                        apps appId [b,a] [u', v'] -- note b,a
         rLamT = do Lam (isTyVar -> True) _ <- idR
                    lamT idR rew (arr Lam)
         rLam# = do Lam (varType -> vty) (exprType -> bodyTy) <- idR
                    vtye <- apply' reifyType vty
                    lamT idR rew $ arr $ \ v e' ->
                      apps lamvId# [vty, bodyTy] [varLitE v,vtye,e']
         rLet  = do -- only NonRec for now
                    Let (NonRec (varType -> patTy) _) (exprType -> bodyTy) <- idR
                    letT reifyBind rew $ \ (patE,rhs') body' ->
                      apps letId [patTy,bodyTy] [patE,rhs',body']
         -- For now, handling only single-branch case expressions containing
         -- pair patterns. The result will be to form nested lambda patterns in
         -- a beta redex.
         rCase = do Case (exprType -> scrutT) wild _ [_] <- idR
                    _ <- observeR' "Reifying case"
                    caseT rew idR idR (const (reifyAlt wild)) $
                      \ scrutE' _ bodyT [(patE,rhs)] ->
                          apps letId [scrutT,bodyT] [patE,scrutE',rhs]
         -- Reify a case alternative, yielding a reified pattern and a reified
         -- alternative body (RHS).
         reifyAlt :: Var -> TranslateH CoreAlt (CoreExpr,CoreExpr)
         reifyAlt wild =
           do -- Only pair patterns for now
              _ <- observeR' "Reifying case alternative"
              (DataAlt (isTupleTyCon.dataConTyCon -> True), vars@[_,_], _) <- idR
              vPats <- mapM (apply' (labeled "varPatT" varPatT#)) vars
              altT idR (const idR) rew $ \ _ _ rhs' ->
                let pat  = apps pairPatId (varType <$> vars) vPats
                    pat' | wild `S.member` coreExprFreeIds rhs'
                         = -- WARNING: untested as of 2013-07-22
                           apps asPatId# [varType wild] [varLitE wild,pat]
                         | otherwise = pat
                in
                  (pat', rhs')
         varPatT# :: TranslateH Var CoreExpr
         varPatT# = do v <- idR
                       let ty = varType v
                       tye <- apply' reifyType ty
                       return $ apps varPatId# [ty] [varLitE v,tye]
         -- Reify a Core binding into a reified pattern and expression.
         -- Only handle NonRec bindings for now.
         reifyBind :: TranslateH CoreBind (CoreExpr,CoreExpr)
         reifyBind = nonRecT varPatT# rew (,)
         -- TODO: Literals
     do _ <- observeR' "Reifying expression "
        ty <- arr exprType
        let mkEval e' = apps evalId [ty] [e']
        mkEval <$> rew

reifyExprC :: RewriteH Core
reifyExprC = tryR unshadow >>> promoteExprR reifyExpr

-- unshadow since we extract variable names without the uniques

{-
letT :: (ExtendPath c Crumb, AddBindings c, Monad m)
     => Translate c m CoreBind a1
     -> Translate c m CoreExpr a2
     -> (a1 -> a2 -> b) 
     -> Translate c m CoreExpr b

caseT :: (ExtendPath c Crumb, AddBindings c, Monad m)
      => Translate c m CoreExpr e
      -> Translate c m Id w
      -> Translate c m Type ty
      -> (Int -> Translate c m CoreAlt alt)
      -> (e -> w -> ty -> [alt] -> b)
      -> Translate c m CoreExpr b

altT :: (ExtendPath c Crumb, AddBindings c, Monad m)
     => Translate c m AltCon a1
     -> (Int -> Translate c m Var a2)
     -> Translate c m CoreExpr a3
     -> (a1 -> [a2] -> a3 -> b)
     -> Translate c m CoreAlt b
-}

mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqName . varName

anybuER :: (MonadCatch m, Walker c g, ExtendPath c Crumb, Injection CoreExpr g) =>
           Rewrite c m CoreExpr -> Rewrite c m g
anybuER r = anybuR (promoteExprR r)

anytdER :: (MonadCatch m, Walker c g, ExtendPath c Crumb, Injection CoreExpr g) =>
           Rewrite c m CoreExpr -> Rewrite c m g
anytdER r = anytdR (promoteExprR r)

tryRulesBU :: [String] -> RewriteH Core
tryRulesBU = tryR . anybuER . rules

reifyRules :: RewriteH Core
reifyRules = tryRulesBU $ map ("reify/" ++)
  ["not","(&&)","(||)","xor","(+)","exl","exr","pair","inl","inr","if","false","true"]

-- or: words $ "not (&&) (||) xor ..."

-- TODO: Is there a way not to redundantly specify this rule list?
-- Yes -- trust GHC to apply the rules later.

reifyDef :: RewriteH Core
reifyDef = rhsR reifyExpr

reifyEval :: ReExpr
reifyEval = reifyArg >>> evalArg
 where
   reifyArg = do (_reifyE', [Type _, _str, arg, _ty]) <- callNameT 'E.reifyE'
                 return arg
   evalArg  = do (_evalE, [Type _, body])       <- callNameT 'E.evalE
                 return body

-- TODO: Replace reifyEval with tryRulesBU ["reify'/eval","eval/reify'"]

-- reifyEval = 

-- rswE = reifyE' ▲ (evalE ▲ swapBI_reified) ($fHasTy(->) ▲ ▲ tup ▹ ■)

inlineCleanup :: TH.Name -> RewriteH Core
inlineCleanup nm = tryR $ anybuER (inlineName nm) >>> anybuER cleanupUnfoldR

inlineNamesTD :: [TH.Name] -> RewriteH Core
inlineNamesTD nms = anytdER (catchesM (inlineName <$> nms))

reifyNamed :: TH.Name -> RewriteH Core
reifyNamed nm = snocPathIn (rhsOf nm)
                  (   inlineCleanup 'E.ifThenElse
                  -- >>> (tryR $ anytdER $ rule "if/pair")
                  >>> reifyExprC
                  >>> reifyRules
                  >>> pathR [App_Arg] (promoteExprR (letIntro nm'))
                  >>> promoteExprR letFloatArg
                  )
            >>> snocPathIn (parentOf (bindingGroupOf nm))
                  (promoteProgR letFloatLetTop)
            >>> inlineCleanup nm
            >>> inlineCleanup 'E.reifyE
            -- >>> tryR (anybuER (promoteExprR reifyEval))
            >>> tryRulesBU ["reify'/eval","eval/reify'"]
            >>> simplifyR  -- For the rule applications at least
 where
   nm' = TH.showName nm ++ "_reified"


-- I don't know why I need both cleanupUnfoldR and simplifyR.

-- Note: I inline reifyE to its reifyE' definition and then simplify
-- reifyE'/evalE, rather than simplifying reifyE/evalE. With this choice, I can
-- also reifyE'/evalE combinations that come from reifyE in source code and ones
-- that reifyExpr inserts.

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
    , external "inline-cleanup"
        (inlineCleanup :: TH.Name -> RewriteH Core)
        ["inline a named definition, and clean-up beta-redexes"]
    , external "inline-names-td"
        (inlineNamesTD :: [TH.Name] -> RewriteH Core)
        ["inline given names, traversing top-down"]
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
--     , external "reify-tops"
--         (reifyTops :: RewriteH ModGuts)
--         ["reify via name"]
    , external "reify-eval"
        (promoteExprR reifyEval :: RewriteH Core)
        ["simplify reifyE' composed with evalE"]
    ]
