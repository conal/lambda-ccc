{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- TODO: Restore the following pragmas

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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
import Control.Arrow (arr,(>>>))
import Data.List (intercalate)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Text.Printf (printf)

-- import qualified Language.Haskell.TH as TH (Name) -- ,mkName
-- import qualified Language.Haskell.TH.Syntax as TH (showName)

-- GHC API
-- import PrelNames (unitTyConKey,boolTyConKey,intTyConKey)

import qualified Language.KURE.Translate as Kure
import HERMIT.Monad (HermitM,newIdH)
import HERMIT.Context
  (ReadBindings(..),hermitBindings,HermitBinding(..),HermitBindingSite(..)
  ,lookupHermitBinding,boundIn,BoundVars,HasGlobalRdrEnv(..)) -- ,AddBindings
import HERMIT.Core (Crumb(..),localFreeIdsExpr)
import HERMIT.External
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure hiding (apply)
import HERMIT.Plugin

-- Note: All of the Dictionary submodules are now re-exported by HERMIT.Dictionary,
--       so if you prefer you could import all these via that module, rather than seperately.
import HERMIT.Dictionary.AlphaConversion (unshadowR)
import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Composite (simplifyR)
import HERMIT.Dictionary.Debug (observeR)
import HERMIT.Dictionary.Rules (rulesR) -- ruleR,
import HERMIT.Dictionary.Inline (inlineNameR) -- , inlineNamesR
import HERMIT.Dictionary.Local (letIntroR,letFloatArgR,letFloatTopR)
import HERMIT.Dictionary.Navigation (rhsOfT,parentOfT,bindingGroupOfT)
-- import HERMIT.Dictionary.Composite (simplifyR)
import HERMIT.Dictionary.Unfold (cleanupUnfoldR) -- unfoldNameR,

import LambdaCCC.Misc (Unop) -- ,Binop
-- import qualified LambdaCCC.Ty as T
-- import qualified LambdaCCC.Prim as P
-- import qualified LambdaCCC.Lambda as E
-- import LambdaCCC.MkStringExpr (mkStringExpr)

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
collectTypeArgs :: CoreExpr -> ([Type], CoreExpr)
collectTypeArgs expr = go [] expr
  where
    go ts (App f (Type t)) = go (t:ts) f
    go ts                e = (reverse ts, e)

collectForalls :: Type -> ([Var], Type)
collectForalls ty = go [] ty
  where
    go vs (ForAllTy v t') = go (v:vs) t'
    go vs t               = (reverse vs, t)

-- TODO: Rewrite collectTypeArgs and collectForalls as unfolds and refactor.

#if 0

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

#endif

-- Substitute a new subexpression for a variable in an expression
subst1 :: (Id,CoreExpr) -> CoreExpr -> CoreExpr
subst1 (v,new) = substExpr (error "subst1: no SDoc")
                    (extendIdSubst emptySubst v new)

{--------------------------------------------------------------------
    KURE utilities
--------------------------------------------------------------------}

-- -- | Transformation while focused on a path
-- pathIn :: (Eq crumb, ReadPath c crumb, MonadCatch m, Walker c b) =>
--           Translate c m b (Path crumb) -> Unop (Rewrite c m b)
-- pathIn mkP f = mkP >>= flip pathR f

-- | Transformation while focused on a snoc path
snocPathIn :: ( Eq crumb, Functor m, ReadPath c crumb
              , MonadCatch m, Walker c b ) =>
              Translate c m b (SnocPath crumb) -> Unop (Rewrite c m b)
snocPathIn mkP r = mkP >>= flip localPathR r

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

-- Next two from Andy G:

-- | Lookup the name in the context first, then, failing that, in GHC's global
-- reader environment.
findTyConT :: ( BoundVars c, HasGlobalRdrEnv c, HasDynFlags m
              , MonadThings m, MonadCatch m) =>
              String -> Translate c m a TyCon
findTyConT nm = prefixFailMsg ("Cannot resolve name " ++ nm ++ ", ") $
                contextonlyT (findTyConMG nm)

findTyConMG :: (BoundVars c, HasGlobalRdrEnv c, HasDynFlags m, MonadThings m) => String -> c -> m TyCon
findTyConMG nm c =
    case filter isTyConName $ findNamesFromString (hermitGlobalRdrEnv c) nm of
      [n] -> lookupTyCon n
      ns  -> do dynFlags <- getDynFlags
                fail $ "multiple matches found:\n" ++ intercalate ", " (map (showPpr dynFlags) ns)

#if 0
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
  \ case (collectTypeArgs -> (ts, Var v)) ->
           liftM2 h (Kure.apply tv (applyN (length ts) (@@ App_Fun) c) v)
                    (return ts)
         _ -> fail "not an application of a variable to types."
  where
    applyN :: Int -> (a -> a) -> a -> a
    applyN n f a = foldr ($) a (replicate n f)
#endif

defR :: RewriteH Id -> RewriteH CoreExpr -> RewriteH Core
defR rewI rewE = prunetdR (  promoteDefR (defAllR rewI rewE)
                          <+ promoteBindR (nonRecAllR rewI rewE) )

rhsR :: RewriteH CoreExpr -> RewriteH Core
rhsR = defR idR

-- unfoldNames :: [TH.Name] -> RewriteH CoreExpr
-- unfoldNames nms = catchesM (unfoldNameR <$> nms) -- >>> cleanupUnfoldR

-- The set of variables in a HERMIT context
isLocal :: ReadBindings c => c -> (Var -> Bool)
isLocal = flip boundIn

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

#if 0

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

#endif

type ReExpr = RewriteH CoreExpr

lamName :: Unop String
lamName = ("LambdaCCC.Lambda." ++)

findIdE :: String -> TranslateH a Id
findIdE = findIdT . lamName

findTyConE :: String -> TranslateH a TyCon
findTyConE = findTyConT . lamName

reifyExpr :: ReExpr
reifyExpr =
  do varId#    <- findIdE "varP#"    -- "var#"
     appId     <- findIdE "appP"     -- "(@^)"
     lamvId#   <- findIdE "lamvP#"   -- "lamv#"
  -- casevId#  <- findIdE "casevP#"  -- "casev#"
     evalId    <- findIdE "evalEP"   -- "evalEP"
     reifyId#  <- findIdE "reifyEP#" -- "reifyE#"
     letId     <- findIdE "lettP"    -- "lett"
     varPatId# <- findIdE "varPat#"
     pairPatId <- findIdE ":#"
     asPatId#  <- findIdE "asPat#"
     -- primId#   <- findIdT ''P.Prim   -- not found! :/
     -- testEId  <- findIdT "EP"
     epTC      <- findTyConE "EP"
     let reifyRhs :: RewriteH CoreExpr
         reifyRhs =
           do ty <- arr exprType
              let (tyVars,ty') = collectForalls ty
                  mkEval (collectTyBinders -> (tyVars',body)) =
                    if tyVars == tyVars' then
                      mkLams tyVars (apps evalId [ty'] [body])
                    else
                      error $ "mkEval: type variable mismatch: "
                        ++ show (uqVarName <$> tyVars, uqVarName <$> tyVars')
                    -- If I ever get the type variable mismatch error, take a
                    -- different approach, extracting the type of e' and
                    -- dropping the EP.
              mkEval <$> rew
          where
            eTy e = TyConApp epTC [e]
            eVar :: Var -> HermitM Var
            eVar v = newIdH (uqVarName v ++ "E") (eTy (varType v))
            rew :: ReExpr
            rew = tries [ ("Eval" ,rEval)
                        , ("Reify",rReify)
                        , ("AppT" ,rAppT)
                        , ("Var#" ,rVar#)
                        , ("LamT" ,rLamT)
                        , ("App"  ,rApp)
                        , ("Lam#" ,rLam#)
                        , ("Let"  ,rLet)
                        , ("Case" ,rCase)
                        ]
             where
--             rVar#  = do local <- isLocalT
--                         varT $
--                           do v <- idR
--                              if local v then
--                                return $ apps varId# [varType v] [varLitE v]
--                               else
--                                fail "rVar: not a lambda-bound variable"
            
            -- reify (eval e) == e
            rEval = do (_evalE, [Type _, e]) <- callNameLam "evalEP"
                       return e
            -- Reify non-local variables and their polymorphic instantiations.
            rReify = do local <- isLocalT
                        e@(collectTypeArgs -> (_, Var v)) <- idR
                        if local v then
                          fail "rReify: lambda-bound variable"
                         else
                          return $ apps reifyId# [exprType e] [e,varLitE v]
            rAppT = do App _ (Type _) <- idR   -- Type applications
                       appT rew idR (arr App)
            rLamT = do Lam (isTyVar -> True) _ <- idR
                       lamT idR rew (arr Lam)
            rApp  = do App (exprType -> funTy) _ <- idR
                       appT rew rew $ arr $ \ u' v' ->
                         let (a,b) = splitFunTy funTy in
                           apps appId [b,a] [u', v'] -- note b,a
#if 0       
            rLam# = translate $ \ c -> \case
                      Lam v@(varType -> vty) e ->
                        do eV <- eVar v
                           e' <- Kure.apply rew (c @@ Lam_Body) $
                                   subst1 (v, apps evalId [vty] [
                                                apps varId# [vty] [varLitE eV]]) e
                           return (apps lamvId# [vty, exprType e] [varLitE eV,e'])
                      _       -> fail "not a lambda."
#else       
            rLam# = do Lam (varType -> vty) (exprType -> bodyTy) <- idR
                       lamT idR rew $ arr $ \ v e' ->
                         apps lamvId# [vty, bodyTy] [varLitE v,e']
#endif      
            -- TODO: Eliminate rVar#
            rVar# :: ReExpr
            rVar#  = do local <- isLocalT
                        Var v <- idR
                        if local v then
                          return $ apps varId# [varType v] [varLitE v]
                         else
                          fail "rVar: not a lambda-bound variable"
#if 0       
            rLet  = do -- only NonRec for now
                       Let (NonRec (varType -> patTy) _) (exprType -> bodyTy) <- idR
                       letT reifyBind rew $ \ (patE,rhs') body' ->
                         apps letId [patTy,bodyTy] [patE,rhs',body']
#else       
            rLet  = toRedex >>> rew
             where
               toRedex = do Let (NonRec v rhs) body <- idR
                            return (Lam v body `App` rhs)
            
#endif      
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
                 vPats <- mapM (applyInContextT (labeled "varPatT" varPatT#)) vars
                 altT idR (const idR) rew $ \ _ _ rhs' ->
                   let pat  = apps pairPatId (varType <$> vars) vPats
                       pat' | wild `elemVarSet` localFreeIdsExpr rhs'
                            = -- WARNING: untested as of 2013-07-22
                              apps asPatId# [varType wild] [varLitE wild,pat]
                            | otherwise = pat
                   in
                     (pat', rhs')
            varPatT# :: TranslateH Var CoreExpr
            varPatT# = do v <- idR
                          return $ apps varPatId# [varType v] [varLitE v]
            -- Reify a Core binding into a reified pattern and expression.
            -- Only handle NonRec bindings for now.
            reifyBind :: TranslateH CoreBind (CoreExpr,CoreExpr)
            reifyBind = nonRecT varPatT# rew (,)
         -- TODO: Literals
     do _ <- observeR' "Reifying expression"
        reifyRhs

reifyExprC :: RewriteH Core
reifyExprC = tryR unshadowR >>> promoteExprR reifyExpr

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

-- mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
-- mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqVarName

uqVarName :: Var -> String
uqVarName = uqName . varName

anybuER :: (MonadCatch m, Walker c g, ExtendPath c Crumb, Injection CoreExpr g) =>
           Rewrite c m CoreExpr -> Rewrite c m g
anybuER r = anybuR (promoteExprR r)

-- anytdER :: (MonadCatch m, Walker c g, ExtendPath c Crumb, Injection CoreExpr g) =>
--            Rewrite c m CoreExpr -> Rewrite c m g
-- anytdER r = anytdR (promoteExprR r)

tryRulesBU :: [String] -> RewriteH Core
tryRulesBU = tryR . anybuER . rulesR

reifyRules :: RewriteH Core
reifyRules = tryRulesBU $ map ("reify/" ++)
  ["not","(&&)","(||)","xor","(+)","exl","exr","pair","inl","inr","if","false","true"]

-- or: words $ "not (&&) (||) xor ..."

-- TODO: Is there a way not to redundantly specify this rule list?
-- Yes -- trust GHC to apply the rules later.

reifyDef :: RewriteH Core
reifyDef = rhsR reifyExpr

callNameLam :: String -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callNameLam = callNameT . lamName

-- Unused
reifyEval :: ReExpr
reifyEval = reifyArg >>> evalArg
 where
   reifyArg = do (_reifyE, [Type _, arg, _str]) <- callNameLam "reifyEP"
                 return arg
   evalArg  = do (_evalE, [Type _, body])            <- callNameLam "evalEP"
                 return body

-- TODO: reifyEval replaced with tryRulesBU ["reify'/eval","eval/reify'"], and
-- even those rules are no longer invoked explicitly.

inlineCleanup :: String -> RewriteH Core
inlineCleanup nm = tryR $ anybuER (inlineNameR nm) >>> anybuER cleanupUnfoldR

-- inlineNamesTD :: [String] -> RewriteH Core
-- inlineNamesTD nms = anytdER (inlineNamesR nms)

-- #define FactorReified

reifyNamed :: String -> RewriteH Core
reifyNamed nm = snocPathIn (rhsOfT cmpNm)
                  (   inlineCleanup (lamName "ifThenElse")
                  -- >>> (tryR $ anytdER $ rule "if/pair")
                  >>> reifyExprC
                  >>> reifyRules
#ifdef FactorReified
                  >>> pathR [App_Arg] (promoteExprR (letIntroR (nm ++ "_reified")))
                  >>> promoteExprR letFloatArgR
#endif
                  )
#ifdef FactorReified
            >>> snocPathIn (extractT $ parentOfT $ bindingGroupOfT $ cmpNm)
                  (promoteProgR letFloatTopR)
#endif
            >>> inlineCleanup nm
            -- I don't know why the following is needed, considering the INLINE
            >>> inlineCleanup (lamName "reifyEP#")
            -- >>> tryR (anybuER (promoteExprR reifyEval))
            -- >>> tryRulesBU ["reifyE/evalE","evalE/reifyE"]
            -- >>> tryRulesBU ["reifyEP/evalEP"]
            >>> tryR simplifyR  -- For the rule applications at least
 where
   cmpNm = cmpString2Var nm

-- I don't know why I need both cleanupUnfoldR and simplifyR.

-- Note: I inline reifyE to its reifyE definition and then simplify
-- reifyE/evalE, rather than simplifying reifyE/evalE. With this choice, I can
-- also reifyE/evalE combinations that come from reifyE in source code and ones
-- that reifyExpr inserts.

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-expr"
        (promoteExprR reifyExpr :: RewriteH Core)
        ["Reify a Core expression into a GADT construction"]
    , external "reify-rules"
        (reifyRules :: RewriteH Core)
        ["convert some non-local vars to consts"]
    , external "inline-cleanup"
        (inlineCleanup :: String -> RewriteH Core)
        ["inline a named definition, and clean-up beta-redexes"]
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
        (reifyNamed :: String -> RewriteH Core)
        ["reify via name"]
--     , external "reify-tops"
--         (reifyTops :: RewriteH ModGuts)
--         ["reify via name"]
    , external "reify-eval"
        (anybuER (promoteExprR reifyEval) :: RewriteH Core)
        ["simplify reifyE composed with evalE"]
    ]
