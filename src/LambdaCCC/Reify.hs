{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

-- TODO: Restore the following pragmas

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Reify
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Reify a Core expression into GADT
----------------------------------------------------------------------

module LambdaCCC.Reify (plugin) where

import Data.Functor ((<$>))
import Control.Monad ((<=<))
import Control.Arrow (Arrow(..),(>>>))

import PrelNames (liftedTypeKindTyConKey)
import Unique(hasKey)

import HERMIT.Monad (newIdH)
import HERMIT.Core (localFreeIdsExpr,CoreProg(..),bindsToProg,progToBinds)
import HERMIT.External (External,external,ExternalName)
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( observeR,callNameT
  , rulesR,inlineR,simplifyR,letFloatLetR,letFloatTopR,letElimR
  , betaReduceR, letNonRecSubstSafeR
  -- , unshadowR   -- May need this one later
  )
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import LambdaCCC.Misc (Unop,(<~))

import TypeEncode.Plugin
  ( apps', ReExpr ,ReCore, TranslateU, findTyConT
  , reCaseR, reConstructR, encodeTypesR )

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

collectForalls :: Type -> ([Var], Type)
collectForalls ty = go [] ty
  where
    go vs (ForAllTy v t') = go (v:vs) t'
    go vs t               = (reverse vs, t)

-- TODO: Rewrite collectTypeArgs and collectForalls as unfolds and refactor.

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> CoreExpr -> CoreExpr
subst ps = substExpr (error "subst: no SDoc") (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new

isTyLam :: CoreExpr -> Bool
isTyLam (Lam v _) = isTyVar v
isTyLam _         = False

kindIsStar :: Kind -> Bool
kindIsStar (TyConApp tc []) = tc `hasKey` liftedTypeKindTyConKey
kindIsStar _                = False

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

type InCoreTC t = Injection t CoreTC

observing :: Bool
observing = False

observeR' :: InCoreTC t => String -> RewriteH t
observeR' | observing = observeR
          | otherwise = const idR

tries :: (InCoreTC a, InCoreTC t) => [(String,TranslateH a t)] -> TranslateH a t
tries = foldr (<+) (observeR' "Unhandled" >>> fail "unhandled")
      . map (uncurry labeled)

labeled :: InCoreTC t => String -> Unop (TranslateH a t)
labeled label = (>>> observeR' label)

-- mkVarName :: MonadThings m => Translate c m Var (CoreExpr,Type)
-- mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqVarName

uqVarName :: Var -> String
uqVarName = uqName . varName

-- Fully type-eta-expand, i.e., ensure that every leading forall has a matching
-- (type) lambdas.
typeEtaLong :: ReExpr
typeEtaLong = readerT $ \ e ->
                 if isTyLam e then
                   lamAllR idR typeEtaLong
                 else
                   expand
 where
   -- Eta-expand enough for lambdas to match foralls.
   expand = do e@(collectForalls . exprType -> (tvs,_)) <- idR
               return $ mkLams tvs (mkApps e ((Type . TyVarTy) <$> tvs))

simplifyE :: ReExpr
simplifyE = extractR simplifyR

-- TODO: Try rewriting more gracefully, testing isForAllTy first and
-- maybeEtaExpandR

-- Apply a rewriter inside type lambdas.
inAppTys :: Unop ReExpr
inAppTys r = r'
 where
   r' = readerT $ \ e -> if isAppTy e then appAllR r' idR else r

isAppTy :: CoreExpr -> Bool
isAppTy (App _ (Type _)) = True
isAppTy _                = False

letFloatToProg :: TranslateH CoreBind CoreProg
letFloatToProg = arr (flip ProgCons ProgNil) >>> tryR letFloatTopR

concatProgs :: [CoreProg] -> CoreProg
concatProgs = bindsToProg . concatMap progToBinds

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

lamName :: Unop String
lamName = ("LambdaCCC.Lambda." ++)

-- findIdE :: String -> TranslateH a Id
-- findIdE = findIdT . lamName

findTyConE :: String -> TranslateH a TyCon
findTyConE = findTyConT . lamName

appsE :: String -> [Type] -> [CoreExpr] -> TranslateU CoreExpr
appsE = apps' . lamName

-- A handy form for composition via <=<
appsE1 :: String -> [Type] -> CoreExpr -> TranslateU CoreExpr
appsE1 str ts e = appsE str ts [e]

-- Some names

evalS, reifyS :: String
evalS = "evalEP"
reifyS = "reifyEP"

varPS, letS, varPatS :: String
varPS   = "varP#"
letS    = "lettP"
varPatS = "varPat#"

epS :: String
epS = "EP"

-- t --> EP t
epOf :: Type -> TranslateH a Type
epOf t = do epTC <- findTyConE epS
            return (TyConApp epTC [t])

-- reify u --> u
unReify :: ReExpr
unReify = do (_reifyE, [Type _, arg]) <- callNameLam reifyS
             return arg
-- eval e --> e
unEval :: ReExpr
unEval = do (_evalE, [Type _, body]) <- callNameLam evalS
            return body

-- reify (eval e) --> e
reifyEval :: ReExpr
reifyEval = unReify >>> unEval

reifyOf :: CoreExpr -> TranslateU CoreExpr
reifyOf e = do guardMsg (kindIsStar (typeKind ty))
                 "reifyLam: doesn't handle type lambda"
               appsE reifyS [exprType e] [e]
 where
   ty = exprType e

evalOf :: CoreExpr -> TranslateU CoreExpr
evalOf e = appsE evalS [dropEP (exprType e)] [e]

dropEP :: Unop Type
dropEP (TyConApp (uqName . tyConName -> name) [t]) =
  if name == epS then t
  else error ("dropEP: not an EP: " ++ show name)
dropEP _ = error "dropEP: not a TyConApp"

reifyR :: ReExpr
reifyR = idR >>= reifyOf

evalR :: ReExpr
evalR = idR >>= evalOf

-- reify (u v) --> reify u `appP` reify v
reifyApp :: ReExpr
reifyApp = do App u v <- unReify
              Just (a,b) <- constT (return (splitFunTy_maybe (exprType u)))
              u' <- reifyOf u
              v' <- reifyOf v
              appsE "appP" [b,a] [u', v'] -- note b,a

-- TODO: refactor so we unReify once and then try variations

varEval :: Var -> TranslateU CoreExpr
varEval v = (evalOf <=< appsE1 varPS [varType v]) (varLitE v)

varSubst :: [Var] -> TranslateU (Unop CoreExpr)
varSubst vs = do vs' <- mapM varEval vs
                 return (subst (vs `zip` vs'))

reifyLam :: ReExpr
reifyLam = do Lam v e <- unReify
              guardMsg (not (isTyVar v)) "reifyLam: doesn't handle type lambda"
              sub     <- varSubst [v]
              e'      <- reifyOf (sub e)
              appsE "lamvP#" [varType v, exprType e] [varLitE v,e']

-- Pass through unless an IO
unlessTC :: String -> ReExpr
unlessTC name = acceptR (not . hasTC name . exprType)

-- Pass through unless an eval application
unlessEval :: ReExpr
unlessEval = acceptR (not . isEval)

hasTC :: String -> Type -> Bool
hasTC name (TyConApp tc [_]) = uqName (tyConName tc) == name
hasTC _ _                    = False

isEval :: CoreExpr -> Bool
isEval (App (App (Var v) (Type _)) _) = uqVarName v == evalS
isEval _                              = False

isTyLamsEval :: CoreExpr -> Bool
isTyLamsEval = isEval . snd . collectTyBinders

reifyPolyLet :: ReExpr
reifyPolyLet = unReify >>>
               do Let (NonRec (isForAllTy . varType -> True) _) _ <- idR
                  letAllR reifyDef reifyR >>> letFloatLetR

-- reifyDef introduces foo_reified binding, which the letFloatLetR then moves up
-- one level. Typically (always?) the "foo = eval foo_reified" definition gets
-- inlined and then eliminated by the letElimR in reifyMisc.

monoLetToRedex :: ReExpr
monoLetToRedex = do Let (NonRec v@(isForAllTy . varType -> False) rhs) body <- idR
                    return (Lam v body `App` rhs)

-- TODO: Perhaps combine reifyPolyLet and monoLetToRedex into reifyLet

#define SplitEval

#ifdef SplitEval

-- e --> eval (reify e) in preparation for rewriting reify e.
-- Fail if e is already an eval or if it has IO or EP type.
reifyRhs :: String -> ReExpr
reifyRhs nm =
  unlessTC "IO" >>> unlessTC epS >>> unlessEval >>>
  typeEtaLong >>>
  do (tvs,body) <- collectTyBinders <$> idR
     eTy        <- epOf (exprType body)
     v          <- constT $ newIdH (nm ++ "_reified") (mkForAllTys tvs eTy)
     reified    <- mkLams tvs <$> reifyOf body
     evald      <- evalOf (mkCoreApps (Var v) ((Type . TyVarTy) <$> tvs))
     return $
       Let (NonRec v reified) (mkLams tvs evald)

reifyDef :: RewriteH CoreBind
reifyDef = do NonRec v _ <- idR
              nonRecAllR idR (reifyRhs (uqVarName v))

reifyProg :: RewriteH CoreProg
reifyProg = progBindsT (const (tryR reifyDef >>> letFloatToProg)) concatProgs

#else

-- Apply a rewriter inside type lambdas, type-eta-expanding if necessary.
inTyLams :: Unop ReExpr
inTyLams r = r'
 where
   r' = readerT $ \ e ->
          if | isTyLam e               -> lamAllR idR r'
             | isForAllTy (exprType e) -> etaExpandR "eta" >>> r'
             | otherwise               -> r

-- e --> eval (reify e) in preparation for rewriting reify e.
-- Fail if e is already an eval or if it has IO or EP type.
-- If there are any type lambdas, skip over them.
reifyRhs :: ReExpr
reifyRhs = inTyLams $
             unlessEval >>> unlessTC "IO" >>> unlessTC epS >>>
             reifyR >>> evalR

reifyDef :: RewriteH CoreBind
reifyDef = nonRecAllR idR reifyRhs

reifyProg :: RewriteH CoreProg
reifyProg = progBindsAnyR (const reifyDef)

#endif

reifyModGuts :: RewriteH ModGuts
reifyModGuts = modGutsR reifyProg

-- TODO: How to float the local bindings as well?

-- TODO: Use arr instead of (consT (return (f ...)))

-- Inline if doing so yields an eval
inlineEval :: ReExpr
inlineEval = inAppTys (inlineR >>> acceptR isTyLamsEval) >>> tryR simplifyE

-- The simplifyE is for beta-reducing type applications.

-- Rewrite inside of reify applications
inReify :: Unop ReExpr
inReify = reifyR <~ unReify

reifyInline :: ReExpr
reifyInline = inReify inlineEval

reifyRuleNames :: [String]
reifyRuleNames = map ("reify/" ++)
  [ "not","(&&)","(||)","xor","(+)","exl","exr","pair","inl","inr"
  , "if","false","decode","encode","true","if-bool","if-pair" ]

-- or: words "not (&&) (||) xor ..."

-- TODO: Is there a way not to redundantly specify this rule list?
-- Yes -- trust GHC to apply the rules later.
-- Keep for now, to help us see that whether reify applications vanish.

reifyRules :: ReExpr
reifyRules = rulesR reifyRuleNames >>> tryR simplifyE

-- reifyRules = rulesR reifyRuleNames >>> tryR (extractR tidy)
--  where
--    tidy :: ReCore
--    tidy = anybuR (promoteR (betaReduceR >>> letNonRecSubstSafeR))

typeBetaReduceR :: ReExpr
typeBetaReduceR = do (isTyLam -> True) `App` _ <- idR
                     betaReduceR >>> letNonRecSubstSafeR

reifyTupCase :: ReExpr
reifyTupCase =
  do Case scrut@(exprType -> scrutT) wild bodyT [branch] <- unReify
     (patE,rhs) <- reifyBranch wild branch
     scrut'     <- reifyOf scrut
     appsE letS [scrutT,bodyT] [patE,scrut',rhs]
 where
   -- Reify a case alternative, yielding a reified pattern and a reified
   -- alternative body (RHS). Only unit and pair patterns. Others are
   -- transformed away in the type-encode plugin.
   reifyBranch :: Var -> CoreAlt -> TranslateU (CoreExpr,CoreExpr)
   reifyBranch wild (DataAlt ( isTupleTyCon . dataConTyCon -> True)
                             , vars, rhs ) =
     do guardMsg (length vars `elem` [0,2])
          "Only handles unit and pair patterns"
        vPats <- mapM varPatT vars
        sub   <- varSubst (wild : vars)
        pat   <- if null vars then
                   appsE "UnitPat" [] []
                  else
                   appsE ":#" (varType <$> vars) vPats
        pat'  <- if wild `elemVarSet` localFreeIdsExpr rhs
                   then -- WARNING: untested as of 2014-03-11
                     appsE "asPat#" [varType wild] [varLitE wild,pat]
                   else
                     return pat
        rhs'  <- reifyOf (sub rhs)
        return (pat', rhs')
    where
      varPatT :: Var -> TranslateU CoreExpr
      varPatT v = appsE varPatS [varType v] [varLitE v]
   reifyBranch _ _ = fail "reifyBranch: Only handles pair patterns so far."

reifyEither :: ReExpr

#if 1

splitTysVals :: [Expr b] -> ([Type], [Expr b])
splitTysVals (Type ty : rest) = first (ty :) (splitTysVals rest)
splitTysVals rest             = ([],rest)

callNameSplitT :: MonadCatch m => String
               -> Translate c m CoreExpr (CoreExpr, [Type], [Expr CoreBndr])
callNameSplitT name = do (f,args) <- callNameT name
                         let (tyArgs,valArgs) = splitTysVals args
                         return (f,tyArgs,valArgs)

-- TODO: Move splitTysVals and callNameSplitT

reifyEither = unReify >>>
              do (_either, tys, funs@[_,_]) <- callNameSplitT "either"
                 funs' <- mapM reifyOf funs
                 appsE "eitherEP" tys funs'

-- Since 'either f g' has a function type, there could be more parameters.
-- I only want two. The others will get removed by reifyApp.

-- Important: reifyEither must come before reifyApp in reifyMisc, so that we can
-- see 'either' applied.

#else

eitherTy :: Type -> Type -> TranslateU Type
eitherTy a b = do tc <- findTyConT "Either"
                  return (TyConApp tc [a,b])

unEitherTy :: Type -> TranslateU (Type,Type)
unEitherTy (TyConApp tc [a,b]) =
  do etc <- findTyConT "Either"
     guardMsg (tyConName tc == tyConName etc)
              "unEitherTy: not an Either"
     return (a,b)
unEitherTy _ = fail "unEitherTy: wrong shape"

-- reify (case scrut of { Left lv -> le ; Right rv -> re })  --> 
-- appE (eitherE (reify (\ lv -> le)) (reify (\ rv -> re))) (reify scrut)

-- Now removed in the type-encode plugin

reifyEither =
  do Case scrut wild bodyT alts@[_,_] <- unReify
     (lt,rt) <- unEitherTy (exprType scrut)
     [le,re] <- mapM (reifyBranch wild) alts
     e       <- appsE "eitherEP" [lt,rt,bodyT] [le,re]
     t       <- eitherTy lt rt
     scrut'  <- reifyOf scrut
     appsE "appP" [bodyT,t] [e,scrut']
 where
   reifyBranch :: Var -> CoreAlt -> TranslateU CoreExpr
   reifyBranch _wild (DataAlt _, [var], rhs) = reifyOf (Lam var rhs)
   reifyBranch _ _ = error "reifyEither: bad branch"

-- TODO: check for wild in rhs. In that case, I guess I'll have to reify the Lam
-- manually in order to get the as pattern. Hm.

#endif

reifyMisc :: ReExpr
reifyMisc = tries [ ("reifyEval"      , reifyEval)
                  , ("reifyEither"    , reifyEither)  -- before App
                  , ("reifyApp"       , reifyApp)
                  , ("reifyLam"       , reifyLam)
                  , ("reifyPolyLet"   , reifyPolyLet)
                  , ("reifyTupCase"   , reifyTupCase)
                  , ("reifyInline"    , reifyInline)
                  , ("reifyRules"     , reifyRules)
                  -- Helpers:
                  , ("monoLetToRedex" , monoLetToRedex)
                  , ("typeBetaReduceR", typeBetaReduceR)
                  , ("letElim"        , letElimR)  -- Note
                  -- Data type encoding
                  -- , ("encodeTypesR"   , encodeTypesR)
                  ]


-- Note: letElim is handy with reifyPolyLet to eliminate the "foo = eval
-- foo_reified", which is usually inaccessible.

callNameLam :: String -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callNameLam = callNameT . lamName

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externC :: Injection a Core =>
           ExternalName -> RewriteH a -> String -> External
externC name rew help = external name (promoteR rew :: ReCore) [help]

externals :: [External]
externals =
    [ externC "reify-rules" reifyRules
        "convert some non-local vars to consts"
    , external "reify-rhs"
#ifdef SplitEval
        (promoteR . reifyRhs :: String -> ReCore)
#else
        (promoteR reifyRhs :: ReCore)
#endif
        ["reifyE the RHS of a definition, giving a let-intro name"]
    , externC "reify-def"  reifyDef "reifyE a definition"
    , externC "reify-misc" reifyMisc "Simplify 'reify e'"
    -- For debugging
    , externC "unreify" unReify "Drop reify"
    , externC "reify-inline" reifyInline "inline names where reified"
    , externC "reify-it" reifyR "apply reify"
    , externC "eval-it" evalR "apply eval"
    , externC "reify-let" reifyPolyLet "reify polymorphic let"
    , externC "let-to-redex" monoLetToRedex "monomorphic let to redex"
    , externC "reify-eval" reifyEval "reify eval"
    , externC "reify-tup-case" reifyTupCase "reify case with unit or pair pattern"
    , externC "reify-module" reifyModGuts "reify all top-level definitions"
    , externC "inline-eval" inlineEval "inline to an eval"
    , externC "type-eta-long" typeEtaLong "type-eta-long form"
    , externC "reify-poly-let" reifyPolyLet "reify polymorphic 'let' expression"
    , externC "encode-types" encodeTypesR
       "encode case expressions and constructor applications"
    , externC "re-construct" reConstructR "encode constructor application"
    , externC "re-case" reCaseR "encode case expression"
    ]
