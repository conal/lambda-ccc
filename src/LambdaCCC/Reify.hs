{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, TupleSections, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

#define OnlyLifted

module LambdaCCC.Reify
  ( plugin
  , caseSizedR, unCallE1
  ) where

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Data.Foldable (msum)
import Control.Monad ((<=<))
import Control.Arrow (Arrow(..),(>>>))
import Data.List (isPrefixOf,find)
import Data.Maybe (fromMaybe)

import HERMIT.Name (newIdH)
import HERMIT.Core (localFreeIdsExpr,CoreProg(..),bindsToProg,progToBinds)
import HERMIT.External (External,external)
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( findIdT, observeR, callT, callNameT
  , rulesR,inlineR,inlineMatchingPredR, simplifyR,letFloatLetR,letFloatTopR,letElimR
  , betaReduceR, etaReduceR, letNonRecSubstSafeR
  , unfoldR, unfoldPredR, cleanupUnfoldR
  , caseReduceUnfoldR, caseFloatCaseR, caseFloatAppR, letSubstR
  , castFloatAppR, bashR,bashExtendedWithR
  -- , unshadowR   -- May need this one later
  )
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import LambdaCCC.Misc ((<~))

import HERMIT.Extras
  ( Unop, Binop, apps', callSplitT, callNameSplitT, unCall, unCall1
  , ReExpr ,ReCore, TransformU, findTyConT
  , setNominalRole_maybe
#ifdef OnlyLifted
  , liftedKind, unliftedKind
#endif
  , collectForalls, subst, isTyLam
  , InCoreTC
  , tries
  , varLitE, uqVarName, typeEtaLong, simplifyE
  , anytdE, anybuE, inAppTys, isAppTy, letFloatToProg , concatProgs
  , rejectR , rejectTypeR
  , simplifyExprR, showPprT, externC
  )
import qualified HERMIT.Extras as Ex -- (Observing, observeR', triesL, labeled)

-- Drop TypeEncode for now.
-- import TypeEncode.Plugin (encodeOf, reConstructR, reCaseR)
-- import qualified TypeEncode.Plugin as Enc

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False

observeR' :: InCoreTC t => String -> RewriteH t
observeR' = Ex.observeR' observing

triesL :: InCoreTC t => [(String,RewriteH t)] -> RewriteH t
triesL = Ex.triesL observing

-- labeled :: InCoreTC t => (String, RewriteH t) -> RewriteH t
-- labeled = Ex.labeled observing

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

lamName :: Unop String
lamName = ("LambdaCCC.Lambda." ++)

-- findIdE :: String -> TransformH a Id
-- findIdE = findIdT . lamName

findTyConE :: String -> TransformH a TyCon
findTyConE = findTyConT . lamName

appsE :: String -> [Type] -> [CoreExpr] -> TransformU CoreExpr
appsE = apps' . lamName

-- -- | Uncall a named function
-- unCallE :: String -> TransformH CoreExpr [CoreExpr]
-- unCallE = unCall . lamName

-- | Uncall a named function
unCallE1 :: String -> ReExpr
unCallE1 = unCall1 . lamName

-- A handy form for composition via <=<
appsE1 :: String -> [Type] -> CoreExpr -> TransformU CoreExpr
appsE1 str ts e = appsE str ts [e]

-- callNameLam :: String -> TransformH CoreExpr (CoreExpr, [CoreExpr])
-- callNameLam = callNameT . lamName

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
mkEP :: TransformH a Type
mkEP = do epTC <- findTyConE epS
          return (TyConApp epTC [])

-- t --> EP t
epOf :: Type -> TransformH a Type
epOf t = flip mkAppTy t <$> mkEP

-- epOf t = do epTC <- findTyConE epS
--             return (TyConApp epTC [t])

-- reify u --> u
unReify :: ReExpr
unReify = unCallE1 reifyS
-- eval e --> e
unEval :: ReExpr
unEval = unCallE1 evalS

-- reify (eval e) --> e
reifyEval :: ReExpr
reifyEval = unReify >>> unEval

#ifdef OnlyLifted

reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = do guardMsg (not (unliftedKind ki))
                 "reifyOf: no unlifted values (with type of kind #)"
               guardMsg (liftedKind ki)
                 ("reifyOf: Can only reify lifted values, but this one is "
                  ++ kindStr ki)
               guardMsg (not (dictRelated (exprType e)))
                 "reify: dictionary-related"
               appsE reifyS [exprType e] [e]
 where
   ty = exprType e
   ki = typeKind ty


kindStr :: Kind -> String
kindStr (TyConApp tc _) = "TyConApp " ++ uqName (tyConName tc) ++ "..."
kindStr _               = "not a TyConApp" -- TODO: more detail here if needed

#else

reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = appsE reifyS [exprType e] [e]

#endif

evalOf :: CoreExpr -> TransformU CoreExpr
evalOf e = appsE evalS [dropEP (exprType e)] [e]

isEP :: Type -> Bool
isEP (TyConApp (tyConName -> name) [_]) = uqName name == epS
isEP _                                  = False

dropEP :: Unop Type
dropEP (TyConApp (uqName . tyConName -> name) [t]) =
  if name == epS then t
  else error ("dropEP: not an EP: " ++ show name)
dropEP _ = error "dropEP: not a TyConApp"

reifyR :: ReExpr
reifyR = idR >>= reifyOf

#ifdef OnlyLifted
reifyR' :: ReExpr
reifyR' = idR >>= reifyOf'

reifyOf' :: CoreExpr -> TransformU CoreExpr
reifyOf' e = do 
                guardMsg (not (unliftedKind ki))
                  "reifyOf: no unlifted values (with type of kind #)"
--                 guardMsg (liftedKind ki)
--                   ("reifyOf: Can only reify lifted values, but this one is "
--                    ++ kindStr ki)
--                 guardMsg (not (dictRelated (exprType e)))
--                   "reify: dictionary-related"
                appsE reifyS [exprType e] [e]
 where
   ty = exprType e
   ki = typeKind ty
#endif

evalR :: ReExpr
evalR = idR >>= evalOf

-- reify (u v) --> reify u `appP` reify v
reifyApp :: ReExpr
reifyApp = do App u v <- unReify
              Just (a,b) <- constT (return (splitFunTy_maybe (exprType u)))
              u' <- reifyOf u
              v' <- reifyOf v
              appsE "appP" [b,a] [u', v'] -- note b,a

-- Apply a rule to a left application prefix
reifyRulesPrefix :: ReExpr
reifyRulesPrefix = reifyRules <+ (reifyApp >>> appArgs reifyRulesPrefix idR)

-- Like appAllR, but on a reified app.
-- 'app ta tb f x --> 'app ta tb (rf f) (rx s)'
appArgs :: Binop ReExpr
appArgs rf rx = appAllR (appAllR idR rf) rx


-- reifyApps =
--   unReify >>> callSplitT >>> arr (\ (f,ts,es) -> ((f,ts),es)) >>> reifyCall

-- reifyCall :: TransformH ((CoreExpr,[Type]), [CoreExpr]) CoreExpr
-- reifyCall = reifyR 

-- TODO: Use arr instead of (constT (return ...))
-- TODO: refactor so we unReify once and then try variations

varEval :: Var -> TransformU CoreExpr
varEval v = (evalOf <=< appsE1 varPS [varType v]) (varLitE v)

varSubst :: [Var] -> TransformU (Unop CoreExpr)
varSubst vs = do vs' <- mapM varEval vs
                 return (subst (vs `zip` vs'))

-- | reify (\ x -> e)  -->  lamv x' (reify (e[x := eval (var x')]))
reifyLam :: ReExpr
reifyLam = do Lam v e <- unReify
              guardMsg (not (isTyVar v)) "reifyLam: doesn't handle type lambda"
              sub     <- varSubst [v]
              e'      <- reifyOf (sub e)
              appsE "lamvP#" [varType v, exprType e] [varLitE v,e']

-- Pass through unless an IO
unlessTC :: String -> ReExpr
unlessTC name = rejectTypeR (hasTC name)

-- Pass through unless a dictionary construction
unlessDict :: ReExpr
unlessDict = rejectTypeR (dictRelated . dropForAlls)
-- unlessDict = rejectTypeR (isDictTy . snd . splitFunTys . dropForAlls)

-- Pass through unless an eval application
unlessEval :: ReExpr
unlessEval = rejectR isEval

-- TODO: rename "unless" to "reject"

hasTC :: String -> Type -> Bool
hasTC name (TyConApp tc [_]) = uqName (tyConName tc) == name
hasTC _ _                    = False

isEval :: CoreExpr -> Bool
isEval (App (App (Var v) (Type _)) _) = uqVarName v == evalS
isEval _                              = False

reifyPolyLet :: ReExpr
reifyPolyLet = unReify >>>
               do Let (NonRec (isForAllTy . varType -> True) _) _ <- idR
                  letAllR reifyDef reifyR >>> letFloatLetR

-- reifyDef introduces foo_reified binding, which the letFloatLetR then moves up
-- one level. Typically (always?) the "foo = eval foo_reified" definition gets
-- inlined and then eliminated by the letElimR in reifyMisc.

-- | Turn a monomorphic let into a beta-redex.
reifyMonoLet :: ReExpr
reifyMonoLet =
    unReify >>>
    do Let (NonRec v@(isForAllTy . varType -> False) rhs) body <- idR
       guardMsgM (worthLet rhs) "trivial let"
       rhsE  <- reifyOf rhs
       sub   <- varSubst [v]
       bodyE <- reifyOf (sub body)
       appsE "letvP#" [varType v, exprType body] [varLitE v, rhsE,bodyE]

-- Placeholder
worthLet :: CoreExpr -> TransformU Bool
worthLet _ = return True

-- Simpler but can lead to loops. Maybe fix by following with reifyLam.
-- 
-- reifyMonoLet =
--   inReify $
--     do Let (NonRec v@(isForAllTy . varType -> False) rhs) body <- idR
--        return (Lam v body `App` rhs)

reifyLetSubst :: ReExpr
reifyLetSubst = inReify letSubstR

-- TODO: Perhaps combine reifyPolyLet and reifyMonoLet into reifyLet

#define SplitEval

#ifdef SplitEval

-- (\ vs -> e) --> (\ vs -> eval (reify e)) in preparation for rewriting reify e.
-- For vs, take all leading type variables.
-- Fail if e is already an eval or if it has IO or EP type.
reifyRhs :: String -> ReExpr
reifyRhs nm =
  unlessDict >>> unlessTC "IO" >>> unlessTC epS >>> unlessEval >>>
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
             unlessDict >>> unlessEval >>> unlessTC "IO" >>> unlessTC epS >>>
             reifyR >>> evalR

reifyDef :: RewriteH CoreBind
reifyDef = nonRecAllR idR reifyRhs

reifyProg :: RewriteH CoreProg
reifyProg = progBindsAnyR (const reifyDef)

#endif

reifyModGuts :: RewriteH ModGuts
reifyModGuts = modGutsR reifyProg

inlineR' :: ReExpr
inlineR' = do Var nm <- idR
              _ <- observeR' ("inline " ++ uqVarName nm)
              inlineR

-- Inline if not of type EP t
inlineNonE :: ReExpr
inlineNonE = rejectTypeR isEP >>>
             inAppTys inlineR' -- >>> tryR simplifyE

-- The simplifyE is for beta-reducing type applications.

-- Rewrite inside of reify applications
inReify :: Unop ReExpr
inReify = reifyR <~ unReify

reifyInline :: ReExpr
reifyInline = inReify inlineNonE
-- reifyInline = inReify inlineEval

-- TODO: drop the non-E test, since we're already under a reify.

isWrapper :: Var -> Bool
isWrapper = ("$W" `isPrefixOf`) . uqVarName -- TODO: alternative?

unfoldSimplify :: ReExpr
unfoldSimplify = unfoldPredR (const . not . bad) >>> cleanupUnfoldR
 where
   bad v = isWrapper v -- || dictRelated (varType v)

-- unfoldSimplify = unfoldR >>> tryR postUnfold

-- unfoldSimplify = unfoldPredR (const . not . isWrapper) >>> tryR postUnfold

-- bashE :: ReExpr
-- bashE = extractR simplifyR -- bashR

#if 0

postUnfold :: ReExpr
postUnfold = curry labeled "post-unfold" $
             extractR (bashExtendedWithR (promoteR <$> simplifies))

-- | Simplifications to apply at the start and to the result of each unfolding
ourSimplifies :: [ReExpr]
ourSimplifies = map labeled
             [ ("inline-dict"   , inlineDict)
             -- , ("inline-wrapper", inlineWrapper)  -- breaks rewrite rules
             ]

-- | Simplifications to apply at the start and to the result of each unfolding
simplifies :: [ReExpr]
simplifies = map labeled
             [ ("let-elim"          , letElimR)       -- Note
             , ("case-reduce-unfold", caseReduceUnfoldR True)
             , ("cast-float-app"    , castFloatAppR)
          -- , ("type-beta-reduce"  , typeBetaReduceR)  -- was looping, I think
             ] ++ ourSimplifies

#endif

reifyUnfold :: ReExpr
reifyUnfold = inReify unfoldSimplify

-- reifyEncode :: ReExpr
-- reifyEncode = inReify encodeTypesR

castFloatAppsR :: ReExpr
castFloatAppsR = go
 where
   go = castFloatAppR <+ (appAllR go idR >>> castFloatAppR)

reifyRuleNames :: [String]
reifyRuleNames = map ("reify/" ++)
  [ "not","(&&)","(||)","xor","(+)","(*)","exl","exr","pair","inl","inr"
  , "if","()","false","true"
  , "toVecZ","unVecZ","toVecS","unVecS"
  , "ZVec","(:<)","(:#)","L","B","unPair","unLeaf","unBranch"
  , "square"
  ]

-- ,"if-bool","if-pair"

-- or: words "not (&&) (||) xor ..."

-- TODO: Is there a way not to redundantly specify this rule list?
-- Yes -- trust GHC to apply the rules later.
-- Keep for now, to help us see that whether reify applications vanish.

reifyRules :: ReExpr
reifyRules = rulesR reifyRuleNames >>> cleanupUnfoldR

-- reifyRules = (rulesR reifyRuleNames >>> tryR simplifyE)
-- #ifndef OnlyLifted
--              <+ reifyCodeF
-- #endif

-- reifyRules = rulesR reifyRuleNames >>> tryR (extractR tidy)
--  where
--    tidy :: ReCore
--    tidy = anybuR (promoteR (betaReduceR >>> letNonRecSubstSafeR))

-- -- eval e |> co  -->  eval (e |> co').
-- -- Since `eval :: E p a -> a` and `co :: a ~ b`, `co' :: E p a ~ E p b`.
-- evalCast :: ReExpr
-- evalCast = (do ep <- mkEP
--                castAllR unEval (arr (mkAppCo (mkSubCo (Refl Nominal ep))))) >>>
--            evalR              

-- reify (I# n) --> intL (I# n)
reifyIntLit :: ReExpr
reifyIntLit = unReify >>> do _ <- callNameT "I#"
                             e <- idR
                             appsE "intL" [] [e]

reifySimplifiable :: ReExpr
reifySimplifiable = inReify simplifyE' -- (extractR bashR)
 where
   simplifyE' = repeatR $
                simplifyE <+ anybuE (caseFloatAppR <+ caseFloatCaseR)

-- Sadly, don't use bashR. It gives false positives (succeeding without change),
-- *and* it leads to lint errors and even to non-terminating exprType (or
-- close).

#ifndef OnlyLifted

reifyDecodeF :: ReExpr
reifyDecodeF = unReify >>>
               do -- (_,[Type a,Type b]) <- callNameT "TypeDecode.Encode.decodeF"
                  (Var f,[Type a,Type b]) <- callT
                  guardMsg (uqVarName f == "decodeF") "oops -- not decodeF"
                  apps' "LambdaCCC.Prim.DecodeP" [a,b] [] >>= appsE1 "kPrimEP" [FunTy a b]

reifyEncodeF :: ReExpr
reifyEncodeF = unReify >>>
               do -- (_,[Type a,Type b]) <- callNameT "TypeDecode.Encode.encodeF"
                  (Var f,[Type a,Type b]) <- callT
                  guardMsg (uqVarName f == "encodeF") "oops -- not encodeF"
                  apps' "LambdaCCC.Prim.EncodeP" [a,b] [] >>= appsE1 "kPrimEP" [FunTy a b]

reifyCodeF :: ReExpr
reifyCodeF = reifyEncodeF <+ reifyDecodeF

-- TODO: refactor

#endif

#if 1

reifyCast :: ReExpr

-- reifyCast = unReify >>>
--             do e'@(Cast e co) <- idR
--                re <- reifyOf e
--                appsE "castEP" [exprType e,exprType e'] [Coercion co,re]

-- reifyCast = unReify >>>
--             do e'@(Cast e co) <- idR
--                case setNominalRole_maybe co of
--                  Nothing  -> fail "Couldn't setNominalRole"
--                  Just coN ->
--                    do re <- reifyOf e
--                       appsE "castEP" [exprType e,exprType e'] [mkEqBox coN,re]

-- Cheat via UnivCo:
reifyCast = unReify >>>
            do e'@(Cast e _) <- idR
               let ty  = exprType e
                   ty' = exprType e'
               re <- reifyOf e
               appsE "castEP" [ty,ty'] [mkEqBox (mkUnivCo Nominal ty ty'),re]

-- reifyCast = (unReify &&& arr exprType) >>>
--             do (Cast e _, ty) <- idR
--                re <- reifyOf e
--                apps' "Unsafe.Coerce.unsafeCoerce" [exprType re,ty] [re]

-- -- Equivalent but a bit prettier:
-- reifyCast = unReify >>>
--             do e'@(Cast e _) <- idR
--                re <- reifyOf e
--                appsE "castEP'" [exprType e,exprType e'] [re]

#else
-- reify (e |> co)  -->  reify (encode e)
reifyCast :: ReExpr
reifyCast = inReify $
              do e'@(Cast e _) <- idR
                 let ty  = exprType e
                     ty' = exprType e'
                 encodeOf ty ty' e
#endif

-- -- This version cheats by dropping the cast entirely.
-- unCast :: ReExpr
-- unCast = do (Cast e _) <- idR
--             return e

-- Also try UnivCo

-- TODO: rework reifyCast so that we can recognize and and eliminate composed
-- inverses.

-- typeBetaReduceR :: ReExpr
-- typeBetaReduceR = do (isTyLam -> True) `App` _ <- idR
--                      betaReduceR >>> letNonRecSubstSafeR

-- Given reifyEP (m d), if m is a variable and d is a dictionary,
-- then anytdR inline >>> simplify.
reifyMethod :: ReExpr
reifyMethod = inReify inlineMethod

inlineMethod :: ReExpr
inlineMethod = do (Var _, _,[d]) <- callSplitT
                  guardMsg (isDictTy (exprType d)) "non-dictionary"
                  anytdE inlineR >>> simplifyE

-- TODO: Replace reifyMethod by inlineDict below.

dictRelated :: Type -> Bool
dictRelated ty = any isDictTy (ran:doms)
 where
   (doms,ran) = splitFunTys (dropForAlls ty)

-- | Inline dictionary maker or consumer
inlineDict :: ReExpr
inlineDict = inlineMatchingPredR (dictRelated . varType)

inlineWrapper :: ReExpr
inlineWrapper = inlineMatchingPredR isWrapper

-- Note: Given reify (m d a .. z), reifyApp whittles down to reify (m d).

-- TODO: Fix reifyMethod to work even when type arguments come after the
-- dictionary. I didn't think it could happen, but it does with fmap on
-- size-typed vectors. I think I want inlining *only* for the method and
-- dictionary, unlike what I'm doing above.
-- 
-- Idea: inline any variable whose type consumes or produces a dictionary.

-- reify of case on 0-tuple or 2-tuple
reifyTupCase :: ReExpr
reifyTupCase =
  do Case scrut@(exprType -> scrutT) wild bodyT [alt] <- unReify
     (patE,rhs) <- reifyAlt wild alt
     scrut'     <- reifyOf scrut
     appsE letS [scrutT,bodyT] [patE,scrut',rhs]
 where
   -- Reify a case alternative, yielding a reified pattern and a reified
   -- alternative body (RHS). Only unit and pair patterns. Others are
   -- transformed away in the type-encode plugin.
   reifyAlt :: Var -> CoreAlt -> TransformU (CoreExpr,CoreExpr)
   reifyAlt wild (DataAlt ( isTupleTyCon . dataConTyCon -> True)
                             , vars, rhs ) =
     do guardMsg (length vars `elem` [0,2])
          "Only handles unit and pair patterns"
        vPats <- mapM varPatT vars
        sub   <- varSubst (wild : vars)
        pat   <- if null vars then
                   appsE "UnitPat" [] []
                  else
                   appsE ":$" (varType <$> vars) vPats
        pat'  <- if wild `elemVarSet` localFreeIdsExpr rhs
                   then -- WARNING: untested as of 2014-03-11
                     appsE "asPat#" [varType wild] [varLitE wild,pat]
                   else
                     return pat
        rhs'  <- reifyOf (sub rhs)
        return (pat', rhs')
    where
      varPatT :: Var -> TransformU CoreExpr
      varPatT v = appsE varPatS [varType v] [varLitE v]
   reifyAlt _ _ = fail "reifyAlt: Only handles pair patterns so far."

reifyUnfoldScrut :: ReExpr
reifyUnfoldScrut = inReify $
                   caseAllR unfoldR idR idR (const idR)

reifyEither :: ReExpr

#if 1

reifyEither = unReify >>>
              do (_either, tys, funs@[_,_]) <- callNameSplitT "either"
                 funs' <- mapM reifyOf funs
                 appsE "eitherEP" tys funs'

-- Since 'either f g' has a function type, there could be more parameters.
-- I only want two. The others will get removed by reifyApp.

-- Important: reifyEither must come before reifyApp in reifyMisc, so that we can
-- see 'either' applied.

#else

eitherTy :: Type -> Type -> TransformU Type
eitherTy a b = do tc <- findTyConT "Either"
                  return (TyConApp tc [a,b])

unEitherTy :: Type -> TransformU (Type,Type)
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
   reifyBranch :: Var -> CoreAlt -> TransformU CoreExpr
   reifyBranch _wild (DataAlt _, [var], rhs) = reifyOf (Lam var rhs)
   reifyBranch _ _ = error "reifyEither: bad branch"

-- TODO: check for wild in rhs. In that case, I guess I'll have to reify the Lam
-- manually in order to get the as pattern. Hm.

#endif

-- | reify (case scrut of wild t { _ -> body })
--    --> reify (let wild = scrut in body)
-- May be followed by let-elimination.
-- Note: does not capture GHC's intent to reduce scrut to WHNF.
reifyCaseWild :: ReExpr
reifyCaseWild = inReify $
                  do Case scrut wild _bodyTy [(DEFAULT,[],body)] <- idR
                     return $ Let (NonRec wild scrut) body

-- reifyConstruct :: ReExpr
-- reifyConstruct = inReify reConstructR

-- reifyCase :: ReExpr
-- reifyCase = inReify reCaseR

data NatTy = VZero | VSucc Type

typeNat :: Type -> TransformU NatTy
typeNat (tcView -> Just ty) = typeNat ty
typeNat len =
  do z <- findTyConT "TypeUnary.TyNat.Z"
     s <- findTyConT "TypeUnary.TyNat.S"
     case len of
       TyConApp ((== z) -> True) []  -> return VZero
       TyConApp ((== s) -> True) [n] -> return (VSucc n)
       _ -> do str <- return len >>> showPprT
               fail ("typeNat: not Z or S n: " ++ str)

sizedTy :: Type -> TransformU (TyCon, NatTy,Type)
sizedTy (tcView -> Just ty)   = sizedTy ty
sizedTy (TyConApp tc [len,x]) = (tc,,x) <$> typeNat len
sizedTy ty                    = do str <- return ty >>> showPprT
                                   fail ("sizedTy: wrong # args: " ++ str)

-- Find a structural identity function on a unary-sized type, given the names of
-- the type and construction functions for zero and succ size.
sizedId :: (String,String,String) -> Type -> TransformU CoreExpr
sizedId (tcn,z,s) ty =
  do (tc,size,a) <- sizedTy ty
     tcv <- findTyConT tcn
     guardMsg (tc == tcv) ("Not a " ++ tcn)
     case size of
       VZero   -> appsE z [  a] [] 
       VSucc n -> appsE s [n,a] []

-- Find a structural identity function on vectors
vecId :: Type -> TransformU CoreExpr
vecId = sizedId ("TypeUnary.Vec.Vec","idVecZ","idVecS")

-- Find a structural identity function on trees
treeId :: Type -> TransformU CoreExpr
treeId = sizedId ("Circat.RTree.Tree","idTreeZ","idTreeS")

pairId :: Type -> TransformU CoreExpr
pairId (TyConApp tc [a]) = do tcv <- findTyConT "Circat.Pair.Pair"
                              guardMsg (tc == tcv) ("Not a Pair")
                              appsE "idPair" [a] []
pairId _ = fail "pairId: wrong # args"


onScrut :: Unop ReExpr
onScrut r = caseAllR r idR idR (const idR)

onRhs :: ReExpr -> ReExpr
onRhs r = caseAllR idR idR idR (const (altAllR idR (const idR) r))

caseSizedR :: ReExpr
caseSizedR =
  onScrut (do ty  <- exprType <$> idR
              idF <- (vecId ty <+ treeId ty <+ pairId ty)
              arr (App idF) >>> unfoldR )
  >>> tryR (caseFloatCaseR >>> onRhs (caseReduceUnfoldR True))

-- | reify a case of a known-size structure
reifyCaseSized :: ReExpr
reifyCaseSized = inReify caseSizedR

-- Temporary workaround. Remove when I get the reifyEP/(:<) rule working on
-- unwrapped (:<).
reifyVecS :: ReExpr
reifyVecS = unReify >>>
            do (Var f,[_sn,Type a,Type n,_co]) <- callT
               guardMsg (uqVarName f == ":<") "Not a (:<)"
               appsE "vecSEP" [n,a] []

-- reifyVecS = unReify >>> unCallE ":<" >>>
--             do [_sn,Type a,Type n,_co] <- idR
--                appsE "vecSEP" [n,a] []
--
-- "callNameT failed: not a call to 'LambdaCCC.Lambda.:<."
--
-- Why?

reifyLeaf :: ReExpr
reifyLeaf = unReify >>>
            do (Var f,[_sn,Type a,_co]) <- callT
               guardMsg (uqVarName f == "L") "Not an L"
               appsE "treeZEP" [a] []

reifyBranch :: ReExpr
reifyBranch = unReify >>>
              do (Var f,[_sn,Type a,Type n,_co]) <- callT
                 guardMsg (uqVarName f == "B") "Not a B"
                 appsE "treeSEP" [n,a] []

-- TODO: refactor or eliminate

miscL :: [(String,ReExpr)]
miscL = [ ("reifyRulesPrefix" , reifyRulesPrefix) -- subsumes reifyRules, I think
     -- , ("reifyRules"       , reifyRules)     -- before App
        , ("reifyEval"        , reifyEval)      -- ''
        , ("reifyEither"      , reifyEither)    -- ''
        -- , ("reifyConstruct"   , reifyConstruct) -- ''
        -- , ("reifyMethod"      , reifyMethod)    -- ''
        , ("reifyUnfold"      , reifyUnfold)
        -- , ("inlineMethod"     , inlineMethod)
        -- , ("reifyCase"        , reifyCase)
        , ("reifyCaseWild"    , reifyCaseWild)
        , ("reifySimplifiable", reifySimplifiable)
        , ("reifyApp"         , reifyApp)
        , ("reifyEtaReduce"   , inReify etaReduceR)
        , ("reifyLam"         , reifyLam)
        , ("reifyMonoLet"     , reifyMonoLet)
        , ("reifyLetSubst"    , reifyLetSubst)
        , ("reifyPolyLet"     , reifyPolyLet)
        , ("reifyTupCase"     , reifyTupCase)
        , ("reifyCaseSized"   , reifyCaseSized)
        , ("reifyVecS"        , reifyVecS)        -- TEMP workaround
        , ("reifyLeaf"        , reifyLeaf)        -- TEMP workaround
        , ("reifyBranch"      , reifyBranch)      -- TEMP workaround
        , ("reifyUnfoldScrut" , reifyUnfoldScrut)
    --  , ("reifyInline"      , reifyInline)
        , ("reifyCast"        , reifyCast)
        , ("inReify castFloatAppsR" , inReify castFloatAppsR)
        , ("reifyIntLit"      , reifyIntLit)
        ]

reifyMisc :: ReExpr
reifyMisc = triesL miscL

-- Note: letElim is handy with reifyPolyLet to eliminate the "foo = eval
-- foo_reified", which is usually inaccessible.

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "reify-rules" reifyRules
        "convert some non-local vars to consts"
    , externC "reify-rules-prefix"  reifyRulesPrefix
         "reify-rules on an application prefix"
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
#ifdef OnlyLifted
    , externC "reify-it'" reifyR' "reifyR'"
#endif
    , externC "eval-it" evalR "apply eval"
    , externC "reify-app" reifyApp "reify (u v) --> reify u `appP` reify v"
    , externC "reify-lam" reifyLam
        "reify (\\ x -> e) --> lamv x' (reify (e[x := eval (var x')]))"
    , externC "reify-mono-let" reifyMonoLet "reify monomorphic let"
    , externC "reify-poly-let" reifyPolyLet "reify polymorphic let"
    , externC "reify-case-wild" reifyCaseWild "reify a evaluation-only case"
--     , externC "reify-construct" reifyConstruct "re-construct under reify"
--     , externC "reify-case" reifyCase "re-case under reify"
    , externC "reify-method" reifyMethod "reify of a method application"
    , externC "inline-method" inlineMethod "inline method application"
    , externC "reify-cast" reifyCast "reify a cast"
    , externC "reify-cast-float-apps" (inReify castFloatAppsR)
        "reify while floating casts"
    , externC "reify-int-literal" reifyIntLit "reify an Int literal"
    , externC "reify-eval" reifyEval "reify eval"
    , externC "reify-unfold" reifyUnfold "reify an unfoldable"
    , externC "reify-unfold-scrut" reifyUnfoldScrut "reify case with unfoldable scrutinee"
    , externC "reify-case-sized" reifyCaseSized "case with a known-length vector scrutinee"
    , externC "reify-vecs" reifyVecS "Temp workaround"
--     , externC "post-unfold" postUnfold "simplify after unfolding"
    , externC "reify-tup-case" reifyTupCase "reify case with unit or pair pattern"
    , externC "reify-simplifiable" reifySimplifiable "Simplify under reify"
    , externC "reify-module" reifyModGuts "reify all top-level definitions"
    , externC "inline-dict" inlineDict "inline a dictionary-related var"
    , externC "inline-wrapper" inlineWrapper "inline a datacon wrapper"
    , externC "type-eta-long" typeEtaLong "type-eta-long form"
    , externC "reify-poly-let" reifyPolyLet "reify polymorphic 'let' expression"
--    , externC "re-simplify" reSimplify "simplifications to complement reification"
--     , externC "reify-encode" reifyEncode "type-encode under reify"
--     , externC "encode-types" encodeTypesR
--        "encode case expressions and constructor applications"
#ifndef OnlyLifted
    , externC "reify-code" reifyCodeF "manual rewrites for reifying encodeF & decodeF"
#endif
    , external "uncalle1" (promoteR . unCallE1 :: String -> ReCore) ["uncall a function"]
    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    ]
    -- ++ Enc.externals
