{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.SReify
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Reify a Core expression into GADT
----------------------------------------------------------------------

#define OnlyLifted

module LambdaCCC.SReify (plugin) where

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Data.Foldable (msum)
import Control.Monad ((<=<),unless)
import Control.Arrow (Arrow(..),(>>>),(<<<))
import Data.List (isPrefixOf,find)
import Data.Maybe (fromMaybe)

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Monad (newIdH)
import HERMIT.Core (localFreeIdsExpr,CoreProg(..),bindsToProg,progToBinds)
import HERMIT.External (External,external)
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  hiding (findTyConT, externals)  -- Use our own findTyConT FOR NOW
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import LambdaCCC.Misc ((<~))

import HERMIT.Extras hiding (observeR', triesL, labeled)
import qualified HERMIT.Extras as Ex

-- Drop TypeEncode for now.
-- import TypeEncode.Plugin (encodeOf, reConstructR, reCaseR)
-- import qualified TypeEncode.Plugin as Enc

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = True

-- observeR' :: InCoreTC t => String -> RewriteC t
-- observeR' = Ex.observeR' observing

-- triesL :: InCoreTC t => [(String,RewriteC t)] -> RewriteC t
-- triesL = Ex.triesL observing

labelR :: InCoreTC t => String -> RewriteH t -> RewriteH t
labelR = curry (Ex.labeled observing)

-- TODO: stop uncurrying Ex.labeled

{--------------------------------------------------------------------
    Standard types
--------------------------------------------------------------------}

-- TODO: Parametrize the rest of the module by 'standardTyT'.

-- TODO: Consider how to eliminate Encode as well. Then simplify to
-- standardTy :: Type -> Bool

-- A "standard type" is built up from `Unit`, `Bool`, `Int` (for now), pairs (of
-- standard types), sums, and functions, or Encode

standardTyT :: Type -> TransformU ()
-- standardTyT _ | trace "standardTyT" False = undefined
standardTyT (tcView -> Just ty) = standardTyT ty
standardTyT (TyConApp tc args) | standardTC tc
                               = mapM_ standardTyT args
#if 1
standardTyT ty@(TyConApp tc _) =
  -- Treat Encode applications as standard.
  do encodeTC <- findTyConT "LambdaCCC.Encode.Encode"
     if tc == encodeTC then successT else nonStandardFail ty
#endif
standardTyT (FunTy arg res) =
  standardTyT arg >> standardTyT res
standardTyT ty = nonStandardFail ty

nonStandardFail :: Type -> TransformU a
nonStandardFail ty =
  do s <- showPprT <<< return ty
     fail ("non-standard type:\n" ++ s)

standardTC :: TyCon -> Bool
standardTC tc =
     (tc `elem` [unitTyCon, boolTyCon, intTyCon])
  || isPairTC tc
  || tyConName tc == eitherTyConName    -- no eitherTyCon

-- TODO: Maybe I just want a standard outer shell.

-- TODO: Maybe use coreView instead of tcView? I think it's tcView we want,
-- since it just looks through type synonyms and not newtypes.

-- TODO: If I remove Encode, standardTy can be Type -> Bool

standardET :: FilterE
standardET = standardTyT =<< arr exprType

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

lamName :: Unop String
lamName = ("LambdaCCC.Lambda." ++)

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

varPS, varPatS :: String
varPS   = "varP#"
varPatS = "varPat#"

epS :: String
epS = "EP"

-- t ==> EP t
mkEP :: TransformH a Type
mkEP = do epTC <- findTyConE epS
          return (TyConApp epTC [])

-- t ==> EP t
epOf :: Type -> TransformH a Type
epOf t = flip mkAppTy t <$> mkEP

-- epOf t = do epTC <- findTyConE epS
--             return (TyConApp epTC [t])

-- reify u ==> u
unReify :: ReExpr
unReify = unCallE1 reifyS
-- eval e ==> e
unEval :: ReExpr
unEval = unCallE1 evalS

-- reify (eval e) ==> e
reifyEval :: ReExpr
reifyEval = unReify >>> unEval

reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = standardTyT (exprType e) >>
            appsE reifyS [exprType e] [e]
 where
   ty = exprType e
   ki = typeKind ty

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

evalR :: ReExpr
evalR = idR >>= evalOf

isAppT :: FilterE
isAppT = appT successT successT (const id)

{--------------------------------------------------------------------
    Reification rewrites
--------------------------------------------------------------------}

-- reifyApp :: ReExpr
-- reifyApp =
--      -- inReify (labelR "castFloatAppR" castFloatAppR) <+
--   reifyAppSimple
--   -- Do separately, to handle non-apps
--   -- <+ inReify (isAppT >> labelR "unfoldR" unfoldR)

-- reify (u v) ==> reify u `appP` reify v .
-- Fails if v (and hence u) has a nonstandard type.
reifyApp :: ReExpr
reifyApp = labelR "reifyApp" $
           do App u v <- unReify
              Just (a,b) <- constT (return (splitFunTy_maybe (exprType u)))
              u' <- reifyOf u
              v' <- reifyOf v
              appsE "appP" [b,a] [u', v'] -- note b,a

-- I've forgotten my motivation for reifyRulesPrefix. Omit for now.
#if 0
-- Apply a rule to a left application prefix
reifyRulesPrefix :: ReExpr
reifyRulesPrefix = labelR "reifyRulesPrefix" $
                   reifyRules <+ (reifyApp >>> appArgs reifyRulesPrefix idR)

-- Like appAllR, but on a reified app.
-- 'app ta tb f x ==> 'app ta tb (rf f) (rx s)'
appArgs :: Binop ReExpr
appArgs rf rx = appAllR (appAllR idR rf) rx
#endif

-- TODO: Use arr instead of (constT (return ...))
-- TODO: refactor so we unReify once and then try variations

varSubst :: [Var] -> TransformU (Unop CoreExpr)
varSubst vs = do vs' <- mapM varEval vs
                 return (subst (vs `zip` vs'))
 where
   varEval :: Var -> TransformU CoreExpr
   varEval v = (evalOf <=< appsE1 varPS [varType v]) (varLitE v)

-- | reify (\ x -> e)  ==>  lamv x' (reify (e[x := eval (var x')]))
reifyLam :: ReExpr
reifyLam = labelR "reifyLam" $
  do Lam v e <- unReify
     guardMsg (not (isTyVar v)) "reifyLam: doesn't handle type lambda"
     sub     <- varSubst [v]
     e'      <- reifyOf (sub e)
     appsE "lamvP#" [varType v, exprType e] [varLitE v,e']

reifyPolyLet :: ReExpr
reifyPolyLet = labelR "reifyPolyLet" $
  unReify >>>
  do Let (NonRec (isForAllTy . varType -> True) _) _ <- idR
     letAllR reifyDef reifyR >>> letFloatLetR

-- reifyDef introduces foo_reified binding, which the letFloatLetR then moves up
-- one level. Typically (always?) the "foo = eval foo_reified" definition gets
-- inlined and then eliminated by the letElimR in reifyMisc.

-- | Turn a monomorphic let into a beta-redex.
reifyMonoLet :: ReExpr
reifyMonoLet = labelR "reifyMonoLet" $
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
reifyLetSubst = labelR "reifyLetSubst" $
                inReify letSubstR

-- TODO: Perhaps combine reifyPolyLet and reifyMonoLet into reifyLet

#define SplitEval

#ifdef SplitEval

-- (\ vs -> e) ==> (\ vs -> eval (reify e)) in preparation for rewriting reify e.
-- For vs, take all leading type variables.
-- Fail if e is already an eval or if it has IO or EP type.
reifyRhs :: String -> ReExpr
reifyRhs nm = labelR ("reifyRhs " ++ nm) $
  standardET >>
  ( typeEtaLong >>>
    do (tvs,body) <- collectTyBinders <$> idR
       eTy        <- epOf (exprType body)
       v          <- constT $ newIdH (nm ++ "_reified") (mkForAllTys tvs eTy)
       reified    <- mkLams tvs <$> reifyOf body
       evald      <- evalOf (mkCoreApps (Var v) ((Type . TyVarTy) <$> tvs))
       return $
         Let (NonRec v reified) (mkLams tvs evald) )


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

-- e ==> eval (reify e) in preparation for rewriting reify e.
-- Fail if e is already an eval or if it has IO or EP type.
-- If there are any type lambdas, skip over them.
reifyRhs :: ReExpr
reifyRhs = labelR "reifyRhs" $
           inTyLams $
             unlessDict >>> unlessEval >>> unlessTC "IO" >>> unlessTC epS >>>
             reifyR >>> evalR

reifyDef :: RewriteH CoreBind
reifyDef = nonRecAllR idR reifyRhs

reifyProg :: RewriteH CoreProg
reifyProg = progBindsAnyR (const reifyDef)

#endif

reifyModGuts :: RewriteH ModGuts
reifyModGuts = modGutsR reifyProg

-- Rewrite inside of reify applications
inReify :: Unop ReExpr
inReify = reifyR <~ unReify

-- TODO: drop the non-E test, since we're already under a reify.

isWrapper :: Var -> Bool
isWrapper = ("$W" `isPrefixOf`) . uqVarName -- TODO: alternative?

reifyUnfold :: ReExpr
#if 1
reifyUnfold = labelR "reifyUnfold" $
              inReify unfoldR

#else
reifyUnfold = labelR "reifyUnfold" $
              inReify unfoldSimplify

unfoldSimplify :: ReExpr
unfoldSimplify = unfoldPredR (const . not . bad) >>> tryR simplifyE
 where
   bad v = isWrapper v -- || dictRelated (varType v)
#endif

#if 0
-- Now handled by reifyRs
castFloatAppsR :: ReExpr
castFloatAppsR = labelR "castFloatAppsR" $
                 go
 where
   go = castFloatAppR <+ (appAllR go idR >>> castFloatAppR)
#endif

-- reifyEncode :: ReExpr
-- reifyEncode = inReify encodeTypesR

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
reifyRules = labelR "reifyRules" $
             rulesR reifyRuleNames >>> cleanupUnfoldR

-- reify (I# n) ==> intL (I# n)
reifyIntLit :: ReExpr
reifyIntLit = labelR "reifyIntLit" $
  unReify >>> do _ <- callNameT "I#"
                 e <- idR
                 appsE "intL" [] [e]

reifySimplifiable :: ReExpr
reifySimplifiable = labelR "reifySimplifiable" $
                    inReify simplifyE' -- (extractR bashR)
 where
   simplifyE' = repeatR $
                simplifyE <+ anybuE (caseFloatAppR <+ caseFloatCaseR)

-- Sadly, don't use bashR. It gives false positives (succeeding without change),
-- *and* it leads to lint errors and even to non-terminating exprType (or
-- close).

#ifndef OnlyLifted

reifyDecodeF :: ReExpr
reifyDecodeF = labelR "reifyDecodeF" $
               unReify >>>
               do -- (_,[Type a,Type b]) <- callNameT "TypeDecode.Encode.decodeF"
                  (Var f,[Type a,Type b]) <- callT
                  guardMsg (uqVarName f == "decodeF") "oops -- not decodeF"
                  apps' "Circat.Prim.DecodeP" [a,b] [] >>= appsE1 "kPrimEP" [FunTy a b]

reifyEncodeF :: ReExpr
reifyEncodeF = labelR "reifyEncodeF" $
               unReify >>>
               do -- (_,[Type a,Type b]) <- callNameT "TypeDecode.Encode.encodeF"
                  (Var f,[Type a,Type b]) <- callT
                  guardMsg (uqVarName f == "encodeF") "oops -- not encodeF"
                  apps' "Circat.Prim.EncodeP" [a,b] [] >>= appsE1 "kPrimEP" [FunTy a b]

reifyCodeF :: ReExpr
reifyCodeF = reifyEncodeF <+ reifyDecodeF

-- TODO: refactor

#endif

reifyCast :: ReExpr

-- reifyCast = labelR "reifyCast" $
--             unReify >>>
--             do e'@(Cast e co) <- idR
--                re <- reifyOf e
--                appsE "castEP" [exprType e,exprType e'] [Coercion co,re]

reifyCast = labelR "reifyCast" $
            unReify >>>
            do e'@(Cast e co) <- idR
               case setNominalRole_maybe co of
                 Nothing  -> fail "Couldn't setNominalRole"
                 Just coN ->
                   do re <- reifyOf e
                      appsE "castEP" [exprType e,exprType e'] [mkEqBox coN,re]

-- -- Cheat via UnivCo:
-- reifyCast = labelR "reifyCast" $
--             unReify >>>
--             do e'@(Cast e _) <- idR
--                let ty  = exprType e
--                    ty' = exprType e'
--                re <- reifyOf e
--                appsE "castEP" [ty,ty'] [mkEqBox (mkUnivCo Nominal ty ty'),re]

-- reifyCast = labelR "reifyCast" $
--             (unReify &&& arr exprType) >>>
--             do (Cast e _, ty) <- idR
--                re <- reifyOf e
--                apps' "Unsafe.Coerce.unsafeCoerce" [exprType re,ty] [re]

-- -- Equivalent but a bit prettier:
-- reifyCast = labelR "reifyCast" $
--             unReify >>>
--             do e'@(Cast e _) <- idR
--                re <- reifyOf e
--                appsE "castEP'" [exprType e,exprType e'] [re]

reifyCast' :: ReExpr
reifyCast' = inReify (catchesM castRs) <+ reifyCast
 where
   castRs =
     [ labelR "castElimReflR" castElimReflR
     , labelR "castElimSymR"  castElimSymR
     , labelR "castCastR"     castCastR
     , labelR "lamFloatCastR" lamFloatCastR
     ]

#if 0

-- Given reifyEP (m d), if m is a variable and d is a dictionary,
-- then anytdR inline >>> simplify.
reifyMethod :: ReExpr
reifyMethod = labelR "reifyMethod" $
              inReify inlineMethod

inlineMethod :: ReExpr
inlineMethod = labelR "inlineMethod" $
               do (Var _, _,[d]) <- callSplitT
                  guardMsg (isDictTy (exprType d)) "non-dictionary"
                  anytdE inlineR >>> simplifyE

-- TODO: Replace reifyMethod by inlineDict below.

dictRelated :: Type -> Bool
dictRelated ty = any isDictTy (ran:doms)
 where
   (doms,ran) = splitFunTys (dropForAlls ty)

-- | Inline dictionary maker or consumer
inlineDict :: ReExpr
inlineDict = labelR "inlineDict" $
             inlineMatchingPredR (dictRelated . varType)

inlineWrapper :: ReExpr
inlineWrapper = labelR "inlineWrapper" $
                inlineMatchingPredR isWrapper

#endif

-- Note: Given reify (m d a .. z), reifyApp whittles down to reify (m d).

-- TODO: Fix reifyMethod to work even when type arguments come after the
-- dictionary. I didn't think it could happen, but it does with fmap on
-- size-typed vectors. I think I want inlining *only* for the method and
-- dictionary, unlike what I'm doing above.
-- 
-- Idea: inline any variable whose type consumes or produces a dictionary.

-- reify of case on 0-tuple or 2-tuple
reifyTupCase :: ReExpr
reifyTupCase = labelR "reifyTupCase" $
  do Case scrut@(exprType -> scrutT) wild bodyT [alt] <- unReify
     (patE,rhs) <- reifyAlt wild alt
     scrut'     <- reifyOf scrut
     appsE "lettP" [scrutT,bodyT] [patE,scrut',rhs]
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
reifyUnfoldScrut = labelR "reifyUnfoldScrut" $
                   inReify $
                     caseAllR unfoldR idR idR (const idR)

reifyEither :: ReExpr

#if 1

reifyEither = labelR "reifyEither" $
  unReify >>>
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

-- reify (case scrut of { Left lv -> le ; Right rv -> re })  ==> 
-- appE (eitherE (reify (\ lv -> le)) (reify (\ rv -> re))) (reify scrut)

-- Now removed in the type-encode plugin

reifyEither = labelR "reifyEither" $
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

reifyCase :: ReExpr
reifyCase =  inReify (labelR "caseReduceR" (caseReduceR True))
          <+ reifyCaseWild
          <+ reifyEither
          <+ reifyTupCase
          <+ onScrut unfoldR -- and simplify?

-- | reify (case scrut of wild t { _ -> body })
--    ==> reify (let wild = scrut in body)
-- May be followed by let-elimination.
-- Note: does not capture GHC's intent to reduce scrut to WHNF.
reifyCaseWild :: ReExpr
reifyCaseWild = labelR "reifyCaseWild" $
  inReify $
    do Case scrut wild _bodyTy [(DEFAULT,[],body)] <- idR
       return $ Let (NonRec wild scrut) body

-- reifyConstruct :: ReExpr
-- reifyConstruct = inReify reConstructR

-- reifyCase :: ReExpr
-- reifyCase = inReify reCaseR

data NatTy = VZero | VSucc Type

sizedTy :: Type -> TransformU (TyCon, NatTy,Type)
sizedTy (TyConApp tc [len0,elemTy]) =
  do z <- findTyConT "TypeUnary.TyNat.Z"
     s <- findTyConT "TypeUnary.TyNat.S"
     return $
       ( tc
       , case fromMaybe len0 (tcView len0) of
           TyConApp ((== z) -> True) []  -> VZero
           TyConApp ((== s) -> True) [n] -> VSucc n
           _ -> error "sizedTy: Vec not Z or S n. Investigate."
       , elemTy )
sizedTy _ = fail "sizedTy: wrong # args"


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

-- | reify a case of a known-size structure
reifyCaseSized :: ReExpr
reifyCaseSized = labelR "reifyCaseSized" $
  inReify $
    onScrut (do ty  <- exprType <$> idR
                idF <- (vecId ty <+ treeId ty <+ pairId ty)
                arr (App idF) >>> unfoldR )
    >>> tryR (caseFloatCaseR >>> onRhs (caseReduceUnfoldR True))

-- Temporary workaround. Remove when I get the reifyEP/(:<) rule working on
-- unwrapped (:<).
reifyVecS :: ReExpr
reifyVecS = labelR "reifyVecS" $
  unReify >>>
  do (Var f,[_sn,Type a,Type n,_co]) <- callT
     guardMsg (uqVarName f == ":<") "Not a (:<)"
     appsE "vecSEP" [n,a] []

-- reifyVecS = labelR "reifyVecS" $
--             unReify >>> unCallE ":<" >>>
--             do [_sn,Type a,Type n,_co] <- idR
--                appsE "vecSEP" [n,a] []
-- 
-- "callNameT failed: not a call to 'LambdaCCC.Lambda.:<."
-- Why? Wrappers.

reifyLeaf :: ReExpr
reifyLeaf = labelR "reifyLeaf" $
            unReify >>>
            do (Var f,[_sn,Type a,_co]) <- callT
               guardMsg (uqVarName f == "L") "Not an L"
               appsE "treeZEP" [a] []

reifyBranch :: ReExpr
reifyBranch = labelR "reifyBranch" $
              unReify >>>
              do (Var f,[_sn,Type a,Type n,_co]) <- callT
                 guardMsg (uqVarName f == "B") "Not a B"
                 appsE "treeSEP" [n,a] []

-- TODO: refactor or eliminate

reifyMisc :: ReExpr
reifyMisc = catchesM reifyRs

reifyRs :: [ReExpr]
reifyRs =
     [ -- reifyRulesPrefix -- subsumes reifyRules
       reifyRules     -- before App
     , reifyEval      -- ''
     , reifyEither    -- ''
  -- , reifyConstruct -- ''
  -- , reifyMethod    -- ''
     , reifyApp
     , reifyCast'
     , reifyCase
     , reifyLam
     , reifyIntLit
#if 0
  -- , inlineMethod
     , labelR "inReify etaReduceR" (inReify etaReduceR)
     , reifyMonoLet
     , reifyLetSubst
     , reifyPolyLet
     , reifyCaseSized
     , reifyVecS        -- TEMP workaround
     , reifyLeaf        -- TEMP workaround
     , reifyBranch      -- TEMP workaround
     , reifyUnfoldScrut
--      , labelR "inReify castFloatAppsR" (inReify castFloatAppsR)
     , reifySimplifiable
#endif
     , reifyUnfold
     -- Non-reify rules
     , labelR "castFloatAppR" castFloatAppR
     ]

-- Note: letElim is handy with reifyPolyLet to eliminate the "foo = eval
-- foo_reified", which is usually inaccessible.

-- reifyBash :: ReExpr
-- reifyBash = bashExtendedWithE reifyRs

reifyBash :: ReCore
reifyBash = bashExtendedWithR (promoteR <$> reifyRs)

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "reify-rules" reifyRules
        "convert some non-local vars to consts"
--     , externC "reify-rules-prefix"  reifyRulesPrefix
--          "reify-rules on an application prefix"
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
    , externC "reify-it" reifyR "apply reify"
    , externC "eval-it" evalR "apply eval"
    , externC "reify-app" reifyApp "reify (u v) ==> reify u `appP` reify v"
    , externC "reify-lam" reifyLam
        "reify (\\ x -> e) ==> lamv x' (reify (e[x := eval (var x')]))"
    , externC "reify-mono-let" reifyMonoLet "reify monomorphic let"
    , externC "reify-poly-let" reifyPolyLet "reify polymorphic let"
    , externC "reify-case-wild" reifyCaseWild "reify a evaluation-only case"
--     , externC "reify-construct" reifyConstruct "re-construct under reify"
--     , externC "reify-case" reifyCase "re-case under reify"
--     , externC "reify-method" reifyMethod "reify of a method application"
--     , externC "inline-method" inlineMethod "inline method application"
    , externC "reify-cast'" reifyCast' "transform or reify a cast"
--     , externC "reify-cast-float-apps" (inReify castFloatAppsR)
--         "reify while floating casts"
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
--     , externC "inline-dict" inlineDict "inline a dictionary-related var"
--     , externC "inline-wrapper" inlineWrapper "inline a datacon wrapper"
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
--     , externC "cast-float-apps" castFloatAppsR "float casts over apps"
    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    , externC "reify-bash" reifyBash "reify & bash"
    ]
    -- ++ Enc.externals
