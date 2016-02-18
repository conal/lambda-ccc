{-# LANGUAGE CPP, TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module LambdaCCC.Reify where

import Prelude hiding (id,(.))

import Data.Functor (void)
import Control.Category (Category(..))
import Control.Monad ((<=<),unless)
import Control.Arrow ((>>>),(<<<),arr,(***))
import Data.Maybe (isJust)
import qualified Data.Map as M
import Data.String (fromString)
import Data.List (isPrefixOf)

import GHC.Float () -- experiment. didn't work.

import HERMIT.Context (AddBindings,addLambdaBinding,addBindingGroup,HermitC,HasCoreRules(..))
import HERMIT.Core (Crumb(..),localFreeIdsExpr,substCoreExpr,CoreProg(..),progToBinds,isCoArg,freeVarsExpr,localFreeVarsExpr)
import HERMIT.GHC hiding (mkStringExpr)
import TcType (isDoubleTy)  -- Doesn't seem to be coming in with HERMIT.GHC.
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary hiding (externals,($$))
import HERMIT.Monad (HermitM)
import HERMIT.Name (HermitName,mkQualified,cmpHN2Var)
import HERMIT.External (External)

-- GHC
import TcType (isIntegerTy)
import Kind (isUnliftedTypeKind)
import PrelNames (ioTyConName,eitherTyConName)

import Circat.Misc ((<~))

import HERMIT.Extras hiding (findTyConT,observeR',catchesL,simplifyE)
import qualified HERMIT.Extras as Ex -- (Observing, observeR', catchesL, labeled)

import Monomorph.Stuff (hasRepMethod, caseDefaultR, simplifyE, castFloatR, betaReducePlusSaferR)
import LambdaCCC.Monomorphize (abstReprCase,abstReprCon,isDictConstruction)

{--------------------------------------------------------------------
    Utilities. Move to HERMIT.Extras
--------------------------------------------------------------------}

unshadowE :: ReExpr
unshadowE = extractR unshadowR

-- | Like 'caseFloatAppR' but cascades through applications.
caseFloatAppsR :: ReExpr
caseFloatAppsR = caseFloatAppR . (appAllR caseFloatAppsR id <+ id)

-- TODO: Move more utilities here from the code below

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

pluginModuleNames :: [ModuleName]
pluginModuleNames = mkModuleName <$> ["LambdaCCC.Reify"]

-- It's odd to use LambdaCCC.Reify here, but when I use the plugin module name,
-- our plugin never gets run (for the non-interactive and interactive plugins).
-- I don't think I'm using an expected pathway.

getAllOpts :: (Monad m, HasDynFlags m) => m [(ModuleName,String)]
getAllOpts = pluginModNameOpts <$> getDynFlags

-- Get our plugin options
reifyOpts :: [(ModuleName,String)] -> [String]
reifyOpts allOpts =
  [opt | (nm,opt) <- allOpts, nm `elem` pluginModuleNames]

-- -fplugin-opt=LambdaCCC.Plugin:verbose
-- 
-- TODO: verbosity level. I could perhaps
-- use hermit's -vN flag, but I don't want its current meaning.

getVerboseM :: (Monad m, HasDynFlags m) => m Bool
getVerboseM = ("verbose" `elem`) . reifyOpts <$> getAllOpts

getVerboseT :: (Monad m, HasDynFlags m) => Transform c m a Bool
getVerboseT = constT getVerboseM

-- pprTrace if verbosity flag
pprTraceV :: (Monad m, HasDynFlags m)
          => String -> SDoc -> Transform c m a ()
pprTraceV str doc =
  ifM getVerboseT (pprTrace str doc (return ())) (return ())

-- #define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = do observing <- getVerboseT
                  lintingExprR lab (labeled observing (lab,r)) -- hard error
#else
watchR :: (InCoreTC a, InCoreTC b) => String -> Unop (TransformH a b)
watchR lab r = do observing <- getVerboseT
                  labeled' observing (lab,r)  -- don't lint
#endif

nowatchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
nowatchR _ = id

-- nowatchR = watchR

catchesL :: InCoreTC t => [(String,RewriteH t)] -> RewriteH t
catchesL ps = do observing <- getVerboseT
                 Ex.catchesL observing ps

-- observeR :: ( Injection a LCoreTC, LemmaContext c, ReadBindings c, ReadPath c Crumb
--             , HasHermitMEnv m, HasLemmas m, LiftCoreM m )
--          => String -> Rewrite c m a

observeV :: InCoreTC a => String -> RewriteH a
observeV str = ifM getVerboseT (observeR str) id

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

repName :: String -> HermitName
repName = mkQualified "Circat.Rep"

lamName :: String -> HermitName
lamName = mkQualified "LambdaCCC.Lambda"

-- ifName :: String -> HermitName
-- ifName = mkQualified "Circat.If"

-- findIdE :: String -> TransformH a Id
-- findIdE = findIdT . lamName

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

-- Use an internal name while reifying, so as not to confuse with the reifyEP
-- that kicks the whole thing off.
mkReifyId :: TransformU Id
mkReifyId = findIdT reifyLocalS

reifyLocalS :: HermitName
reifyLocalS = "LambdaCCC...."

-- reify u --> u
unReify :: ReExpr
unReify = unCallE1 reifyS
-- eval e --> e
unEval :: ReExpr
unEval = unCallE1 evalS

-- reify (eval e) --> e
reifyEval :: ReExpr
reifyEval = unEval . unReify

reifyName :: HermitName
reifyName = lamName reifyS

evalName :: HermitName
evalName = lamName evalS

isListTy :: Type -> Bool
isListTy (coreView -> Just ty) = isListTy ty
isListTy (TyConApp (tyConName -> qualifiedName -> "GHC.Types.[]") _) = True
isListTy _ = False

isIO :: Type -> Bool
isIO (coreView -> Just ty) = isIO ty
isIO (TyConApp tc _) = tyConName tc == ioTyConName
isIO _ = False

-- Types we know how to handle
reifiableType :: Type -> Bool
reifiableType (coreView -> Just ty) = reifiableType ty
reifiableType (FunTy dom ran) = reifiableType dom && reifiableType ran
reifiableType ty = not (or (($ ty) <$> bads))
 where
   bads = [ isForAllTy
          , isUnliftedTypeKind . typeKind
          , isPredTy -- isDictTy
          , isIntegerTy
          , isListTy
          , isIO
          , isEP
          ]

checkReifiableType :: Monad m => Type -> Transform c m a ()
checkReifiableType ty = guardMsg (reifiableType ty) "Non-reifiable type."

-- Generate a reify call. Fail on types, coercions, and dictionaries.
reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = do guardMsg (not (isTyCoArg e))           "Type or coercion."
               checkReifiableType (exprType' e)
               apps' reifyName [exprType' e] [e]

evalOf :: CoreExpr -> TransformU CoreExpr
evalOf e = appsE evalS [dropEP (exprType' e)] [e]

isEP :: Type -> Bool
isEP (TyConApp (unqualifiedName . tyConName -> name) [_]) | name == epS = True
isEP _ = False

dropEP :: Unop Type
dropEP (TyConApp (unqualifiedName . tyConName -> name) [t]) =
  if name == epS then t
  else error ("dropEP: not an EP: " ++ show name)
dropEP _ = error "dropEP: not a TyConApp"

wrapReify :: ReExpr
wrapReify = idR >>= reifyOf

-- reify (u v) --> reify u `appP` reify v
reifyApp :: ReExpr
reifyApp = do App u v <- unReify
              Just (a,b) <- constT (return (splitFunTy_maybe (exprType' u)))
              -- guardMsg (not (isDictTy a)) "reifyApp: dictionary argument"
              u' <- reifyOf u
              v' <- reifyOf v
              appsE "appP" [b,a] [u', v'] -- note b,a

-- TODO: Use arr instead of (constT (return ...))
-- TODO: refactor so we unReify once and then try variations

varSubst :: Var -> TransformH a (CoreExpr, Unop CoreExpr)
varSubst v = do suffix <- show <$> constT getUniqueM
                let lit = Lit (mkMachString (uqVarName v ++ suffix))
                ev <- (evalOf <=< appsE1 varPS [varType v]) lit
                return (lit, subst [(v,ev)])

-- | reify (\ x -> e)  -->  lamv x' (reify (e[x := eval (var x')]))
reifyLam :: ReExpr
reifyLam = do Lam v e <- unReify
              guardMsg (not (isTyVar v)) "reifyLam: doesn't handle type lambdas"
              checkReifiableType (idType v)
              (litE,sub) <- varSubst v
              e'         <- reifyOf (sub e)
              appsE "lamvP#" [varType v, exprType' e] [litE,e']

-- TODO: Switch to HOAS.

-- reifyDef introduces foo_reified binding, which the letFloatLetR then moves up
-- one level. Typically (always?) the "foo = eval foo_reified" definition gets
-- inlined and then eliminated by the letElimR in reifyMisc.

letTrivialSubstR :: ReExpr
letTrivialSubstR =
 do Let (NonRec v rhs) body <- id
    if | v `notElemVarSet` freeVarsExpr body -> return body
       | trivial rhs || varOccCount v body <= 1 -> letSubstR
       | otherwise -> -- traceR "reifyTrivialLet failed" >>>
                                                fail "Non-trivial"
 where
   trivial e = exprIsTrivial e || isEval e || isDict e

-- TODO: revisit the single-occurrence criterion, and maybe avoid substituting
-- under lambdas. Hermit has some useful functionality, but take care about what
-- it (and GHC) consider trivial.

-- When rhs = eval (var x), reify will make it var x. We don't introduce eval
-- any other way.

reifyLet :: ReExpr
reifyLet =
  unReify >>>
  do Let (NonRec v rhs) body <- idR
     -- guardMsgM (worthLet rhs) "trivial let"
     checkReifiableType (idType v)
     rhsE  <- reifyOf rhs
     (litE,sub) <- varSubst v
     bodyE <- reifyOf (sub body)
     appsE "letvP#" [varType v, exprType' body] [litE, rhsE,bodyE]

-- | Float a let out of a reify. Try if reifyLet fails.
reifyLetFloat :: ReExpr
reifyLetFloat = guardMsgM (arr isReify) "not a reify call" >> letFloatArgR

-- Placeholder
worthLet :: CoreExpr -> TransformU Bool
worthLet _ = return True

-- Rewrite inside of reify applications
inReify :: Unop ReExpr
inReify = wrapReify <~ unReify

-- TODO: More efficient inReify implementation, re-using the existing reify

reifyIf :: ReExpr
reifyIf =
  unReify >>>
  do (Var (fqVarName -> "LambdaCCC.Lambda.if'"),args@(length -> 2)) <- callT
     (\ f -> mkApps (Var f) args) <$> findIdT (lamName ("ifEP"))

reifyBottom :: ReExpr
reifyBottom =
  do App (Var (fqVarName -> "Circat.Rep.bottom")) (Type ty) <- unReify
     dict <- simpleDict ("Circat.Prim.CircuitBot") $* [ty]
     appsE "bottomEP" [ty] [dict]

-- TODO: Combine reifyBottom with reifyStdMeth?

-- TODO: factor out commonalities between reifyIf and reifyBottom.

-- Translate methods to cat class and prim
stdMeths :: M.Map String (String,String)
stdMeths = M.fromList $ concatMap ops
    [ ( "GHC.Classes","Eq"
      , [("==","EqP"), ("/=","NeP")])
    , ( "GHC.Classes","Ord"
      , [("<","LtP"),(">","GtP"),("<=","LeP"),(">=","GeP")])
    , ( "GHC.Num", "Num"
      , [("negate","NegateP"),("+","AddP"),("-","SubP"),("*","MulP")])
    , ( "GHC.Float", "Floating"
      , [("exp","ExpP"),("cos","CosP"),("sin","SinP")])
    , ( "GHC.Real", "Fractional"
      , [("recip","RecipP"),("/","DivideP")])
    -- FromIntegral has two parameters besides the category,
    -- and so needs special treatment. (This one doesn't work.)
    , ( "GHC.Real", "FromIntegral"
      , [("fromIntegral","FromIP")])
    ]
 where
   op modu cls meth ctor =
     ( modu++"."++meth
     , ("Circat.Prim.Circuit"++cls, "Circat.Prim."++ctor))
   ops (modu,cls,meths) = [op modu cls meth ctor | (meth,ctor) <- meths]

-- Reify standard methods, given type and dictionary argument.
-- We assume only a single type argument.
reifyStdMeth :: ReExpr
reifyStdMeth =
  unReify >>>
  do ty <- exprTypeT
     (Var (fqVarName -> flip M.lookup stdMeths -> Just (cls,prim)), tyArgs, moreArgs) <- callSplitT
     guardMsg (not (any isTypeArg moreArgs))
         "reifyStdMeth: types among moreArgs"
     guardMsg (all (isDictTy . exprType) moreArgs)
         "reifyStdMeth: non-dict argument"
     catDict <- simpleDict (fromString cls) $* tyArgs
     primV <- findIdT (fromString prim)
     appsE1 "kPrimEP" [ty] (App (mkTyApps (Var primV) tyArgs) catDict)

-- Reify an application of 'repr' or 'abst' to its type, dict, and coercion
-- args (four in total), leaving the final expression argument for reifyApp.
reifyRepMeth :: ReExpr
reifyRepMeth =
  unReify >>>
  do (Var v,args@(length -> 4)) <- callT
     guardMsg (isRepMeth (fqVarName v)) "not a HasRep method"
     (\ f -> mkApps (Var f) args) <$> findIdT (lamName (uqVarName v ++ "EP"))

isRepMeth :: String -> Bool
isRepMeth = (`elem` repMethNames) . fromString

repMethNames :: [HermitName]
repMethNames = repName <$> ["repr","abst"]

-- reifyTupCase :: ReExpr
-- reifyTupCase = reifyUnitCase <+ reifyPairCase

-- Do I need to handle unit, or will caseDefaultR do it?

-- | (case scrut of w { (a,b) -> rhs }) --> let { w = scrut; a = fst w; b = snd w } in rhs
pairCaseToLet :: ReExpr
pairCaseToLet =
  do Case scrut w _
       [(DataAlt (isBoxedTupleTyCon . dataConTyCon -> True), [a,b], rhs) ] <- id
     let w' = zapVarOccInfo w
         partArgs = [Type (varType a), Type (varType b), Var w']
         wPart f = (\ v -> mkCoreApps (Var v) partArgs)
                   <$> findIdT (fromString ("Data.Tuple."++f))
     fstW <- wPart "fst"
     sndW <- wPart "snd"
     return $
       mkCoreLets [NonRec w' scrut, NonRec a fstW, NonRec b sndW] rhs

reifyPairCase :: ReExpr
reifyPairCase = inReify pairCaseToLet

reifyPrim :: ReExpr
reifyPrim =
  unReify >>>
  do ty <- exprTypeT
     (Var (fqVarName -> flip M.lookup primMap -> Just nm), tyArgs, [])
       <- callSplitT
     primV <- findIdP nm
     appsE1 "kPrimEP" [ty] (mkApps (Var primV) (Type <$> tyArgs))

reifyLit :: ReExpr
reifyLit =
  unReify >>>
  do ty <- exprTypeT
     guardMsg (isPrimitiveTy ty) "reifyLit: must have primitive type"
     (void callDataConT <+
      do (_,[_],[_dict,{-Lit-} _]) <- callNameSplitT "GHC.Num.fromInteger"
         return ())
     e        <- idR
     hasLitD  <- simpleDict (primName "HasLit") $* [ty]
     appsE "kLit" [ty] [hasLitD,e]

reifyDelay :: ReExpr
reifyDelay =
  unReify >>>
  do (Var (fqVarName -> "Circat.Misc.delay"),[Type ty,s0]) <- callT
     showD     <- simpleDict "GHC.Show.Show" $* [ty]
     genBusesD <- simpleDict "Circat.Circuit.GenBuses" $* [ty]
     primV     <- findIdT "Circat.Prim.DelayP"
     appsE1 "kPrimEP" [ty `FunTy` ty]
       (mkApps (Var primV) [Type ty,genBusesD,showD,s0])

reifyLoop :: ReExpr
reifyLoop =
  unReify >>>
  do (Var (fqVarName -> "Circat.Misc.loop"),tys@[_a,_b,s],[h]) <- callSplitT
     dict <- simpleDict (lamName "CircuitLoopKon") $* [s]
     h'   <- reifyOf h
     appsE "loopEP" tys [dict,h']

callTyDictsT :: Monad m => Transform c m CoreExpr (CoreExpr, [CoreExpr])
callTyDictsT =
  do va@(Var _, args) <- arr collectArgs
     guardMsg (all (\ e -> isTypeArg e || okayDict e) args)
              "Arguments must be types or dictionaries"
     return va
 where
   okayDict = isDict
   -- okayDict = isDictTy . exprType'
   -- okayDict = isDictConstruction

isTyOrDict :: CoreExpr -> Bool
isTyOrDict e = isTypeArg e || isDict e

isReifyRule :: CoreRule -> Bool
isReifyRule = ("reify " `isPrefixOf`) . unpackFS . ru_name

getReifyRules :: TransformH a [CoreRule]
getReifyRules = filter isReifyRule . map snd <$> getHermitRulesT

-- Already reified, so reuse.
reifyReified :: ReExpr
reifyReified =
  -- observeV "reifyReified" >>>
  do e <- id
     guardMsg (isReify e) "Not a reify call"
     (Var reifyId, reifyArgs@[_,reifyArg]) <- return (collectArgs e)
     (Var _, _) <- callTyDictsT $* reifyArg  -- narrow applicability
     rs <- getReifyRules
     -- unless (null rs) $ pprTraceV "reify rules" (ppr rs)
     dflags <- getDynFlags
     maybe (fail "no matching reify rule")
           (\ (rule,newRhs) ->
              do -- pprTrace "reifyReified" (ppr rule $$ ppr newRhs) (return ())
                 return $
                  simpleOptExpr $  -- *
                   mkCoreApps newRhs (drop (ruleArity rule) reifyArgs)
           )
           (lookupRule dflags (inScope e) (const True) reifyId reifyArgs rs)

-- * Experiment for beta-reduction. Effective, but could be expensive.
--   TODO: simple & safe (not cost increasing) beta-reduction just at the outside.

inScope :: CoreExpr -> InScopeEnv
inScope e = (mkInScopeSet (localFreeVarsExpr e),idUnfolding)

-- TODO: Find a way to find relevant rules much much more quickly. For instance,
-- add some context with reify rules indexed by their main argument.
-- Incrementally adjust during module compilation as we new rules.

-- reifyUnfold :: ReExpr
-- reifyUnfold = inReify $
--   do (h@(Var f), args) <- callTyDictsT
--      guardMsg (all isTyOrDict args) "Arguments are not all types or dictionaries"
--      if isJust (isClassOpId_maybe f) then
--        -- For class-ops, 
--        -- | (foo ... dict ty1 ... tyn) --> $foo_meth ty1 ... tyn
--        do (tys,dict:postDict) <- return (break isDict args)
--           reduced <- ((caseReduceR True <+ caseReduceUnfoldR True) . unfoldR) -- *
--                        $* mkCoreApps h (tys ++ [dict])
--           return $ mkCoreApps reduced postDict
--       else
--        tryR (anybuE detickE) . unfoldR    

-- * TODO: more dependable way to drive scrutinee to a constructor, followed by
-- caseReduceR.

-- Unfold under reify.
reifyUnfold :: ReExpr
reifyUnfold = inReify $
  do (h@(Var f), args) <- callTyDictsT
     guardMsg (all isTyOrDict args) "Arguments are not all types or dictionaries"
     if isJust (isClassOpId_maybe f) then
       -- For class-ops, 
       -- | (foo ... dict ty1 ... tyn) --> $foo_meth ty1 ... tyn
       do (tys,dict:postDict) <- return (break isDict args)
          guardMsgM (nonLocal $* dict) "dictionary argument is local"
          reduced <- unfoldR $* mkCoreApps h (tys ++ [dict])
          return $ mkCoreApps reduced postDict
      else
       tryR (anybuE detickE) . unfoldR    

-- The detickE is an experiment for helping with a ghci issue.
-- See journal from 2016-02-05.

nonLocal :: TransformH CoreExpr Bool
nonLocal = (callDataConT >> return True) <+ nonLocal . (simplifyOneStepE <+ unfoldR)
-- TODO: Maybe pare down simplifyOneStepE for use here

-- Dictionary variables often get casts that become vacuous.
-- Look for in a method argument.
argCastSimplify :: ReExpr
argCastSimplify = anyArgR (anybuE (castElimR <+ castCastR))

anyArgR :: Unop ReExpr
anyArgR re = appAnyR (anyArgR re) re

reifySimplify :: ReExpr
reifySimplify = inReify simplifyOneStepE

-- I used to repeatR the simplifyOneStepE, but doing so prevents other reify
-- rules from intervening.

simplifyOneStepE :: ReExpr
simplifyOneStepE = -- watchR "simplifyOneStepE" $
     watchR "etaReduceR" etaReduceR
  <+ watchR "betaReducePlusSaferR" betaReducePlusSaferR  -- to Let
  <+ watchR "letElimR" letElimR
  <+ watchR "letTrivialSubstR" letTrivialSubstR
  <+ watchR "caseReduceR" (caseReduceR False)
  <+ watchR "letFloatCaseR" letFloatCaseR
  <+ watchR "letFloatAppR" letFloatAppR  -- maybe letFloatExprR to replace these two
  <+ watchR "caseFloatCaseR" caseFloatCaseR
  <+ watchR "caseFloatAppsR" caseFloatAppsR
  <+ watchR "caseDefaultR" caseDefaultR
  <+ watchR "detickE" detickE  -- done elsewhere. still needed here?
  <+ watchR "abstReprCase" abstReprCase
  <+ watchR "abstReprCon" abstReprCon
  <+ watchR "simplifyScrutineeR" simplifyScrutineeR
  <+ watchR "recastR" recastR
  <+ watchR "argCastSimplify" argCastSimplify
  <+ watchR "castFloatApps" castFloatApps
  <+ watchR "castFloatR" castFloatR  -- combination and elim, too. rename.

--   <+ watchR "pairCaseToLet" pairCaseToLet

simplifyScrutineeR :: ReExpr
simplifyScrutineeR = -- (observeV "simplifyScrutineeR" >>>) $
  onScrutineeR $
    do guardMsgM (not . isStandardType <$> exprTypeT) "scrutinee has standard type"
       simplifyOneStepE <+ unfoldGentlyR

isStandardType :: Type -> Bool
isStandardType (coreView -> Just ty) = isStandardType ty
isStandardType (TyConApp tc args) | isPairTC tc = all isStandardType args
isStandardType (FunTy dom ran) = isStandardType dom && isStandardType ran
isStandardType ty = isPrimitiveTy ty

-- | Like 'unfoldR', but doesn't betaReducePlusR, which can duplicate reification work.
unfoldGentlyR :: ReExpr
unfoldGentlyR = watchR "unfoldGentlyR" $
                onAppsHead (acceptR okay >> inlineR)
 where
   okay (Var v) = not (isRepMeth (fqVarName v))
   okay _ = False

onAppsHead :: Unop ReExpr
onAppsHead re = do (h,args) <- arr collectArgs
                   flip mkCoreApps args <$> (re $* h)

-- Use in a final pass to generate helpful error messages for non-reified
-- syntax.
reifyOops :: ReExpr
reifyOops =
  unReify >>>
  do ty  <- exprTypeT
     str <- showPprT
     appsE "reifyOopsEP#" [ty] [Lit (mkMachString str)]

reifyMisc :: ReExpr
reifyMisc = lintExprR' <<<
       watchR "reifyEval"     reifyEval
  <+   watchR "reifyRepMeth"  reifyRepMeth
  <+   watchR "reifyStdMeth"  reifyStdMeth
  <+   watchR "reifyIf"       reifyIf
  <+   watchR "reifyBottom"   reifyBottom
  <+   watchR "reifyDelay"    reifyDelay
  <+   watchR "reifyLoop"     reifyLoop
  <+   watchR "reifyLit"      reifyLit
  <+   watchR "reifyApp"      reifyApp -- special apps must come earlier
  <+   watchR "reifyLam"      reifyLam
  <+   watchR "reifyPrim'"    reifyPrim'
  <+   watchR "reifyReified"  reifyReified
  <+ nowatchR "reifySimplify" reifySimplify
  <+   watchR "reifyLet"      reifyLet
  <+   watchR "reifyPairCase" reifyPairCase
  <+   watchR "reifyLetFloat" reifyLetFloat
  <+   watchR "reifyUnfold"   reifyUnfold  -- last resort

-- TODO: move reifyPrim to before reifyApp. Faster?
-- Does reifyApp eventually fail on primitives?

-- TODO: either comment out lintExprR' when not debugging or have it turned on
-- only in verbose mode (getVerboseT).

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

findIdP :: String -> TransformH a Id
findIdP = findIdT . primName

primName :: String -> HermitName
primName = mkQualified "Circat.Prim"

-- TODO: generalize primName, lamName, etc

-- Map name to prim name and dictionary constraints
primMap :: M.Map String String
primMap = M.fromList
  [ ("GHC.Classes.not"   , "NotP")
  , ("GHC.Classes.&&"    , "AndP")
  , ("GHC.Classes.||"    , "OrP")
  , ("Circat.Misc.xor"   , "XorP")
  , ("Data.Tuple.fst"    , "ExlP")
  , ("Data.Tuple.snd"    , "ExrP")
  , ("Data.Either.Left"  , "InlP")
  , ("Data.Either.Right" , "InrP")
  , ("GHC.Tuple.(,)"     , "PairP")
  ]

-- TODO: make primitives a map to expressions, to use during reification. Or
-- maybe a transformation that succeeds only for primitives, since we'll have to
-- look up IDs.

isPrimitiveName :: String -> Bool
isPrimitiveName name =
     name `M.member` primMap
  || name `M.member` stdMeths

isPrimOrRepMeth :: Var -> [Type] -> Bool
isPrimOrRepMeth (fqVarName -> name) tys =
  isRepMeth name || (isPrimitiveName name && all isPrimitiveTy tys)

isPrimitiveOp :: Var -> Bool
isPrimitiveOp (fqVarName -> name) =
     name `M.member` primMap
  || name `M.member` stdMeths

isPrimitiveTy :: Type -> Bool
isPrimitiveTy ty = any ($ ty) [isUnitTy,isBoolTy,isIntTy,isDoubleTy]

-- | case c of { False -> a'; True -> a }  ==>  if_then_else c a a'
-- Assuming there's a HasIf instance.
rewriteIf :: ReExpr
rewriteIf = do Case c wild ty [(_False,[],a'),(_True,[],a)] <- id
               guardMsg (isBoolTy (exprType' c)) "scrutinee not Boolean"
               guardMsg (isDeadOcc (idOccInfo wild)) "rewriteIf: wild is alive"
               ifCircTc <- findTyConT (lamName "IfCirc")
               dict     <- buildDictionaryT' $* TyConApp ifCircTc [ty]
               apps' (lamName "if'") [ty] [dict,pair c (pair a a')]
 where
   pair p q = mkCoreTup [p,q]

{--------------------------------------------------------------------
    Another pass at primitives
--------------------------------------------------------------------}

simplePrims :: M.Map String (Type -> [Type] -> TransformH a CoreExpr)
simplePrims = mk <$> primMap
 where
   mk name primTy tyArgs =
     do primV <- findIdP name
        -- type is Prim primTy
        -- pprTrace "simplePrims" (ppr primV <+> text "::" <+> ppr primTy) (return ())
        appsE1 "kPrimEP" [primTy] (mkApps (Var primV) (Type <$> tyArgs))

reifyPrim' :: ReExpr
reifyPrim' =
  unReify >>>
  do ty <- exprTypeT
     (Var (fqVarName -> flip M.lookup simplePrims -> Just mk), tyArgs, [])
       <- callSplitT
     mk ty tyArgs

{--------------------------------------------------------------------
    Run it
--------------------------------------------------------------------}

reifyE :: ReExpr
reifyE = watchR "reifyE" $
         anytdE (repeatR reifyMisc)

#if 0
reifyR :: ReCore
reifyR = id -- tryR (anytdR (promoteR reifyOops))
       . traceR "done"
       . tryR (promoteR reifyGutsR)
       . traceR "reifying"
       . tryR monomorphR
       . traceR "monorphizing"
       . tryR (anytdR (promoteR unfoldDriver))
       . tryR preMonoR
       . tryR (anybuR (promoteR detickE)) -- for ghci break points
       . traceR "preparation"

-- Since we've switched to a later compiler phase, maybe I don't need these first few.

reifyProgR :: ReProg
reifyProgR = progBindsAnyR (const $
                            -- observeR "reifyBindR" .
                            nonRecAllR id reifyE)

reifyGutsR :: ReGuts
reifyGutsR = modGutsR reifyProgR

reifyMonomorph :: ReExpr
reifyMonomorph = watchR "reifyMonomorph" $
                 inReify ( tryR unshadowE
                         . {- bracketR "simplifyE" -} (tryR simplifyE)
                         -- . tryR (anybuE (repeatR castFloatR))
                         . traceR "simplifying"
                         . monomorphizeE
                         . observeR "monomorphizing"
                         )

-- TODO: Weave cast floating into monomorphize, defining mkLam, mkApp, mkCase, etc.

-- simplifyWithLetFloatingE can take much longer than simplifyE, so use it
-- mainly when debugging.

monomorphR :: ReCore
monomorphR = anytdR (promoteR reifyMonomorph)
#endif

unfoldDriver :: ReExpr
unfoldDriver = tryR bashE . tryR simplifyE .  -- TODO: simpler simplification
               unfoldNamesR ((fromString . ("LambdaCCC.Run." ++)) <$>
                             ["go","go'","goSep","goNew","goNew'"])
                             -- ,"goM","goM'","goMSep","reifyMealy"

-- Note: unfoldNamesR could be made more efficient. Maybe fix it or use an more
-- direct route with unfoldPredR and a *set* of names.

-- | Construct a recast function from a to b
recastF :: Type -> Type -> TransformH a CoreExpr
recastF (regularizeType -> a) (regularizeType -> b) =
  idRC <+ reprR <+ abstR <+ funR <+ oopsR
 where
    idRC  = do guardMsg (a =~= b) "recast id: types differ"
               idId <- findIdT "Prelude.id"
               return $ Var idId `App` Type a
    reprR = do f <- hasRepMethod "repr" $* a
               (a',b') <- unJustT $* splitFunTy_maybe (exprType' f)
               guardMsg (a' =~= a) "recast tryMeth: a' /= a"
               g <- recastF b' b
               buildCompositionT g f
    abstR = do g <- hasRepMethod "abst" $* b
               (a',b') <- unJustT $* splitFunTy_maybe (exprType' g)
               guardMsg (b' =~= b) "recast tryMeth: b' /= b"
               f <- recastF a a'
               buildCompositionT g f
    funR  = do (aDom,aRan) <- unJustT $* splitFunTy_maybe a
               (bDom,bRan) <- unJustT $* splitFunTy_maybe b
               f <- recastF bDom aDom  -- contravariant
               h <- recastF aRan bRan  -- covariant
               glueV <- findIdT "LambdaCCC.Reify.-->"
               -- return $ 
               unfoldR $*
                 mkApps (Var glueV)
                        ([Type aDom,Type aRan,Type bDom,Type bRan, f,h])
    oopsR = do str <- showPprT $* (a,b)
               -- _ <- traceR ("recastF unhandled: " ++ str)
               -- fail "oopsR"
               -- Can be okay for dictionaries, esp IfCat (:>)
               fail ("recastF unhandled: " ++ str)

-- To do: Rewrite recastF to work directly from the coercion rather than just
-- its type, so that we won't have to search.

-- TODO: Try reworking recastF to take an expression argument, so that it
-- doesn't have to build id, (.), etc.

-- | Add pre- and post-processing.
-- Used dynamically by recastF
(-->) :: forall a b a' b'. (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f
-- f --> h = \ g x -> h (g (f x))
{-# INLINE (-->) #-}

-- | Replace a cast expression with the application of a recasting function
recastR :: ReExpr
recastR = do Cast e (coercionKind -> Pair a b) <- id
             f <- recastF a b
             tryR unshadowE . tryR bashE $* App f e

-- TODO: remove the unshadowE when not debugging

-- TODO: replace bashE

{--------------------------------------------------------------------
    Experiment in polymorphic reification
--------------------------------------------------------------------}

-- t --> EP t
epTy :: ReType
epTy = do ty <- id
          tc <- findTyConT (lamName epS)
          return (TyConApp tc [ty])

-- abstract-reifies
-- float-reifies >>> try unshadow
-- try (one-td reify-beta-expand-plus)

-- try (any-bu let-float-with-lift)
-- tryR (modGutsR (anybuR letFloatTopR)) .

-- Like letFloatTopR but on CoreBind
letFloatTopR' :: TransformH CoreBind [CoreBind]
letFloatTopR' = 
    arr progToBinds
  . watchR "letFloatTopR" letFloatTopR
  . arr (`ProgCons` ProgNil)
  . okay
 where
   -- RHS of inner let can be anything but a coercion
   okay = nonRecAllR id (accepterRhs (arr (not . isCoArg)))
          -- nonRecAllR id (letAllR (nonRecAllR id (acceptR (not . isCoArg))) id)

-- | Tweak the unqualified part of a name, keeping the module name intact,
-- yielding a string for 'newIdT' or 'findIdT.'
onUQname :: Unop String -> Name -> String
onUQname f nm = modStr ++ f (unqualifiedName nm)
 where
   modStr = maybe "" (\m -> moduleNameString (moduleName m) ++ ".")
              (nameModule_maybe nm)

-- onUQname based on hermit's qualifiedName.

lamBound :: (ReadCrumb c, ExtendCrumb c, AddBindings c)
         => Var -> Unop (Transform c m a b)
lamBound v t = transform (\ c -> applyT t (addLambdaBinding v c @@ Lam_Body))

-- | Expand drivers to reveal reify calls, and transform reify calls away.
tickleReifies :: ReExpr
tickleReifies = -- watchR "tickleReifies" $
  --  tryR (anytdE reifyOops) .  -- sometimes helps debugging
    tryR (anytdE (repeatR reifyMisc))
  . tryR (anytdE (repeatR unfoldDriver))

-- TODO: Combine traversals.

reifyBind :: TransformH CoreBind ([CoreBind],[CoreRule])
reifyBind = -- watchR "reifier" $
  do b@(NonRec v rhs0) <- id
     -- pprTraceV "reifyBind" (ppr v <+> text "::" <+> ppr (varType v))
     -- pprTrace "reifyBind" (ppr v <+> text "::" <+> ppr (varType v)) (return ())
     -- pprTraceV "reifyBind" (ppr b)
     -- pprTrace "reifyBind" (ppr b) (return ())
     -- void $ observeR "reifyBind" $* b
     rhs <- tryR tidyE $* rhs0   -- for ghci
     void $ observeV "reifyBind" $* NonRec v rhs
     (bndrs,rhs') <- go (uqVarName v) rhs
     -- Lift let $reify_foo_fun to top
     Let b' ruleRhs  <- lintExprR' . -- while debugging
                        tryR (anybuE letFloatReifier) $* rhs'
     void $ observeV "reified version" $* Let b' ruleRhs
     pprTraceV "reifyBind b'" (ppr b')
     rule <- mkReifyRule bndrs v (snd (collectBinders ruleRhs))
     return ([b,b'],[rule])
  <+ ( arr (\ b -> ([b],[])) . tryR (nonRecAllR id tickleReifies) )
  -- TODO: Rec
  -- TODO: Rename rhs to rhs1, and rhs' to rhs.
 where
   go :: String -> CoreExpr -> TransformH a ([Var],CoreExpr)
   -- go _ e | pprTrace "go" (ppr e) False = error "WAT"
   go nm e = do guardMsg (not (isTyCoArg e)) "Cannot reify a type or coercion"
                case (exprType' e, e) of
                  (_, Lam v body) | isTyVar v || isDictId v ->
                    ((v:) *** Lam v) <$> lamBound v (go nm body)
                  (ForAllTy {}, _)                -> etaRetry "t"
                  (FunTy dom _, _) | isDictTy dom -> etaRetry "eta"
                  _ -> ([],) <$> ( reifyBetaExpandPlusR nm
                                 . tryR (floatReifies . abstractReifies)
                                 . reifyE   -- can fail
                                 -- . observeV "Reifying"
                                 . reifyOf e
                                 )
    where
      etaRetry etaName = go nm =<< etaExpandR etaName $* e
   -- Tidying to help callTyDictsT. TODO: revisit.
   -- I may need it elsewhere as well.
   tidyE = -- bracketR "tidyE" $
           anybuE detickE
   mkReifyRule :: [Var] -> Id -> CoreExpr -> TransformH a CoreRule
   mkReifyRule vs i rhs =
     do reifyId <- findIdT reifyName
        let rule = mkRule False                             -- True -- auto
                          False                             -- local
                          (fsLit ("reify " ++ uqVarName i)) -- name
                          AlwaysActive                      -- act
                          (varName reifyId)                 -- fn
                          vs                                -- bndrs
                          args                              -- args
                          rhs                               -- rhs
        -- liftIO $ putStrLn ("Rule: " ++ unpackFS (ru_name rule))
        pprTraceV "Generated rule" (ppr rule)
        return rule
    where
      args = [Type (exprType' arg),arg] where arg = appV i
      appV v = mkCoreApps (Var v) (varToCoreExpr <$> vs)

-- TODO: Try using exprIsLambda_maybe instead of eta-expansion.

lintExprR' :: RewriteH CoreExpr
-- lintExprR' = catchM lintExprR (\ msg -> error msg . observeR "lintExprR")

lintExprR' = catchM lintExprR (\ msg -> do e <- id
                                           pprTrace "lintExprR" (ppr e) (return ())
                                           error msg)

-- lintExprR' = catchM lintExprR error

-- class Monad m => MonadCatch m where
--   -- | Catch a failing monadic computation.
--   catchM :: m a -> (String -> m a) -> m a


-- lintExprR' = do str <- lintExprT
--                 if str /= "Core Lint Passed" then
--                   {- fail "lintExprR': Lint error" . -} traceR str
--                  else
--                   id

-- TODO: intercept failure and report the message.


augmentProgBinds :: TransformH CoreBind ([CoreBind],[CoreRule]) ->
                    TransformH [CoreBind] ([CoreBind],[CoreRule])
augmentProgBinds (applyT -> rebind) = transform go
 where
   go :: HermitC -> [CoreBind] -> HermitM ([CoreBind],[CoreRule])
   go _ [] = return mempty
   go c (bindIn:bindsIn) =
     do o@(bindsOut,rulesOut) <- rebind c bindIn
        os <- go (addHermitCoreRules rulesOut (addBindingGroups bindsOut c)) bindsIn
        return (o `mappend` os)

-- Old version:
-- 
-- augmentProgBinds rew = arr mconcat . mapT rew

-- TODO: Similarly for let bindings, I think.

addBindingGroups :: (AddBindings c, ReadCrumb c) => [CoreBind] -> c -> c
addBindingGroups = flip (foldr addBindingGroup)

-- TODO: Generalize beyond HermitC, and add to hermit.

-- TODO: Have reifyProg succeed iff *any* reifyBind succeeds.

-- reifyBind :: TransformH CoreBind ([CoreBind],[CoreRule])

-- Simple optimizations. Always succeeds, so take care!
simpleOptExprR :: ReExpr
simpleOptExprR = tryR (watchR "simpleOptExprR" $ changedSynR (arr simpleOptExpr))

-- TODO: Stop checking changedSynR when we're not watching. I only put it there to reduce noise.

reifyBinds :: TransformH [CoreBind] ([CoreBind],[CoreRule])
reifyBinds = augmentProgBinds reifyBind

reifyModule :: ReGuts
reifyModule =
  -- ((do {rs <- getReifyRules; pprTraceV "getReifyRules" (ppr rs)}) >> ) $
  -- modGutsR (tryR (walkP anybuR progBindElimR)) >>> -- *
  tryR unshadowP >>>  -- For easier observation. Remove later.
  -- traceR "reifyModule" >>>
  -- tryR (watchR "specialiseR" specialiseR) >>>
  do guts <- id
     (prog',rules) <- reifyBinds $* mg_binds guts
     pprTraceV "reifyModule new rules" (ppr rules)
     return guts { mg_binds = prog', mg_rules = rules ++ mg_rules guts }
  >>> unshadowP
  -- >>> modGutsR (observeR "reifyModule result")
 where
   unshadowP :: ReGuts
   unshadowP = tryR (extractR unshadowR)

-- * See journal from 2016-02-05.

walkP :: Unop ReCore -> Unop ReProg
walkP trav r = extractR (trav (promoteR r :: ReCore))

-- | An always-succeeding rewrite that turns failures into 'Nothing'.
-- Similar to 'mtryM', but works for non-monoidal types as well.
catchMaybe :: MonadCatch m => m a -> m (Maybe a)
catchMaybe ma = tryM Nothing (fmap Just ma)
-- catchMaybe ma = fmap Just ma <+ return Nothing

-- Abstract out sub-expressions satisfying a given predicate
abstractPredM :: TransformH CoreExpr Bool -> RewriteH CoreExpr
abstractPredM p = prunetdE (letIntroR "z" . accepterR p)

-- let-float when the RHS satisfies a given predicate
letFloatsPredM :: TransformH CoreExpr Bool -> RewriteH CoreExpr
letFloatsPredM p = walkE innermostR (accepterRhs p . letFloatExprR)

accepterRhs :: (Monad m, ReadCrumb c, ExtendCrumb c, AddBindings c) =>
               Transform c m CoreExpr Bool -> Rewrite c m CoreExpr
accepterRhs p = letT (nonRecT mempty p (\ () b -> b)) id (\ b _ -> b) >> id

-- accepterRhs p = letAllR (nonRecAllR id (accepterR p)) id

abstractReifies :: ReExpr
abstractReifies = watchR "abstractReifies" $
                  abstractPredM (arr isReify)

floatReifies :: ReExpr
floatReifies = watchR "floatReifies" $
               tryR unshadowE .  -- To help debugging
               cseExprR .
               letFloatsPredM (arr isReify)

-- | Convert outer reify let bindings into a multi-beta-redex. Assumes (and
-- doesn't check) that none of the variables appear in any of the RHSs.
reifyBetaExpandPlusR :: String -> ReExpr
reifyBetaExpandPlusR nm = prefixFailMsg ("reifyBetaExpandPlusR failed: ") $
                          go [] [] =<< id
 where
   go :: [Var] -> [CoreExpr] -> CoreExpr -> TransformH a CoreExpr
   go vs es (Let (NonRec v e) body) | isReify e = go (v:vs) (e:es) body
   go vs es body =
     do -- guardMsg (not (null vs)) "No reify bindings"
        fun <- letIntroR (reifyNamePrefix ++ nm) $* mkCoreLams vs body
        return (mkCoreApps fun es)

reifyNamePrefix :: String
reifyNamePrefix = "$reify_"

letFloatReifier :: ReExpr
letFloatReifier = -- letAllR (nonRecAllR id (tryR (anytdE reifyOops))) id . -- debugging aid
                  acceptR isLetReifier . (letFloatExprR <+ letFloatLamLiftR)
 where
   isLetReifier (Let (NonRec v _) _) = isPrefixOf reifyNamePrefix (uqVarName v)
   isLetReifier _ = False

isReify :: CoreExpr -> Bool
isReify (collectArgs -> (Var v,[_,_])) = cmpHN2Var reifyName v
isReify _ = False

isEval :: CoreExpr -> Bool
-- isEval e | pprTrace "isEval" (ppr e) False = error "WAT!"
isEval (collectArgs -> (Var v,[_,_])) = -- pprTrace "isEval" (text "cmpHN2Var evalName" <+> ppr v <+> equals <+> ppr (cmpHN2Var evalName v)) $
                                        cmpHN2Var evalName v
isEval _ = False

-- (\ x -> let v = r in e)  ==>  let v' = (\ x -> r) in (\ x -> e[v -> v' x))
letFloatLamLiftR :: ReExpr
letFloatLamLiftR = prefixFailMsg ("letFloatLamLiftR failed: ") $
  withPatFailMsg (wrongExprForm "Lam x (Let (NonRec v r) e)") $
  do Lam x (Let (NonRec v rhs) e) <- id
     v' <- newIdT (uqVarName v) $* liftTy x (varType v)
     let sub = substCoreExpr v (App (varToCoreExpr v') (varToCoreExpr x))
     return $ Let (NonRec v' (Lam x rhs)) (Lam x (sub e))
 where
   liftTy :: Var -> Unop Type
   liftTy x | isTyVar x = ForAllTy x
            | otherwise = FunTy (varType x)



{--------------------------------------------------------------------
    Commands for interactive use
--------------------------------------------------------------------}

externals :: [External]
externals =
    [ externC' "reifyE" reifyE
    -- TEMP:
    , externC' "rewrite-if" rewriteIf
    , externC' "reify-misc" reifyMisc
    , externC' "reify-eval" reifyEval
    , externC' "reify-if" reifyIf
    , externC' "reify-delay" reifyDelay
    , externC' "reify-loop" reifyLoop
    , externC' "reify-bottom" reifyBottom
    , externC' "reify-repmeth" reifyRepMeth
    , externC' "reify-stdmeth" reifyStdMeth
    , externC' "reify-app" reifyApp
    , externC' "reify-lam" reifyLam
    , externC' "reify-let" reifyLet
    , externC' "reify-lit" reifyLit
    , externC' "reify-prim" reifyPrim
    , externC' "reify-prim'" reifyPrim'
    , externC' "reify-simplify" reifySimplify
    , externC' "reify-reified" reifyReified
    , externC' "reify-unfold" reifyUnfold
    , externC' "reify-oops" reifyOops
    , externC' "optimize-cast" optimizeCastR
    , externC' "let-trivial-subst" letTrivialSubstR
    , externC' "recast" recastR
    , externC' "unreify" unReify
    , externC' "uneval" unEval
    , externC' "reify-of" (reifyOf =<< id)
    , externC' "tickle-reifies" (tickleReifies :: ReExpr)
    , externC' "lam-float-cast" lamFloatCastR
    , externC' "reify-module" reifyModule
    , externC' "abstract-reifies" abstractReifies
    , externC' "float-reifies" floatReifies
    , externC' "reify-beta-expand-plus" (reifyBetaExpandPlusR "foo")
    , externC' "let-float-lam-lift" letFloatLamLiftR
    , externC' "let-float-reifier" letFloatReifier
    , externC' "pair-case-to-let" pairCaseToLet
    , externC' "simplify-expr" simplifyExprR
    , externC' "unfold-driver" unfoldDriver
    , externC' "simplify-scrutinee" simplifyScrutineeR
    , externC' "simplify-one-step" simplifyOneStepE
    ]

--     , externC' "reify" reifyR
--     , externC' "reify-monomorph" reifyMonomorph
--     , externC' "reify-prog" reifyProgR
--     , externC' "monomorph" monomorphR
