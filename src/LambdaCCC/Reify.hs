{-# LANGUAGE CPP, TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

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

module LambdaCCC.Reify where

import Prelude hiding (id,(.))

import Data.Functor (void)
import Control.Category (Category(..))
import Control.Monad ((<=<))
import Control.Arrow ((>>>),arr,(***))
import qualified Data.Map as M
import Data.String (fromString)

import HERMIT.Context (AddBindings,addBindingGroup,HermitC)
import HERMIT.Core (localFreeIdsExpr,substCoreExpr,CoreProg(..),progToBinds,isCoArg,freeVarsExpr)
import HERMIT.GHC hiding (mkStringExpr)
import TcType (isDoubleTy)  -- Doesn't seem to be coming in with HERMIT.GHC.
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary hiding (externals)
import HERMIT.Monad (HermitM)
import HERMIT.Name (HermitName,mkQualified,cmpHN2Var)
import HERMIT.External (External)

import TcType (isIntegerTy)

import Circat.Misc ((<~))

import HERMIT.Extras hiding (findTyConT,observeR',catchesL,simplifyE)
import qualified HERMIT.Extras as Ex -- (Observing, observeR', catchesL, labeled)

import Monomorph.Stuff ({-preMonoR, -} castFloatR, caseDefaultR, simplifyE) -- , simplifyWithLetFloatingE
import LambdaCCC.Monomorphize (abstReprCase,abstReprCon)

{--------------------------------------------------------------------
    Utilities. Move to HERMIT.Extras
--------------------------------------------------------------------}

unshadowE :: ReExpr
unshadowE = extractR unshadowR

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', catchesL, labeled)

observing :: Ex.Observing
observing = False -- True

-- #define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error
#else
-- watchR :: String -> Unop ReExpr
-- watchR lab r = labeled observing (lab,r) >>> lintExprR  -- Fail softly on core lint error.

watchR :: (InCoreTC a, InCoreTC b) => String -> Unop (TransformH a b)
watchR lab r = labeled' observing (lab,r)  -- don't lint
#endif

nowatchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
nowatchR _ = id

-- nowatchR = watchR

catchesL :: InCoreTC t => [(String,RewriteH t)] -> RewriteH t
catchesL = Ex.catchesL observing

-- labeled :: InCoreTC t => (String, RewriteH t) -> RewriteH t
-- labeled = Ex.labeled observing

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

-- Generate a reify call. Fail on types, coercions, and dictionaries.
reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = do guardMsg (not (isTyCoArg e)) "Type or coercion."
               let ty = exprType' e
               guardMsg (not (isDictTy ty)) "Dictionary."
               guardMsg (not (isForAllTy ty)) "Polymorphic."
               guardMsg (not (isIntegerTy ty)) "Integer." -- TODO: Generalize
               -- appsE reifyS [exprType' e] [e]
               apps' reifyName [exprType' e] [e]

-- reifyOf e = appsE reifyS [exprType' e] [e]

evalOf :: CoreExpr -> TransformU CoreExpr
evalOf e = appsE evalS [dropEP (exprType' e)] [e]

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
              appsE "lamvP#" [varType v, exprType' e] [varLitE v,e']

-- reifyDef introduces foo_reified binding, which the letFloatLetR then moves up
-- one level. Typically (always?) the "foo = eval foo_reified" definition gets
-- inlined and then eliminated by the letElimR in reifyMisc.

letTrivialSubstR :: ReExpr
letTrivialSubstR =
 do Let (NonRec v rhs) body <- id
    if | v `notElemVarSet` freeVarsExpr body -> return body
       | exprIsTrivial rhs || isEval rhs     -> letSubstR
       | otherwise                           -> -- traceR "reifyTrivialLet failed" >>>
                                                fail "Non-trivial"

-- When rhs = eval (var x), reify will make it var x. We don't introduce eval
-- any other way.

-- | Turn a monomorphic let into a beta-redex.
reifyMonoLet :: ReExpr
reifyMonoLet = watchR "reifyMonoLet" $
    unReify >>>
    do Let (NonRec v rhs) body <- idR
       -- guardMsgM (worthLet rhs) "trivial let"
       -- Instead of guarding against polymorphic rhs, let reifyOf reject.
       -- guardMsg (not (isForAllTy (varType v))) "polymorphic let"
       rhsE  <- reifyOf rhs
       sub   <- varSubst [v]
       bodyE <- reifyOf (sub body)
       appsE "letvP#" [varType v, exprType' body] [varLitE v, rhsE,bodyE]

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

-- TODO: Combine reifyBottom with reifyStdMeths?

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

-- reify of case on 0-tuple or 2-tuple
reifyTupCase :: ReExpr
reifyTupCase =
  do Case scrut@(exprType' -> scrutT) wild bodyT [alt] <- unReify
     (patE,rhs) <- reifyAlt wild alt
     scrut'     <- reifyOf scrut
     appsE letS [scrutT,bodyT] [patE,scrut',rhs]
 where
   -- Reify a case alternative, yielding a reified pattern and a reified
   -- alternative body (RHS). Only unit and pair patterns. Others are
   -- transformed away.
   reifyAlt :: Var -> CoreAlt -> TransformU (CoreExpr,CoreExpr)
   reifyAlt wild (DataAlt ( isBoxedTupleTyCon . dataConTyCon -> True)
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
      do (_,[_],[_dict,Lit _]) <- callNameSplitT "GHC.Num.fromInteger"
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

reifyAbstCase :: ReExpr
reifyAbstCase = inReify $ watchR "abstReprCase" abstReprCase

reifyAbstCon :: ReExpr
reifyAbstCon = inReify $ watchR "abstReprCon" abstReprCon

callTyDictsT :: Monad m => Transform c m CoreExpr (CoreExpr, [CoreExpr])
callTyDictsT =
  do va@(Var _, args) <- callT
     guardMsg (all (\ e -> isTypeArg e || isDictTy (exprType' e)) args)
              "Arguments must be types or dictionaries"
     return va

-- Already reified, so reuse.
reifyReified :: ReExpr
reifyReified = watchR "reifyReified" $
               unReify >>>
  do (Var v, args) <- callTyDictsT
     reify_v <- findIdT (fromString (reifyVarStr v))
     return $ mkCoreApps (Var reify_v) args

-- Last resort. Not included in reifySimplify.
reifyUnfold :: ReExpr
reifyUnfold = watchR "reifyUnfold" $
              inReify $ callTyDictsT >> anybuE detickE . unfoldR

-- The detickE is an experiment for helping with a ghci issue.
-- See journal from 2016-02-05.

-- TODO: Maybe check that the type of reify_v matches.

reifySimplify :: ReExpr
reifySimplify = inReify simplifyOneStepE

simplifyOneStepE :: ReExpr
simplifyOneStepE = watchR "simplifyOneStepE" $
     watchR "etaReduceR" etaReduceR
  <+ watchR "letElimR" letElimR
  <+ watchR "letTrivialSubstR" letTrivialSubstR
  <+ watchR "castFloatR" castFloatR  -- combination and elim, too. rename.
  <+ watchR "caseReduceR" (caseReduceR False)
  <+ watchR "letFloatCaseR" letFloatCaseR
  <+ watchR "caseFloatCaseR" caseFloatCaseR
  <+ watchR "caseDefaultR" caseDefaultR
  <+ watchR "detickE" detickE

-- Use in a final pass to generate helpful error messages for non-reified
-- syntax.
reifyOops :: ReExpr
reifyOops =
  unReify >>>
  do ty  <- exprTypeT
     str <- showPprT
     appsE "reifyOopsEP#" [ty] [Lit (mkMachString str)]

miscL :: [(String,ReExpr)]
miscL = [ ---- Special applications and so must come before reifyApp
          ("reifySimplify"   , reifySimplify)
        , ("reifyEval"       , reifyEval)
        , ("reifyRepMeth"    , reifyRepMeth)
        , ("reifyStdMeth"    , reifyStdMeth)
        , ("reifyIf"         , reifyIf)
        , ("reifyBottom"     , reifyBottom)
        , ("reifyDelay"      , reifyDelay)
        , ("reifyLoop"       , reifyLoop)
        , ("reifyLit"        , reifyLit)
        , ("reifyApp"        , reifyApp)
        , ("reifyLam"        , reifyLam)
        , ("reifyMonoLet"    , reifyMonoLet)
        , ("reifyTupCase"    , reifyTupCase)
        , ("reifyPrim'"      , reifyPrim')
        , ("reifyAbstCase"   , reifyAbstCase)
        , ("reifyAbstCon"    , reifyAbstCon)
        , ("reifyReified"    , reifyReified)
        , ("reifyUnfold"     , reifyUnfold)
        ]

-- TODO: move reifyPrim to before reifyApp. Faster?
-- Does reifyApp eventually fail on primitives?

reifyMisc :: ReExpr
reifyMisc = catchesL miscL

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
  , ("GHC.Tuple.fst"     , "ExlP")
  , ("GHC.Tuple.snd"     , "ExrP")
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
#endif

reifyE :: ReExpr
reifyE = watchR "reifyE" $
         anytdE (repeatR reifyMisc)

#if 0
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

reifyVarStr :: Id -> String
reifyVarStr v = "$reify_"++ uqVarName v   -- revisit: use module part, too

reifyBind :: TransformH CoreBind ([CoreBind],[CoreRule])
reifyBind = -- watchR "reifier" $
--   do b@(NonRec v rhs) <- id
  do b@(NonRec v rhs0) <- id
     rhs <- tryR (watchR "anybuE detickE" (anybuE detickE)) $* rhs0   -- for ghci
     (bndrs,rhs') <- go (uqVarName v) rhs
     -- Lift let $reify_foo_fun to top
     rhs'' <- tryR (anybuE letFloatWithLiftR) $* rhs'
     v'   <- newIdT (reifyVarStr v) $* exprType' rhs''
     rule <- mkReifyRule bndrs v v'
     newDefs <- (letFloatTopR' <+ arr (: [])) $* NonRec v' rhs''
     pprTrace "reifyBind" (ppr v) (return ())
     return (b : newDefs,[rule])
  <+ arr (\ b -> ([b],[]))
 where
   go :: String -> CoreExpr -> TransformH a ([Var],CoreExpr)
   go nm e = do guardMsg (not (isTyCoArg e)) "Cannot reify a type or coercion"
                case e of
                  Lam v body | isTyVar v || isDictId v ->
                    ((v:) *** Lam v) <$> go nm body
                  _ ->
                    ([],) <$> ( tryR ( reifyBetaExpandPlusR nm
                                     . floatReifies
                                     . abstractReifies )
                              . tryR reifyE
                              . reifyOf e )
   mkReifyRule :: [Var] -> Id -> Id -> TransformH a CoreRule
   mkReifyRule vs i reI =
     do reifyId <- findIdT reifyName
        let rule = Rule { ru_name  = fsLit ("reify " ++ uqVarName i)
                        , ru_act   = AlwaysActive
                        , ru_fn    = varName reifyId
                        , ru_rough = [Just (varName i)]
                        , ru_bndrs = vs
                        , ru_args  = [appV i]
                        , ru_rhs   = appV reI
                        , ru_auto  = True
                        , ru_local = False
                        }
        -- liftIO $ putStrLn ("Rule: " ++ unpackFS (ru_name rule))
        -- void (traceR =<< showPprT $* rule)
        return rule
    where
      appV v = mkCoreApps (Var v) (varToCoreExpr <$> vs)

-- TODO: eta-expand as needed.

augmentProgBinds :: TransformH CoreBind ([CoreBind],[CoreRule]) ->
                    TransformH [CoreBind] ([CoreBind],[CoreRule])
augmentProgBinds (applyT -> rebind) = transform go
 where
   go :: HermitC -> [CoreBind] -> HermitM ([CoreBind],[CoreRule])
   go _ [] = return mempty
   go c (bindIn:bindsIn) =
     do o@(bindsOut,_) <- rebind c bindIn
        os <- go (addBindingGroups bindsOut c) bindsIn
        return (o `mappend` os)

-- Old version:
-- 
-- augmentProgBinds rew = arr mconcat . mapT rew

-- TODO: Similarly for let bindings, I think.

addBindingGroups :: (AddBindings c, ReadCrumb c) => [CoreBind] -> c -> c
addBindingGroups = flip (foldr addBindingGroup)

-- TODO: Have reifyProg succeed iff *any* reifyBind succeeds.

-- reifyBind :: TransformH CoreBind ([CoreBind],[CoreRule])

reifyBinds :: TransformH [CoreBind] ([CoreBind],[CoreRule])
reifyBinds = augmentProgBinds reifyBind

reifyModule :: ReGuts
reifyModule =
  -- modGutsR (tryR (walkP anytdR progBindElimR)) >>> -- *
  unshadowP >>>  -- For easier observation. Remove later.
  do guts <- id
     (prog',rules) <- reifyBinds $* mg_binds guts
     return guts { mg_binds = prog', mg_rules = mg_rules guts ++ rules }
  >>> unshadowP
  -- >>> modGutsR (observeR "reifyModule result")
 where
   unshadowP :: ReGuts
   unshadowP = tryR (extractR unshadowR)

-- See journal from 2016-02-05.

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
     do guardMsg (not (null vs)) "No reify bindings"
        fun <- letIntroR ("$reify_" ++ nm ++ "_fun") $* mkCoreLams vs body
        return (mkCoreApps fun es)

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

letFloatWithLiftR :: ReExpr
letFloatWithLiftR = letFloatExprR <+ letFloatLamLiftR

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
    , externC' "reify-monolet" reifyMonoLet
    , externC' "reify-tupcase" reifyTupCase
    , externC' "reify-lit" reifyLit
    , externC' "reify-prim" reifyPrim
    , externC' "reify-prim'" reifyPrim'
    , externC' "reify-simplify" reifySimplify
    , externC' "reify-oops" reifyOops
    , externC' "optimize-cast" optimizeCastR
    , externC' "unreify" unReify
    , externC' "uneval" unEval
    , externC' "reify-of" (reifyOf =<< id)

    , externC' "reify-module" reifyModule
    , externC' "abstract-reifies" abstractReifies
    , externC' "float-reifies" floatReifies
    , externC' "reify-beta-expand-plus" (reifyBetaExpandPlusR "foo")
    , externC' "let-float-lam-lift" letFloatLamLiftR
    , externC' "let-float-with-lift" letFloatWithLiftR
    ]

--     , externC' "reify" reifyR
--     , externC' "reify-monomorph" reifyMonomorph
--     , externC' "reify-prog" reifyProgR
--     , externC' "unfold-driver" unfoldDriver
--     , externC' "monomorph" monomorphR
