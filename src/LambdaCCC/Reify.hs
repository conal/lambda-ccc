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

-- TODO: Explicit exports

import Prelude hiding (id,(.))

import Data.Functor (void)
import Control.Category (Category(..))
import Control.Monad ((<=<))
import Control.Arrow ((>>>))
import qualified Data.Map as M
import Data.String (fromString)

import HERMIT.Core (localFreeIdsExpr)
import HERMIT.GHC hiding (mkStringExpr)
import TcType (isDoubleTy)  -- Doesn't seem to be coming in with HERMIT.GHC.
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary hiding (externals)
import HERMIT.Name (HermitName)
import HERMIT.External (External)

import Circat.Misc ((<~))

import HERMIT.Extras hiding (findTyConT,observeR',orL,simplifyE)
import qualified HERMIT.Extras as Ex -- (Observing, observeR', orL, labeled)

import Monomorph.Stuff (preMonoR, monomorphizeE, simplifyE)

{--------------------------------------------------------------------
    Utilities. Move to HERMIT.Extras
--------------------------------------------------------------------}

unshadowE :: ReExpr
unshadowE = extractR unshadowR

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', orL, labeled)

observing :: Ex.Observing
observing = False -- True

-- #define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error
#else
-- watchR :: String -> Unop ReExpr
-- watchR lab r = labeled observing (lab,r) >>> lintExprR  -- Fail softly on core lint error.

watchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
watchR lab r = labeled' observing (lab,r)  -- don't lint
#endif

nowatchR :: InCoreTC a => String -> RewriteH a -> RewriteH a
nowatchR _ = id

-- nowatchR = watchR

orL :: InCoreTC t => [(String,RewriteH t)] -> RewriteH t
orL = Ex.orL observing

-- labeled :: InCoreTC t => (String, RewriteH t) -> RewriteH t
-- labeled = Ex.labeled observing

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

repName :: String -> HermitName
repName = moduledName "Circat.Rep"

lamName :: String -> HermitName
lamName = moduledName "LambdaCCC.Lambda"

-- ifName :: String -> HermitName
-- ifName = moduledName "Circat.If"

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
reifyEval = unReify >>> unEval

-- Generate a reify call. Fail on dictionaries.
reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = do guardMsg (not (isDictTy (exprType' e)))
                        "reifyOf: Given a type expr."
               appsE reifyS [exprType' e] [e]

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

-- | Turn a monomorphic let into a beta-redex.
reifyMonoLet :: ReExpr
reifyMonoLet =
    unReify >>>
    do Let (NonRec v@(isForAllTy . varType -> False) rhs) body <- idR
       guardMsgM (worthLet rhs) "trivial let"
       rhsE  <- reifyOf rhs
       sub   <- varSubst [v]
       bodyE <- reifyOf (sub body)
       appsE "letvP#" [varType v, exprType' body] [varLitE v, rhsE,bodyE]

-- Placeholder
worthLet :: CoreExpr -> TransformU Bool
worthLet _ = return True

-- Simpler but can lead to loops. Maybe fix by following with reifyLam.
-- 
-- reifyMonoLet =
--   inReify $
--     do Let (NonRec v@(isForAllTy . varType -> False) rhs) body <- idR
--        return (Lam v body `App` rhs)

-- TODO: Perhaps combine reifyPolyLet and reifyMonoLet into reifyLet

-- The simplifyE is for beta-reducing type applications.

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
     guardMsg (not (any isType moreArgs))
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
   -- transformed away in the type-encode plugin.
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
          ("reifyEval"    , reifyEval)
        , ("reifyRepMeth" , reifyRepMeth)
        , ("reifyStdMeth" , reifyStdMeth) 
        , ("reifyIf"      , reifyIf)
        , ("reifyBottom"  , reifyBottom)
        , ("reifyDelay"   , reifyDelay)
        , ("reifyLoop"    , reifyLoop)
        , ("reifyLit"     , reifyLit)
        , ("reifyApp"     , reifyApp)
        , ("reifyLam"     , reifyLam)
        , ("reifyMonoLet" , reifyMonoLet)
        , ("reifyTupCase" , reifyTupCase)
        , ("reifyPrim"    , reifyPrim)
--      , ("reifyCast"    , reifyCast)
        ]

reifyMisc :: ReExpr
reifyMisc = orL miscL

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

findIdP :: String -> TransformH a Id
findIdP = findIdT . primName

primName :: String -> HermitName
primName = moduledName "Circat.Prim"

-- TODO: generalize primName, lamName, etc

-- Map name to prim name and dictionary constraints
primMap :: M.Map String String
primMap = M.fromList
  [ ("GHC.Classes.not"           , "NotP")
  , ("GHC.Classes.&&"            , "AndP")
  , ("GHC.Classes.||"            , "OrP")
  , ("Circat.Misc.xor"           , "XorP")
  , ("GHC.Tuple.fst"             , "ExlP")
  , ("GHC.Tuple.snd"             , "ExrP")
  , ("Data.Either.Left"          , "InlP")
  , ("Data.Either.Right"         , "InrP")
  , ("GHC.Tuple.(,)"             , "PairP")
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
    Run it
--------------------------------------------------------------------}

reifyE :: ReExpr
reifyE = anytdE (repeatR reifyMisc)

reifyProgR :: ReProg
reifyProgR = progBindsAnyR (const $
                            -- observeR "reifyBindR" .
                            nonRecAllR id reifyE)

reifyMonomorph :: ReExpr
reifyMonomorph = inReify (tryR simplifyE . monomorphizeE)

reifyR :: ReCore
reifyR = promoteR (modGutsR reifyProgR)
       . tryR monomorphR
       . tryR (anytdR (promoteR unfoldDriver))
       . tryR preMonoR -- though always succeeds (for now)

unfoldDriver :: ReExpr
unfoldDriver = tryR bashE . tryR simplifyE .  -- TODO: simpler simplification
               unfoldNamesR ((fromString . ("LambdaCCC.Run." ++)) <$>
                             ["go","go'","goSep","goNew","goNew'"])
                             -- ,"goM","goM'","goMSep","reifyMealy"

-- Note: unfoldNamesR could be made more efficient. Maybe fix it or use an more
-- direct route with unfoldPredR and a *set* of names.

monomorphR :: ReCore
monomorphR = anytdR (promoteR reifyMonomorph)

-- reifyR = promoteR (modGutsR reifyProgR)

externals :: [External]
externals =
    [ externC' "reify" reifyR
    -- TEMP:
    , externC' "monomorph" monomorphR
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
    , externC' "reify-oops" reifyOops
    , externC' "reify-monomorph" reifyMonomorph
    , externC' "reify-prog" reifyProgR
    , externC' "unfold-driver" unfoldDriver
    , externC' "optimize-cast" optimizeCastR
    ]
