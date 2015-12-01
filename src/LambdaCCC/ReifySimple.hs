{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, TupleSections, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ReifySimple
-- Copyright   :  (c) 2013 Tabula, Inc.
-- LICENSE     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Reify a Core expression into GADT
----------------------------------------------------------------------

module LambdaCCC.ReifySimple
  ( reifyMisc, lamName, repName --, ifName
  , inReify -- TEMP
  , reifyEval, reifyIf, reifyDelay, reifyLoop, reifyBottom
  , reifyRepMeth, reifyApp, reifyLam, reifyMonoLet
  , reifyTupCase, reifyLit, reifyPrim, reifyStdMeth
  , reifyOops
  , isPrimOrRepMeth, isPrimitiveOp, isPrimitiveTy
  , observing
  ) where

  -- TODO: export externals instead, and use in Monomorphize

import Prelude hiding (id,(.))

import Data.Functor ((<$>),void)
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

import LambdaCCC.Misc ((<~))

import HERMIT.Extras hiding (findTyConT,observeR',triesL)
import qualified HERMIT.Extras as Ex -- (Observing, observeR', triesL, labeled)

-- Drop TypeEncode for now.
-- import TypeEncode.Plugin (encodeOf, reConstructR, reCaseR)
-- import qualified TypeEncode.Plugin as Enc

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False -- True

triesL :: InCoreTC t => [(String,RewriteH t)] -> RewriteH t
triesL = Ex.triesL observing

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

-- reify u --> u
unReify :: ReExpr
unReify = unCallE1 reifyS
-- eval e --> e
unEval :: ReExpr
unEval = unCallE1 evalS

-- reify (eval e) --> e
reifyEval :: ReExpr
reifyEval = unReify >>> unEval

reifyOf :: CoreExpr -> TransformU CoreExpr
reifyOf e = appsE reifyS [exprType' e] [e]

evalOf :: CoreExpr -> TransformU CoreExpr
evalOf e = appsE evalS [dropEP (exprType' e)] [e]

dropEP :: Unop Type
dropEP (TyConApp (unqualifiedName . tyConName -> name) [t]) =
  if name == epS then t
  else error ("dropEP: not an EP: " ++ show name)
dropEP _ = error "dropEP: not a TyConApp"

reifyR :: ReExpr
reifyR = idR >>= reifyOf

-- reify (u v) --> reify u `appP` reify v
reifyApp :: ReExpr
reifyApp = do App u v <- unReify
              Just (a,b) <- constT (return (splitFunTy_maybe (exprType' u)))
              -- guardMsg (not (isDictTy a)) "reifyApp: dictionary argument"
              u' <- reifyOf u
              v' <- reifyOf v
              appsE "appP" [b,a] [u', v'] -- note b,a

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
inReify = reifyR <~ unReify

#if 0
reifyRuleNames :: [RuleName]
reifyRuleNames = map (RuleName . ("reify/" ++))
  [ "not","(&&)","(||)","xor","(+)","(*)","exl","exr","pair","inl","inr"
  , "if","()","false","true"
  ]

-- ,"if-bool","if-pair"

-- or: words "not (&&) (||) xor ..."

-- TODO: Is there a way not to redundantly specify this rule list?
-- Yes -- trust GHC to apply the rules later.
-- Keep for now, to help us see that whether reify applications vanish.

reifyRules :: ReExpr
reifyRules = rulesR reifyRuleNames >>> cleanupUnfoldR

#endif

#if 0
reifyCast :: ReExpr
reifyCast =
  unReify >>>
  do Cast e co <- idR
     let Pair a b = coercionKind co
     re   <- reifyOf e
     aTyp <- buildTypeableT' $* a
     bTyp <- buildTypeableT' $* b
     appsE "coerceEP" [a,b] [aTyp,bTyp,mkEqBox (toRep co),re]

-- TODO: Probe whether we ever get nominal casts here.
-- If so, reify differently, probably as a Core cast with mkNthCo.

-- Convert a coercion to representational if not already
toRep :: Unop Coercion
toRep co | coercionRole co == Representational = co
         | otherwise = mkSubCo co

#endif

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
     void callDataConT
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
          ("reifyEval"        , reifyEval)
--      , ("reifyRulesPrefix" , reifyRulesPrefix)
--      , ("reifyRules"       , reifyRules)
        , ("reifyRepMeth"     , reifyRepMeth)
        , ("reifyStdMeth"     , reifyStdMeth) 
        , ("reifyIf"          , reifyIf)
        , ("reifyBottom"      , reifyBottom)
        , ("reifyDelay"       , reifyDelay)
        , ("reifyLoop"        , reifyLoop)
        , ("reifyLit"         , reifyLit)
        ----
        , ("reifyApp"         , reifyApp)
        , ("reifyLam"         , reifyLam)
        , ("reifyMonoLet"     , reifyMonoLet)
        , ("reifyTupCase"     , reifyTupCase)
        , ("reifyPrim"        , reifyPrim)
--      , ("reifyCast"        , reifyCast)
        ]

reifyMisc :: ReExpr
reifyMisc = triesL miscL

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
  -- || isRepMeth name

isPrimOrRepMeth :: Var -> Type -> Bool
isPrimOrRepMeth (fqVarName -> name) ty =
  isRepMeth name || (isPrimitiveName name && isPrimitiveTy ty)

isPrimitiveOp :: Var -> Bool
isPrimitiveOp (fqVarName -> name) =
     name `M.member` primMap
  || name `M.member` stdMeths
  -- || isRepMeth name

-- isPrimitiveOp :: Var -> Type -> Bool
-- isPrimitiveOp (fqVarName -> name) ty =
--      name `M.member` primMap
--   || (name `M.member` stdMeths && isPrimitiveTy ty)
--   || isRepMeth name

-- isPrimitiveOp :: Var -> [CoreExpr] -> Bool
-- isPrimitiveOp (fqVarName -> name) args =
--      name `M.member` primMap
--   || (name `M.member` stdMeths && tyArg1 args)
--   || isRepMeth name
--  where
--    tyArg1 [] = True  -- test hack
--    tyArg1 (Type ty : _) = isPrimitiveTy ty
--    tyArg1 _ = False

isPrimitiveTy :: Type -> Bool
isPrimitiveTy ty = any ($ ty) [isUnitTy,isBoolTy,isIntTy,isDoubleTy]
