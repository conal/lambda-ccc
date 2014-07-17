{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE MagicHash, MultiWayIf, TupleSections, CPP #-}
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

module LambdaCCC.ReifySimple (reifyMisc, reifyCast, inReify, isPrimitive) where

import Data.Functor ((<$>))
import Control.Monad ((<=<))
import Control.Arrow ((>>>))
import qualified Data.Map as M

import HERMIT.Core (localFreeIdsExpr)
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure -- hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary hiding (externals)

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
observing = False

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
reifyOf e = appsE reifyS [exprType e] [e]

evalOf :: CoreExpr -> TransformU CoreExpr
evalOf e = appsE evalS [dropEP (exprType e)] [e]

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
              Just (a,b) <- constT (return (splitFunTy_maybe (exprType u)))
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
              appsE "lamvP#" [varType v, exprType e] [varLitE v,e']

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

-- TODO: Perhaps combine reifyPolyLet and reifyMonoLet into reifyLet

-- The simplifyE is for beta-reducing type applications.

-- Rewrite inside of reify applications
inReify :: Unop ReExpr
inReify = reifyR <~ unReify

#if 0
reifyRuleNames :: [String]
reifyRuleNames = map ("reify/" ++)
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

-- Apply a rule to a left application prefix
reifyRulesPrefix :: ReExpr
reifyRulesPrefix = reifyRules <+ (reifyApp >>> appArgs reifyRulesPrefix idR)

-- Like appAllR, but on a reified app.
-- 'app ta tb f x --> 'app ta tb (rf f) (rx s)'
appArgs :: Binop ReExpr
appArgs rf rx = appAllR (appAllR idR rf) rx

#endif

-- reify (I# n) --> intL (I# n)
reifyIntLit :: ReExpr
reifyIntLit = unReify >>> do _ <- callNameT "I#"
                             e <- idR
                             appsE "intL" [] [e]

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

reifyPrim :: ReExpr
reifyPrim =
  unReify >>>
  do Var v@(varName -> qualifiedName -> flip M.lookup primMap -> Just nm) <- idR
     appsE1 "kPrimEP" [varType v] =<< Var <$> findIdP nm

miscL :: [(String,ReExpr)]
miscL = [ ("reifyEval"        , reifyEval)
--         , ("reifyRulesPrefix" , reifyRulesPrefix)
        , ("reifyApp"         , reifyApp)
        , ("reifyLam"         , reifyLam)
        , ("reifyMonoLet"     , reifyMonoLet)
        , ("reifyTupCase"     , reifyTupCase)
        , ("reifyCast"        , reifyCast)
        , ("reifyIntLit"      , reifyIntLit)
        , ("reifyPrim"        , reifyPrim)
        ]

reifyMisc :: ReExpr
reifyMisc = triesL miscL

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

findIdP :: String -> TransformH a Id
findIdP = findIdT . primName

primName :: Unop String
primName = ("LambdaCCC.Prim." ++)

primMap :: M.Map String String
primMap = M.fromList
  [ ("GHC.Classes.&&","AndP")
  , ("GHC.Classes.||","OrP")
  , ("GHC.Classes.not","NotP")
  , ("GHC.Num.$fNumInt_$c+","AddP")
  , ("GHC.Num.$fNumInt_$c*","MulP")
  ]

{-
not      --> kPrim NotP
(&&)     --> kPrim AndP
(||)     --> kPrim OrP
xor      --> kPrim XorP
(+)      --> kPrim AddP
(*)      --> kPrim MulP
fst      --> kPrim ExlP
snd      --> kPrim ExrP
(,)      --> kPrim PairP
Left     --> kPrim InlP
Right    --> kPrim InrP
condBool --> kPrim CondBP

()       --> kLit  ()
False    --> kLit  False
True     --> kLit  True
-}

-- TODO: make primitives a map to expressions, to use during reification. Or
-- maybe a transformation that succeeds only for primitives, since we'll have to
-- look up IDs. We'll see.

isPrimitive :: Var -> Bool
isPrimitive v = qualifiedName (varName v) `M.member` primMap
