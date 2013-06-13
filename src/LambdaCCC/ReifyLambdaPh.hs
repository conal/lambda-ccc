{-# LANGUAGE TemplateHaskell, TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
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

module LambdaCCC.ReifyLambdaPh where

-- TODO: explicit exports

import Data.Functor ((<$>))
import GHC.Pack (unpackCString#)
import Text.Printf (printf)
import Debug.Trace
import Data.List (intercalate)

import GhcPlugins
import TypeRep (Type(..))
import Var
import PrelNames (unpackCStringUtf8Name,unpackCStringName)

-- TODO: Pare down
import Language.HERMIT.Monad (HermitM,liftCoreM)
import Language.HERMIT.External
import Language.HERMIT.Kure hiding (apply)
import qualified Language.HERMIT.Kure as Kure
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.GHC (uqName,var2String)
import Language.HERMIT.Primitive.Unfold (cleanupUnfoldR)
import Language.HERMIT.Primitive.GHC (rule)
import Language.HERMIT.Core (Crumb(..),Core) -- ,CoreDef(..)
import Language.HERMIT.Context (HermitBindingSite(LAM),ReadBindings(..))

import LambdaCCC.Misc (Unop)
import qualified LambdaCCC.LambdaPh as E

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps _ [t] _ | trace (printf "apps: t==%s" (pretty t)) False = error "kownT"
apps _ _ [e] | trace (printf "apps: e==%s" (pretty e)) False = error "kownE"  -- BOMBS!
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d arguments but got %d."
                     (var2String f) arity ntys
  | trace (printf "apps #tys==%d, #vals==%d" (length ts) (length es)) False = error "wonk?"
  | trace (printf "apps %s %s %s"
            (var2String f) "Q" "R" {-(pretties ts) (pretties es)-})
          False = error "urk??"
  | trace (printf "apps: %s has arity %d" (var2String f) arity) False = error "urk?"
  | otherwise = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)
 where
   arity = tyArity f
   ntys  = length ts

-- apps f ts0 es = mkCoreApps (mkTApps (exprType e0) e0 ts0) es
--  where
--    e0 = varToCoreExpr f
--    -- Check that we have few enough type arguments.
--    -- TODO: also check that we don't have too few.
--    mkTApps :: Type -> CoreExpr -> [Type] -> CoreExpr
--    mkTApps (ForAllTy {}) _ [] = oops "few"
--    mkTApps _  e [] = e
--    mkTApps ty e ts | Just ty' <- coreView ty = mkTApps ty' e ts
--    mkTApps ty@(ForAllTy {}) e (t:ts') =
--      mkTApps (applyTy ty t) (App e (Type t)) ts'
--    mkTApps _ _ (_:_) = oops "many"
--    oops x = error (printf "mkCoreTyApps: Too %s type args for %s"
--                           x (var2String f))

tyArity :: Id -> Int
tyArity = length . fst . splitForAllTys . varType

-- Unsafe way to ppr in pure code.
tr :: Outputable a => a -> a
tr x = trace ("tr: " ++ pretty x) x

pretty :: Outputable a => a -> String
pretty = showPpr tracingDynFlags

pretties :: Outputable a => [a] -> String
pretties = intercalate "," . map pretty

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- reify :: a -> E a
-- reify = error "reify: not implemented."

reifyCoreExpr :: RewriteH CoreExpr
reifyCoreExpr =
  do varId     <- findIdT 'E.var
     appId     <- findIdT '(E.:^)
     lamvId    <- findIdT 'E.lamv
     -- varString <- varToStringLitE' <$> findIdT 'unpackCString#
     -- unpackId  <- findIdT 'unpackCString#
     -- unpackId <- constT (lookupId unpackCStringName)
     unpackId <- constT (lookupId unpackCStringUtf8Name)
     let varString = varToStringLitE' unpackId
     let reifyE :: Unop CoreExpr
         reifyE e | tr e `seq` False = undefined
         reifyE (Var v) = trace (printf "Var %s :: %s" (var2String v) (pretty (varType v))) $
                          trace ("varId == " ++ var2String varId) $
                          trace ("unpackId/seq: " ++ (unpackId `seq` "HNF okay")) $  -- CRASH!
                          trace ("unpackId == " ++ var2String unpackId) $   -- CRASH!
                          trace (printf "varString %s == " (var2String v)) $
                          trace (printf "%s" (pretty (varString v))) $  -- BOMBS!
                          -- trace (printf "varString %s == %s" (var2String v) (pretty (varString v))) $
                          let e' = apps varId [varType v] [varString v] in
                            trace (printf "e' == %s" (pretty e')) e'
         reifyE (Lit _) = error "reifyE: Lit not handled"
         reifyE (App u v@(Type{})) = App (reifyE u) v
         -- TODO: Pairs
         reifyE (App u v) = apps appId [a,b] [reifyE u, reifyE v]
          where
            (a,b) = splitFunTy (exprType u)
         reifyE (Lam v e) | isTyVar v = Lam v (reifyE e)
                          | otherwise = apps lamvId [varType v, exprType e]
                                                    [varString v,reifyE e]
         reifyE _ = error "reifyE: incomplete"
     reifyE <$> idR


-- mkStringExpr is hanging for some reason, so for now I'm just creating
-- (type-incorrect) unboxed strings (NS)
varToStringLitE :: Var -> CoreExpr
-- varToStringLitE = mkStringExpr . var2String
varToStringLitE = Lit . mkMachString . var2String

-- mkStringExpr :: MonadThings m => String -> m CoreExpr  -- Result :: String

stringLitE' :: Id -> String -> CoreExpr
stringLitE' unpackId = App (Var unpackId) . Lit . mkMachString

varToStringLitE' :: Id -> Var -> CoreExpr
varToStringLitE' unpackId = stringLitE' unpackId . var2String



{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "reify-core" (promoteExprR reifyCoreExpr)
        [ "Turn a Core expression into a GADT construction" ]
    ]
