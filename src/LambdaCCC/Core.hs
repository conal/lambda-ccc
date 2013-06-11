{-# LANGUAGE ViewPatterns, PatternGuards, TemplateHaskell, LambdaCase #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Core
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
--
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
--
-- Core version of ToCCC.
-- With much help from Andrew Farmer and Neil Sculthorpe.
----------------------------------------------------------------------

module LambdaCCC.Core (plugin,externals) where

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..)) -- ,liftA2
import Control.Arrow ((>>>), arr)
import Control.Monad ((<=<))
import Data.Maybe (fromMaybe)
import Text.Printf (printf)
import qualified Data.Map as M

import GhcPlugins
import TypeRep (Type(..))

-- import qualified Language.Haskell.TH as TH

-- We really should make Language.HERMIT export everything
import Language.HERMIT.Monad (HermitM,liftCoreM)
import Language.HERMIT.External
import Language.HERMIT.Kure hiding (apply)
import qualified Language.HERMIT.Kure as Kure
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug (observeR)
import Language.HERMIT.GHC (uqName)
import Language.HERMIT.Primitive.Unfold (cleanupUnfoldR)
import Language.HERMIT.Primitive.GHC (rule)
import Language.HERMIT.Core (Crumb(..),CoreDef(..))
import Language.HERMIT.Context (HermitBindingSite(LAM),ReadBindings(..))

-- import LambdaCCC.CCC
import LambdaCCC.FunCCC  -- Function-only vocabulary

-- TODO: Switch to real CCC vocabulary and revisit the types of mkCurry etc
-- below. The type parameters may change order. Better yet, follow the
-- function-specific (FunCCC) phase with a generalization using something like
-- 'arr' to explicitly generalize from functions to morphisms.

{--------------------------------------------------------------------
    Misc utilities
--------------------------------------------------------------------}

type Unop  a = a -> a
type Binop a = a -> Unop a

ppCore :: Outputable a => a -> CoreM String
ppCore a = flip showPpr a <$> getDynFlags

ppH :: Outputable a => a -> HermitM String
ppH = liftCoreM . ppCore

ppT :: Outputable a => Translate c HermitM a String
ppT = contextfreeT ppH

-- unhandledT :: Outputable a => a -> Translate c HermitM a b
-- unhandledT e = ("Not yet handled: " ++) <$> ppT e >>= fail

-- unhandledT :: Show a => a -> Translate c HermitM a b
-- unhandledT e = fail $ "Not yet handled: " ++ show e

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)

-- Somewhat more informative error messages:

-- apps f ts0 es = mkCoreApps (mkTApps (exprType e0) e0 ts0) es
--  where
--    e0 = varToCoreExpr f
--    -- Check that we have few enough type arguments.
--    -- TODO: also check that we don't have too few.
--    mkTApps :: Type -> CoreExpr -> [Type] -> CoreExpr
--    mkTApps _  e [] = e
--    mkTApps ty e ts | Just ty' <- coreView ty = mkTApps ty' e ts
--    mkTApps ty@(ForAllTy {}) e (t:ts') =
--      mkTApps (applyTy ty t) (App e (Type t)) ts'
--    mkTApps _ _ (_:_) =
--      error (printf "mkCoreTyApps: Too many type args for %s"
--                    (uqName (varName f)))

tupleTy :: [Type] -> Type
tupleTy = mkBoxedTupleTy -- from TysWiredIn

unTupleTy :: Type -> Maybe [Type]
unTupleTy (TyConApp tc tys)
  | isTupleTyCon tc && tyConArity tc == length tys = Just tys
unTupleTy _ = Nothing

pairTy :: Binop Type
pairTy a b = tupleTy [a,b]

unPairTy :: Type -> Maybe (Type,Type)
unPairTy = listToPair <=< unTupleTy

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

mkCurry :: Id -> Unop CoreExpr
mkCurry curryId f = apps curryId [a,b,c] [f]
 where
   (unPairTy -> Just (a,b), c) = splitFunTy (exprType f)

-- apply :: forall a b. ((a :=> b) :* a) :-> b

-- mkApply :: Id -> Unop CoreExpr
-- mkApply applyId f = apps applyId [a,b] [f]
--  where
--    (unPairTy -> Just (FunTy a b, _a)) = exprType f

-- const :: forall b a. b :-> (a :=> b)

mkConst :: Id -> Type -> Unop CoreExpr
mkConst constId a x = apps constId [exprType x,a] [x]

-- (.) :: forall b c a. (b :-> c) -> (a :-> b) -> (a :-> c)

mkCompose :: Id -> Binop CoreExpr
mkCompose compId g f = apps compId [b,c,a] [g,f]
 where
   FunTy b  c = exprType g
   FunTy a _b = exprType f

-- fst :: forall a b. a :* b :-> a
-- snd :: forall a b. a :* b :-> b
-- (.) :: forall b c a. (b :-> c) -> (a :-> b) -> (a :-> c)

mkFst :: Id -> Type -> Type -> CoreExpr
mkFst fstId a b = apps fstId [a,b] []

mkSnd :: Id -> Type -> Type -> CoreExpr
mkSnd sndId a b = apps sndId [a,b] []

-- compFst :: forall b b' c. (b :-> c) -> (b :* b' :-> c)
-- compFst f = f . fst

mkCompFst :: Id -> Id -> Type -> Unop CoreExpr
mkCompFst composeId fstId b' f =
  apps composeId [b,c,b `pairTy`b'] [f, mkFst fstId b b']
 where
   (b,c) = splitFunTy (exprType f)

-- mkCompFst :: Id -> Type -> Unop CoreExpr
-- mkCompFst compFstId b' f = apps compFstId [b,b',c] [f]
--  where
--    (b,c) = splitFunTy (exprType f)

-- TODO: Use compId and fstId to define compFst

-- applyComp :: forall a b c. (a :-> (b :=> c)) -> (a :-> b) -> (a :-> c)

-- mkApplyComp :: Id -> Binop CoreExpr
-- mkApplyComp applyCompId f g = apps applyCompId [a,b,c] [f,g]
--     where
--       ([a,b],c) = splitFunTysN 2 (exprType f)

-- (&&&) :: forall a c d. (a :-> c) -> (a :-> d) -> (a :-> c :* d)
-- apply :: forall a b. (a :=> b) :* a :-> b
-- (.)   :: forall k b c a. (b :-> c) -> (a :-> b) -> (a :-> c)

-- applyComp :: forall a b c. (a :-> (b :=> c)) -> (a :-> b) -> (a :-> c)
-- applyComp h k = apply . (h &&& k)

-- apply :: (b :=> c) :* b :-> c
-- (.) :: ((b :=> c) :* b :-> c) -> (a :-> (b :=> c) :* b) -> (a :-> c)

mkApply :: Id -> Type -> Type -> CoreExpr
mkApply applyId a b = apps applyId [a,b] []

mkApplyComp :: (Id,Id,Id) -> Binop CoreExpr
mkApplyComp (applyId,composeId,ampId) f g =
  apps composeId
       [FunTy b c `pairTy` b, c, a]
       [mkApply applyId b c,mkAmp ampId f g]
    where
      ([a,b],c) = splitFunTysN 2 (exprType f)

-- Oh, weird. I get "too many type args for .", but I think I really have too
-- few. What's up? I'm using the Category version.
-- 
-- TODO: Switch to the Prelude version.
-- TODO: Maybe change back to applyComp and compFst.

mkAmp :: Id -> Binop CoreExpr
mkAmp ampId f g = apps ampId [a,c,d] [f,g]
 where
   ( a,c) = splitFunTy (exprType f)
   (_a,d) = splitFunTy (exprType g)

-- TODO: consider some refactoring of mkXyz above

mkApplyUnit :: Id -> Unop CoreExpr
mkApplyUnit applyUnitId e = apps applyUnitId [r] [e]
 where
   (_unit,r) = splitFunTy (exprType e)
   -- TODO: Check that _unit == Unit. How?

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

-- | Translate a pair expression.
pairT :: (Applicative m, Monad m, ExtendPath c Crumb) =>
         Translate c m CoreExpr a -> Translate c m CoreExpr b
      -> (a -> b -> z) -> Translate c m CoreExpr z
pairT ta tb f = translate $ \ c ->
  \ case (unPair -> Just (a,b)) ->
           f <$> Kure.apply ta (c @@ App_Fun @@ App_Arg) a
             <*> Kure.apply tb (c            @@ App_Arg) b
         _         -> fail "not a pair node."

-- Just the lambda-bound variables in a HERMIT context
lambdaVars :: ReadBindings c => c -> [Var]
lambdaVars = map fst . filter (isLam . snd . snd) . M.toList . hermitBindings
 where
   isLam LAM = True
   isLam _   = False

-- | Extract just the lambda-bound variables in a HERMIT context
lambdaVarsT :: (ReadBindings c, Applicative m) => Translate c m a [Var]
lambdaVarsT = contextonlyT (pure . lambdaVars)

retypeVar :: RewriteH Type -> RewriteH Var
retypeVar tr = translate $ \ c -> \ v ->
                 setVarType v <$> Kure.apply tr c (varType v)

-- Neil: We don't currently traverse into variables using generic traversals, so
-- it is not neccassary to add a Crumb to the context at this point. It's
-- possible this may change in the future though (in which case, retypeVar would
-- appear as a congruence combinator provided by HERMIT).

{-
   where
   crumb = error "retypeVar: what crumb to use?"
-}

{--------------------------------------------------------------------
    Rewriting
--------------------------------------------------------------------}

-- | Lambda-bound variables, inner-first
type LContext = [Id]

showContext :: LContext -> String
showContext = show . map (uqName.varName)

-- "\ a b c " --> [c,b,a] --> ((() :* a) :* b) :* c
cxtType :: LContext -> Type
cxtType = foldr (flip pairTy) unitTy . map varType

selectVar :: (Id,Id,Id) -> Id -> LContext -> Maybe CoreExpr
selectVar (composeId,fstId,sndId) x cxt0 = select cxt0 (cxtType cxt0)
 where
   select :: LContext -> Type -> Maybe CoreExpr
   select [] _   = Nothing
   select (v:vs) cxTy 
     | v == x    = Just (apps sndId [a,b] [])
     | otherwise = mkCompFst composeId fstId b <$> select vs a
    where
      Just (a,b) = unPairTy cxTy

-- -- Unsafe way to ppr in pure code.
-- tr :: Outputable a => a -> a
-- tr x = trace ("tr: " ++ showPpr tracingDynFlags x) x

-- Given compFst & snd ids, const id, and a lambda context, translate a
-- variable.

findVar :: (Id,Id,Id) -> Id -> LContext -> Id -> CoreExpr
findVar compFstSndId constId cxt x =
  fromMaybe (mkConst constId (cxtType cxt) (Var x))
            (selectVar compFstSndId x cxt)

-- findVar :: (Id,Id) -> Id -> LContext -> Id -> CoreExpr
-- findVar compFstSndId constId cxt x =
--   fromMaybe (mkConst constId (cxtType cxt) (Var x))
--             (selectVar compFstSndId x cxt)

convertExpr :: RewriteH CoreExpr
convertExpr =
  do curryId     <- findIdT 'curry
     constId     <- findIdT 'const
     composeId   <- findIdT '(Prelude..)
     fstId       <- findIdT 'fst
     sndId       <- findIdT 'snd
  -- compFstId   <- findIdT 'compFst
  -- applyCompId <- findIdT 'applyComp
     applyId     <- findIdT 'apply
     ampId       <- findIdT '(&&&)
     applyUnitId <- findIdT 'applyUnit
     let rr :: RewriteH CoreExpr
         rr = do c <- lambdaVarsT
                 observeR' (printf "rr: %s" (showContext c)) >>= \_ ->
                   -- NB Pair before App
                   tries [("Var",rVar),("Pair",rPair),("App",rApp),("Lam",rLam)]
          where
            tries :: [(String,RewriteH CoreExpr)] -> RewriteH CoreExpr
            tries = foldr (<+) (observeR' "Other" >>> fail "unhandled")
                  . map (uncurry try)
            try label rew = rew >>> observeR' label
         rVar, rPair, rApp, rLam :: RewriteH CoreExpr
         rVar  = do cxt <- lambdaVarsT
                    varT $ arr $ findVar (composeId,fstId,sndId) constId cxt
                                 -- findVar (compFstId,sndId) constId cxt
         rPair = pairT rr       rr $ mkAmp ampId
         rApp  = appT  rr       rr $ mkApplyComp (applyId,composeId,ampId)
                                     -- mkApplyComp applyCompId
         rLam  = lamT (pure ()) rr $ const (mkCurry curryId)

     mkApplyUnit applyUnitId <$> rr -- >>> observeR "Final"

observing :: Bool
observing = False

observeR' :: String -> RewriteH CoreExpr
observeR' | observing = observeR
          | otherwise = const idR

-- retypeVar :: RewriteH Type -> RewriteH Var

tweakTy :: RewriteH Type
tweakTy = idR                            -- for now

convertDef :: RewriteH CoreDef
convertDef = defAllR idR convertExpr
-- convertDef = defAllR (retypeVar (anybuR tweakTy)) convertExpr


{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "lambda-to-ccc" (promoteExprR convertExpr)
        [ "top level lambda->CCC transformation on expressions" ]
    , external "lambda-to-ccc-def" (promoteDefR convertDef)
        [ "top level lambda->CCC transformation on definitions" ]

--     , external "expr-type" (promoteExprT exprTypeT)
--         [ "get the type of the current expression" ]

    , external "unfold-rules" (promoteExprR . unfoldRules)
        [ "Apply a named GHC rule" ] .+ Deep .+ Context -- TODO: does not work with rules with no arguments

    ]

unfoldRules :: [String] -> RewriteH CoreExpr
unfoldRules nms = catchesM (rule <$> nms) >>> cleanupUnfoldR

exprTypeT :: TranslateH CoreExpr String
exprTypeT = arr exprType >>> ppT
