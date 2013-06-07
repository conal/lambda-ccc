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

-- TODO: explicit exports

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
import Language.HERMIT.Core (Crumb(..))
import Language.HERMIT.Context (HermitC,HermitBindingSite(LAM),hermitC_bindings)

-- import LambdaCCC.CCC
import LambdaCCC.FunCCC  -- Function-only vocabulary

-- TODO: Switch to real CCC vocabulary and revisit the types of mkCurry etc
-- below. The type parameters may change order.

import CLasH.Utils.Core.CoreShow ()

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

unhandledT :: Show a => a -> Translate c HermitM a b
unhandledT e = fail $ "Not yet handled: " ++ show e

-- TODO: Use one of HERMIT's pretty-printers instead of CLasH's Show.

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)

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

-- TODO: Discard types returned from unTuple and unPair, since they're easy to
-- reconstruct.

unType :: CoreExpr -> Type
unType (Type t) = t
unType _ = error "unType: not a type"

-- curry :: forall a b c. (a :* b :-> c) -> (a :-> b :=> c)

-- mkCurry :: Id -> RewriteH CoreExpr
-- mkCurry curryId = do
--     f <- observeR "mkCurry f"
--     (ab,c) <- maybe (fail "mkCurry splitFunTy") return $ splitFunTy_maybe $ exprType f
--     (tc,[a,b]) <- maybe (fail "mkCurry splitTyConApp") return $ splitTyConApp_maybe ab 
--     dflags <- constT getDynFlags
--     constT $ liftIO $ do
--         putStrLn $ showPpr dflags ab
--         putStrLn $ showPpr dflags c
--         putStrLn $ showPpr dflags tc
--         putStrLn $ showPpr dflags a
--         putStrLn $ showPpr dflags b
--         return ()
--     guardMsg (isTupleTyCon tc) "mkCurry: tycon is not a tuple tycon"
--     return $ apps curryId [a,b,c] [f]


-- mkCurry :: Id -> Unop CoreExpr
-- mkCurry curryId f = apps curryId [a,b,c] [f]
--  where
--    FunTy (unPairTy -> Just (a,b)) c = exprType f

mkCurry :: Id -> Unop CoreExpr
mkCurry curryId f = apps curryId [a,b,c] [f]
 where
   -- (unPairTy -> Just (a,b),c) = splitFunTy (exprType f)
   (ab,c) = splitFunTy (exprType f)
   Just (a,b) = unPairTy ab



-- apply :: forall a b. ((a :=> b) :* a) :-> b

-- mkApply :: Id -> Unop CoreExpr
-- mkApply applyId f = apps applyId [a,b] [f]
--  where
--    (unPairTy -> Just (FunTy a b, _a)) = exprType f

-- const :: forall b a. b :-> (a :=> b)

mkConst :: Id -> Type -> Unop CoreExpr
mkConst constId a x = apps constId [exprType x,a] [x]

-- (.) :: forall b c a. (b :-> c) -> (a :-> b) -> (a :-> c)

-- mkCompose :: Id -> Binop CoreExpr
-- mkCompose compId g f = apps compId [b,c,a] [g,f]
--  where
--    FunTy b  c = exprType g
--    FunTy a _b = exprType f

-- fst :: forall a b. a :* b :-> a
-- snd :: forall a b. a :* b :-> b
-- (.) :: forall b c a. (b :-> c) -> (a :-> b) -> (a :-> c)

-- compFst :: forall b b' c. (b :-> c) -> (b :* b' :-> c)
-- compSnd :: forall b b' c. (b' :-> c) -> (b :* b' :-> c)

mkCompFst :: Id -> Type -> CoreExpr -> Maybe CoreExpr
mkCompFst compFstId b' f = do
    (b,c) <- splitFunTy_maybe $ exprType f
    return $ apps compFstId [b,b',c] [f]

-- TODO: Use compId and fstId to define compFst

-- applyComp :: forall a b c. (a :-> (b :=> c)) -> (a :-> b) -> (a :-> c)

mkApplyComp :: Id -> Binop CoreExpr
mkApplyComp applyCompId f g = apps applyCompId [a,b,c] [f,g]
    where ([a,b],c) = splitFunTysN 2 $ exprType f

-- TODO: Use applyId and compId to define mkApplyComp

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
         Translate c m CoreExpr a1 -> Translate c m CoreExpr a2
      -> (a1 -> a2 -> b) -> Translate c m CoreExpr b
pairT t1 t2 f = translate $ \ c ->
  \ case (unPair -> Just (e1,e2)) ->
           f <$> Kure.apply t1 (c @@ Alt_Var 0) e1
             <*> Kure.apply t2 (c @@ Alt_Var 1) e2
         _         -> fail "not a pair node."

-- TODO: Revisit choice of crumb. I could use something App_Fun @@ App_Arg and
-- App_Arg.

-- Just the lambda-bound variables in a HERMIT context
lambdaVars :: HermitC -> [Var]
lambdaVars = map fst . filter (isLam . snd . snd) . M.toList . hermitC_bindings
 where
   isLam LAM = True
   isLam _   = False

-- | Extract just the lambda-bound variables in a HERMIT context
lambdaVarsT :: Monad m => Translate HermitC m a [Var]
lambdaVarsT = contextonlyT (return . lambdaVars)


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

selectVar :: (Id,Id) -> Id -> LContext -> Maybe CoreExpr
selectVar (compFstId,sndId) x cxt0 = select cxt0 (cxtType cxt0)
 where
   select :: LContext -> Type -> Maybe CoreExpr
   select []     _    = Nothing
   select (v:vs) cxTy = do 
        -- - <- tr (return cxTy)
        (tc, [a,b]) <- splitTyConApp_maybe cxTy
        -- _ <- tr (return a)
        -- _ <- tr (return $ varName sndId)
        -- _ <- tr (return b)
        guardMsg (isTupleTyCon tc) "select: not a tuple tycon"
        if v == x
            then return (apps sndId [a,b] []) 
            else mkCompFst compFstId b =<< select vs a

-- Unsafe way to ppr in pure code.
tr :: Outputable a => a -> a
tr x = trace ("tr: " ++ showPpr tracingDynFlags x) x

-- Given comp, fst & snd ids, const, a variable, translate the variable in the context.
findVar :: (Id,Id) -> Id -> LContext -> Id -> CoreExpr
findVar compFstSndId constId cxt x =
  fromMaybe (mkConst constId (cxtType cxt) (Var x))
            (selectVar compFstSndId x cxt)

-- TODO: Inspect and test findVar carefully.

type Recore  = RewriteH CoreExpr

convert :: Recore
convert =
  do curryId     <- findIdT 'curry
     constId     <- findIdT 'const
     sndId       <- findIdT 'snd
     compFstId   <- findIdT 'compFst
     applyCompId <- findIdT 'applyComp
     ampId       <- findIdT '(&&&)
     applyUnitId <- findIdT 'applyUnit
     let rr :: Recore
         rr = do c <- lambdaVarsT
                 observeR (printf "rr: %s" (showContext c)) >>= \_ -> 
                    -- NB Pair before App
                    tries [("Var",rVar),("Pair",rPair),("App",rApp),("Lam",rLam)]
          where
            try label rew = rew >>> observeR label
            tries :: [(String,Recore)] -> Recore
            tries = foldr (<+) (observeR "Other" >>> fail "unhandled")
                  . map (uncurry try)
         rVar, rPair, rApp, rLam :: Recore
         rVar  = do cxt <- lambdaVarsT
                    varT $ findVar (compFstId,sndId) constId cxt
         rPair = pairT rr rr (mkAmp ampId)
         rApp  = appT  rr rr (mkApplyComp applyCompId)
         rLam  = lamT  rr (const (mkCurry curryId))

     mkApplyUnit applyUnitId <$> rr

--      appId     <- findIdT 'apply
--      compId    <- findIdT '(.)
--      fstId     <- findIdT 'fst

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "lambda-to-ccc" (promoteExprR convert)
        [ "top level lambda->CCC transformation, first version" ]
    , external "expr-type" (promoteExprT exprTypeT)
        [ "get the type of the current expression" ]
    ]

exprTypeT :: TranslateH CoreExpr String
exprTypeT = arr exprType >>> ppT
