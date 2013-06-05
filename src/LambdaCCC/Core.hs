{-# LANGUAGE ViewPatterns, PatternGuards, TemplateHaskell, LambdaCase #-}
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
import Control.Applicative (Applicative(..),liftA2)
import Control.Arrow ((>>>), arr)
import Control.Monad ((<=<))
import Data.Maybe (fromMaybe)
import Text.Printf (printf)

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

mkCurry :: Id -> RewriteH CoreExpr
mkCurry curryId = do
    f <- observeR "mkCurry f"
    (ab,c) <- maybe (fail "mkCurry splitFunTy") return $ splitFunTy_maybe $ exprType f
    (tc,[a,b]) <- maybe (fail "mkCurry splitTyConApp") return $ splitTyConApp_maybe ab 
    dflags <- constT getDynFlags
    constT $ liftIO $ do
        putStrLn $ showPpr dflags ab
        putStrLn $ showPpr dflags c
        putStrLn $ showPpr dflags tc
        putStrLn $ showPpr dflags a
        putStrLn $ showPpr dflags b
        return ()
    guardMsg (isTupleTyCon tc) "mkCurry: tycon is not a tuple tycon"
    return $ apps curryId [a,b,c] [f]

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

mkCompFst :: Id -> Unop CoreExpr
mkCompFst compFstId f = apps compFstId [b,b',c] [f]
 where
   FunTy _ (FunTy (unPairTy -> Just (b,b')) c) = exprType f

-- TODO: Use compId and fstId to define compFst

-- applyComp :: forall a b c. (a :-> (b :=> c)) -> (a :-> b) -> (a :-> c)

mkApplyComp :: Id -> Binop CoreExpr
mkApplyComp applyCompId f g = apps applyCompId [a,b,c] [f,g]
    where ([a,b],c) = splitFunTysN 2 $ exprType f

-- TODO: Use applyId and compId to define mkApplyComp

mkAmp :: Id -> Binop CoreExpr
mkAmp ampId f g = apps ampId [a,c,d] [f,g]
 where
   FunTy a  c = exprType f
   FunTy _a d = exprType g

-- TODO: consider some refactoring of mkXyz above

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

-- | Translate a pair expression.
pairT :: (PathContext c, Applicative m, Monad m) =>
         Translate c m CoreExpr a1 -> Translate c m CoreExpr a2
      -> (a1 -> a2 -> b) -> Translate c m CoreExpr b
pairT t1 t2 f = translate $ \ c ->
  \ case (unPair -> Just (e1,e2)) ->
           f <$> Kure.apply t1 (c @@ 0) e1 <*> Kure.apply t2 (c @@ 1) e2
         _         -> fail "not a pair node."

{--------------------------------------------------------------------
    Rewriting
--------------------------------------------------------------------}

-- | Lambda-bound variables, inner-first
type Context = [Id]

showContext :: Context -> String
showContext = show . map (uqName.varName)

-- "\ a b c " --> [c,b,a] --> ((a :* b) :* c) :* () ?
cxtType :: Context -> Type
cxtType = foldr (flip pairTy) unitTy . map varType

-- \ a b c --> [c,b,a] --> c :* (b :* (a :* ()))
-- cxtType :: Context -> Type
-- cxtType = foldr (pairTy . varType) unitTy

selectVar :: (Id,Id) -> Id -> Context -> Maybe CoreExpr
selectVar (compFstId,sndId) x cxt0 = select cxt0 (cxtType cxt0)
 where
   select :: Context -> Type -> Maybe CoreExpr
   select [] _                    = Nothing
   select (v:vs) cxTy | v == x    = Just {- to skip past this error and get to the mkCurry one (mkIntExpr 0) -} (apps sndId [a,b] [])
                      | otherwise = mkCompFst compFstId <$> select vs a
    where
      Just (a,b) = unPairTy cxTy

-- Given comp, fst & snd ids, const, a variable, translate the variable in the context.
findVar :: (Id,Id) -> Id -> Id -> Context -> CoreExpr
findVar compFstSndId constId x cxt =
  fromMaybe (mkConst constId (cxtType cxt) (Var x))
            (selectVar compFstSndId x cxt)

-- TODO: Inspect and test findVar carefully.

type Recore  = RewriteH CoreExpr
type RecoreC = Context -> Recore

convert :: Recore
convert =
  do curryId     <- findIdT 'curry
     constId     <- findIdT 'const
     sndId       <- findIdT 'snd
     compFstId   <- findIdT 'compFst
     applyCompId <- findIdT 'applyComp
     ampId       <- findIdT '(&&&)
     let rr :: RecoreC
         rr c = observeR (printf "rr: %s" (showContext c)) >>= \_ -> 
                   (rVar  c >>> observeR "Var")
                <+ (rPair c >>> observeR "Pair") -- NB: before App
                <+ (rApp  c >>> observeR "App")
                <+ (rLam  c >>> observeR "Lam")
                <+ (observeR "Other" >>> fail "only Var, App, Lam currently handled")

         rVar :: RecoreC
         rVar cxt = varT $ \ x -> findVar (compFstId,sndId) constId x cxt

         rPair :: RecoreC
         rPair cxt = pairT (rr cxt) (rr cxt) $ mkAmp ampId
         -- rPair _ = fail "rPair unimplemented"

         rApp :: RecoreC
         rApp cxt = appT (rr cxt) (rr cxt) $ \ u v -> mkApplyComp applyCompId u v
    
         rLam :: RecoreC
         rLam cxt = do 
            x <- lamT (pure ()) const 
            Lam _ b <- lamR (rr (x:cxt)) 
            applyInContextT (observeR "b") b
            tyStr <- applyInContextT exprTypeT b
            constT $ liftIO $ putStrLn tyStr
            applyInContextT (mkCurry curryId) b

     rr []
--         rew :: Context -> CoreExpr -> RewriteH CoreExpr
--         rew cxt (Var x  ) = do _ <- observeR "Var"
--                                pure $ findVar (compFstId,sndId) constId x cxt
--         rew cxt (unPair -> Just ((_,ea),(_,eb))) =
--           do _ <- observeR "Pair"
--              mkAmp ampId <$> rew cxt ea <*> rew cxt eb
--         rew cxt (App u v) = do _ <- observeR "App"
--                                mkApplyComp applyCompId <$> rew cxt u <*> rew cxt v
--         rew cxt (Lam x e) = do _ <- observeR "Lam"
--                                mkCurry curryId <$> rew (x : cxt) e
--         rew _   e         = do _ <- observeR "Other"
--                                return e   -- ???
         -- rew _   e         = unhandledT e
         -- rew _ _ = fail "convert: only Var, App, Lam currently handled"
--      in 
--        idR >>= rew []

--      appId     <- findIdT 'apply
--      compId    <- findIdT '(.)
--      fstId     <- findIdT 'fst

-- TODO: Rework rew with simpler types, and adapt from idR.

-- idR :: Monad m => Rewrite c m a
-- type Rewrite c m a = Translate c m a a
-- newtype Translate c m a b = Translate {apply :: c -> a -> m b}
-- instance Monad m => Monad (Translate c m a) where ...

-- rew [] :: CoreExpr -> HermitM CoreExpr
-- idR :: Rewrite c m CoreExpr
-- idR >>= rew [] :: Rewrite 

-- constT :: m b -> Translate c m a bSource



-- Redo using varT, appT, lamT:

type Convert = TranslateH CoreExpr (Context -> CoreExpr)

convert' :: Recore
convert' =
  do curryId     <- findIdT 'curry
     constId     <- findIdT 'const
     sndId       <- findIdT 'snd
     compFstId   <- findIdT 'compFst
     applyCompId <- findIdT 'applyComp
     let conv :: Convert
         conv = observeR "conv" >>= \ _ ->
                varT (findVar (compFstId,sndId) constId)
             <+ appT conv conv (liftA2 (mkApplyComp applyCompId))
--             <+ lamT conv (\ x u' cxt -> mkCurry curryId (u' (x : cxt)))
             <+ (idR >>= unhandledT)
     ($ []) <$> conv

-- TODO: Maybe use HERMIT's binding context rather than building one of my own.


{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = optimize (phase 0 . interactive externals)

externals :: [External]
externals =
    [ external "lambda-to-ccc" (promoteExprR convert)
        [ "top level lambda->CCC transformation, first version" ]
    , external "lambda-to-ccc'" (promoteExprR convert')
        [ "top level lambda->CCC transformation, second version" ]
    , external "expr-type" (promoteExprT exprTypeT)
        [ "get the type of the current expression" ]
    ]

exprTypeT :: TranslateH CoreExpr String
exprTypeT = arr exprType >>> ppT
