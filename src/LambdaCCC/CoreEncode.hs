{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.CoreEncode
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Transform away all non-standard types
----------------------------------------------------------------------

module LambdaCCC.CoreEncode where

-- TODO: explicit exports
import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.),(>>>))
import Control.Arrow (arr)
import Control.Monad (unless)
import Data.Functor ((<$),(<$>))
import Control.Applicative (liftA2)
import Data.Monoid (mempty)
import Data.List (intercalate)
import qualified Data.Set as S

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Core (CoreDef(..),CoreProg)
import HERMIT.Dictionary hiding (externals) -- re-exports HERMIT.Dictionary.*
import HERMIT.External (External,ExternalName,external,(.+),CmdTag(Loop))
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad (saveDef,newIdH,Label)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT)
import qualified HERMIT.Extras as Ex

import LambdaCCC.Misc ((<~))

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

-- Tighten the type of (>>). (Alternatively, choose a different operator.)
infixl 1 >>
(>>) :: Monad m => m () -> m b -> m b
(>>) = (Prelude.>>)

-- | case e of { Con -> rhs }  ==>  rhs
-- Warning: can gain definedness when e == _|_.
caseNoVarR :: ReExpr
caseNoVarR =
  do Case _ _ _ [(DataAlt _,[],rhs)] <- id
     return rhs

#define Memo

#ifdef Memo

-- Build a dictionary for a given PredType, memoizing in the stash.
memoDict :: TransformH PredType CoreExpr
memoDict = -- traceR "memoDict" .
           do lab <- stashLabel
              findDef True lab
                <+ do dict <- buildDictionaryT'
                      -- Stash if non-trivial
                      ((isVarT $* dict) >> return dict)
                       <+ do v <- newIdT lab
                             constT (saveDef lab (Def v dict))
                             return (Let (NonRec v dict) (Var v))

-- Memoize a transformation. Don't introduce a let binding (for later floating),
-- which would interfere with additional simplification.
memoR :: Unop ReExpr
memoR r = do lab <- stashLabel
             findDef True lab
               <+ do e' <- r
                     saveDefNoFloat lab e'
                     return e'

#else

zoink

memoDict :: TransformH PredType CoreExpr
memoDict = buildDictionaryT'

memoR :: Unop ReExpr
memoR = id

#endif

-- | 'betaReduceR' but using 'castFloatAppR'' if needed to reveal a redex.
betaReduceCastR :: ReExpr
betaReduceCastR = castFloatAppR' >>> castAllR betaReduceR id

-- | Combine `castFloatLamR` and `castCastR`
castLamCastR :: ReExpr
castLamCastR = castAllR castLamsFloatR id >>> castCastR

-- | Float a cast through nested lambdas
castLamsFloatR :: ReExpr
castLamsFloatR = tryR (lamAllR id castLamsFloatR) >>> castFloatLamR

-- | (\ x :: a -> e)  ==>
--   cast (\ x' :: a' -> e[x:= cast x' (sym co)]) (co -> <b>)
-- where all of the occurrences of x in e look like cast x' co.
lamCastVarR :: ReExpr
lamCastVarR =
  anytdE castElimSymR .
  do Lam x body <- id
     Just co <- return (castOccsSame x body)
     let co' = mkSymCo co
     x' <- constT $ newIdH (uqVarName x ++ "'") (pSnd (coercionKind co))
     let sub = subst [(x, Var x' `mkCast` co')]
     return $
       Lam x' (sub body) `mkCast`
         mkFunCo repr co' (mkReflCo repr (exprType' body))

-- | Combine `lamCastVarR` and `castCastR`
lamCastVarCastR :: ReExpr
lamCastVarCastR = castAllR lamCastVarR id >>> castCastR

-- An alternative to lamCastVarR

-- | (\ x -> e)  ==>  (\ x' -> e [x := x' `cast` sym co]) `cast` (sym co -> <b>)
-- where :: a, e :: b, normalizeTypeT r a --> (co,a'), x' :: a'
lamNormalizeVarR :: Role -> ReExpr
lamNormalizeVarR r =
  do Lam x e <- id
     guardMsg (not (isTyVar x)) "lamNormalizeVarR: type lambda"
     let a = varType  x
     (co,a') <- normalizeTypeT r $* a
     guardMsg (not (isReflCo co)) "lamNormalizeVarR: already normal"
#if 0
     aStr  <- showPprT $* a
     aStr' <- showPprT $* a'
     _ <- traceR ("lamNormalizeVarR: " ++ aStr ++ " --> " ++ aStr')
#endif
     let co' = mkSymCo co
     x' <- constT $ newIdH (uqVarName x ++ "'") a'
     return $
       Lam x' (subst [(x, Var x' `mkCast` co')] e)
        `mkCast` (mkFunCo r co' (mkReflCo r (exprType e)))

-- | \ x :: () -> f (e :: ())  ==>  f
etaReduceUnitR :: ReExpr

etaReduceUnitR =
  do Lam x (App e x') <- id
     unless (isUnitTy ( varType x )) $
       do tyStr <- showPprT $* varType x
          fail $ "etaReduceUnitR: Bound variable of type " ++ tyStr
     guardMsg (isUnitTy (exprType x')) "etaReduceUnitR: Argument not of unit type"
     return e

-- etaReduceUnitR =
--   do Lam x (App e x') <- id
--      guardMsg (isUnitTy ( varType x )) "etaReduceUnitR: Bound variable not of unit type"
--      guardMsg (isUnitTy (exprType x')) "etaReduceUnitR: Argument not of unit type"
--      return e

-- etaReduceUnitR =
--   lamT (acceptR (isUnitTy . varType))
--        (appT id (notM isTypeE >> acceptR (isUnitTy . exprType)) const)
--        (flip const)

-- | (co -> co') ==> (co,co')
unFunCo_maybe :: Coercion -> Maybe (Coercion,Coercion)
unFunCo_maybe (TyConAppCo _r t [co,co']) | isFunTyCon t = Just (co,co')
-- Cheat:
unFunCo_maybe _                                         = Nothing

-- | (\ x -> e) `cast` (co -> co')  ==>
--   (\ x' -> e [x := x' `cast` sym co] `cast` co')
castIntoLamR :: ReExpr
castIntoLamR = do Lam x e `Cast` (unFunCo_maybe -> Just (co,co')) <- id
                  x' <- constT (newIdH (uqVarName x ++ "'") (coercionDom co))
                  let e' = subst [(x, Var x' `mkCast` SymCo co)] e
                  return $ Lam x' (e' `mkCast` co')

-- | (\ a -> e) `cast` (forall a. co)  ==>  (\ a -> e `cast` co)
castIntoTyLamR :: ReExpr
castIntoTyLamR =
  do Lam a e `Cast` ForAllCo a' co <- id
     let e' | a == a'   = e
            | otherwise = subst [(a, Var a')] e
     return $
       Lam a' (e' `mkCast` co)

-- | u v `cast` co  ==>  (u `cast` (refl -> co)) v
castIntoAppR :: ReExpr
castIntoAppR = do ty <- exprTypeT
                  App u v `Cast` co <- id
                  let role  = coercionRole co
                      funCo = mkFunCo role (mkReflCo role ty) co
                  return $ App (u `mkCast` funCo) v

coercionDom, coercionRan :: Coercion -> Type
coercionDom = pFst . coercionKind
coercionRan = pSnd . coercionKind

-- | (let b in e) `cast` co  ==>  let b in e `cast` co
castIntoLetR :: ReExpr
castIntoLetR =
  do Let b e `Cast` co <- id
     return $ Let b (e `mkCast` co)

-- | cast (case s of p -> e) co ==> case s of p -> cast e co
-- (Alias for 'caseFloatCastR')
castIntoCaseR :: ReExpr
castIntoCaseR = caseFloatCastR

-- | (,) ta' tb' (a `cast` coa) (b `cast` cob)  ==>
--   (,) ta tb a b `cast` coab
--  where `coa :: ta ~R ta'`, `cob :: tb ~R tb'`, and
--  `coab :: (ta,tb) ~R (ta',tb')`.
castIntoPairR :: ReExpr
castIntoPairR =
  do ab' <- unPairR
     case ab' of
       (Cast a coa,Cast b cob) ->
         return $
           Cast (mkCoreTup [a,b])
                (mkTyConAppCo repr pairTyCon [coa,cob])
       (a,Cast b cob) ->
         return $
           Cast (mkCoreTup [a,b])
                (mkTyConAppCo repr pairTyCon [refl a,cob])
       (Cast a coa,b) ->
         return $
           Cast (mkCoreTup [a,b])
                (mkTyConAppCo repr pairTyCon [coa,refl b])
       _ -> fail "castIntoPairR pair of non-casts"
 where
   refl = mkReflCo repr . exprType

-- TODO: Refactor
-- TODO: Do I always want repr here?

-- | Move cast into an expression
castIntoR :: ReExpr
castIntoR = isCastE >>  -- optimization
  orR [ watchR "castIntoPairR"  castIntoPairR
--       , watchR "castIntoAppR"   castIntoAppR
      , watchR "castIntoLamR"   castIntoLamR
      , watchR "castIntoTyLamR" castIntoTyLamR
      , watchR "castIntoLetR"   castIntoLetR
      , watchR "castIntoCaseR"  castIntoCaseR
      , watchR "castCastR"      castCastR
      ]

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

-- (Observing, observeR', triesL, labeled)

observing :: Ex.Observing
observing = False

-- #define LintDie

#ifdef LintDie
watchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error
#else
-- watchR lab r = labeledR lab r >>> lintExprR  -- Fail softly on core lint error.
watchR :: Injection a CoreTC =>
          String -> RewriteH a -> RewriteH a
watchR lab r = labeled observing (lab,r)  -- don't lint
#endif

skipT :: Monad m => Transform c m a b
skipT = fail "untried"

{--------------------------------------------------------------------
    Triviality
--------------------------------------------------------------------}

-- | Trivial expression: for now, literals, variables, casts of trivial.
trivialExpr :: FilterE
trivialExpr = setFailMsg "Non-trivial" $
              isTypeE <+ isVarT <+ isLitT
           <+ trivialLam
           <+ castT trivialExpr id mempty

trivialBind :: FilterH CoreBind
trivialBind = nonRecT successT trivialExpr mempty

trivialLet :: FilterE
trivialLet = letT trivialBind successT mempty

trivialLam :: FilterE
trivialLam = lamT id trivialExpr mempty

trivialBetaRedex :: FilterE
trivialBetaRedex = appT trivialLam successT mempty

-- These filters could instead be predicates. Then use acceptR.

letElimTrivialR :: ReExpr
letElimTrivialR = -- watchR "trivialLet" $
                  trivialLet >> letSubstR

betaReduceTrivial :: ReExpr
betaReduceTrivial = -- watchR "betaReduceTrivial" $
                    trivialBetaRedex >> betaReduceR

{--------------------------------------------------------------------
    Working with LambdaCCC.Encode
--------------------------------------------------------------------}

encName :: Unop String
encName = ("LambdaCCC.Encode." ++)

findTyConE :: String -> TransformH a TyCon
findTyConE = findTyConT . encName

appsE :: String -> [Type] -> [CoreExpr] -> TransformU CoreExpr
appsE = apps' . encName

-- A handy form for composition via <=< or =<<
appsE1 :: String -> [Type] -> CoreExpr -> TransformU CoreExpr
appsE1 str ts e = appsE str ts [e]

-- TODO: Try switching from TransformU

-- | Uncall a named function
unCallE :: String -> TransformH CoreExpr [CoreExpr]
unCallE = unCall . encName

-- | Uncall a named function
unCallE1 :: String -> ReExpr
unCallE1 = unCall1 . encName

-- | Uncall a named function of one dictionary and one other argument, dropping
-- the dictionary.
unCallD1 :: String -> ReExpr
unCallD1 f = do [_d,e] <- unCall f
                return e

unCallDE1 :: String -> ReExpr
unCallDE1 = unCallD1 . encName

oneOccT :: FilterE
oneOccT =
  do Let (NonRec v _) body <- id
     guardMsg (varOccCount v body <= 1) "oneOccT: multiple occurrences"

-- | 'letSubstR' in non-recursive let if there's just one occurrence of the
-- bound variable
letSubstOneOccR :: ReExpr
letSubstOneOccR = oneOccT >> letSubstR

{--------------------------------------------------------------------
    Super inlining
--------------------------------------------------------------------}

superInlineR :: ReExpr
superInlineR = watchR "superInlineR" $
               anytdE (repeatR inlineR')

-- superInlineR = watchR "superInlineR" $
--                bashUsingE (inlineR' : simplifiers)

inlineR' :: ReExpr
inlineR' = watchR "inlineR" inlineR

superInlineSimplifyR :: ReExpr
superInlineSimplifyR = -- bracketR "superInlineSimplifyR" $
                       memoR $
                       tryR (anytdE unshadowExprR) . simplifyAll . superInlineR

-- TODO: remove the unshadowing later

{--------------------------------------------------------------------
    Standard types
--------------------------------------------------------------------}

-- TODO: Parametrize the rest of the module by 'standardTyT'.

-- TODO: Consider how to eliminate Encode as well. Then simplify to
-- standardTy :: Type -> Bool

-- A "standard type" is built up from `Unit`, `Bool`, `Int` (for now), pairs (of
-- standard types), sums, and functions, or Encode

standardTyT :: FilterTy
standardTyT =
     tyConAppT (acceptR standardTC) (const standardTyT) mempty
  <+ (funTyT standardTyT standardTyT mempty)
  <+ (standardTyT . tcViewT)
  <+ fail "standardTyT: not"

-- standardTyT (tcView -> Just ty) = standardTyT ty
-- standardTyT (TyConApp tc args) | standardTC tc
--                                = mapM_ standardTyT args
-- standardTyT ty@(TyConApp tc _) =
--   -- Treat Encode applications as standard.
--   do encodeTC <- findTyConT "LambdaCCC.Encode.Encode"
--      if tc == encodeTC then successT else nonStandardFail ty
-- standardTyT (FunTy arg res) =
--   standardTyT arg >> standardTyT res
-- standardTyT ty = nonStandardFail ty

standardTC :: TyCon -> Bool
standardTC tc =
     (tc `elem` [unitTyCon, boolTyCon, intTyCon])
  || isPairTC tc
  || tyConName tc == eitherTyConName    -- no eitherTyCon

nonStandardFail :: FilterTy
nonStandardFail =
  do s <- showPprT
     fail ("non-standard type:\n" ++ s)

nonStandardTyT :: FilterTy
nonStandardTyT = notM standardTyT

nonStandardE :: FilterE
nonStandardE = isTypeE <+ (nonStandardTyT . arr exprType')

-- TODO: Maybe I just want a standard outer shell.

-- TODO: Maybe use coreView instead of tcView? I think it's tcView we want,
-- since it just looks through type synonyms and not newtypes.

-- TODO: If I remove Encode, standardTy can be Type -> Bool

{--------------------------------------------------------------------
    Simple Encode/Encodable wrapping/unwrapping
--------------------------------------------------------------------}

tyConApp1 :: TyCon -> Type -> Type
tyConApp1 tc t = TyConApp tc [t]

tyConAppE1 :: String -> ReType
tyConAppE1 name = do tc <- findTyConE name
                     arr (tyConApp1 tc)

-- t ==> Encode t
encodeTyR :: ReType
encodeTyR = tyConAppE1 "Encode"

-- t ==> Encodable t
encodableR :: ReType
encodableR = tyConAppE1 "Encodable"

encodeDictT :: TransformH Type CoreExpr
encodeDictT = memoDict . encodableR
-- encodeDictT = buildDictionaryT' . encodableR

encodeR :: ReExpr
encodeR = -- nonStandardE >>
          do e <- idR
             let ty = exprType e
             dict <- encodeDictT $* ty
             appsE "encode" [ty] [dict,e]

decodeR :: ReExpr
decodeR = cleanupUnfoldR .
          appAllR squashCode id .
          do e    <- idR
             ty   <- unEncodeTy $* exprType e
             dict <- encodeDictT $* ty
             appsE "decode" [ty] [dict,e]

-- recodeR :: ReExpr
-- recodeR = do e <- idR
--              let ty = exprType e
--              dict <- encodeDictT $* ty
--              appsE "recode" [ty] [dict,e]

-- TODO: refactor, and consider making apps' and apps1' into non-U transforms.

-- Alternatively,

-- | e ==> recode e ==> decode (encode e), and inline & simplify decode.
recodeR :: ReExpr
recodeR = -- watchR "recodeR" $
          decodeR . encodeR

-- inlineDecodeR :: ReExpr
-- inlineDecodeR = appAllR (isDecode >> squashCode) id

-- -- | e ==> recode e, with a simplified type-specialized recode
-- recodeSquashR :: ReExpr
-- recodeSquashR = watchR "recodeSquashR" $
--                 nonStandardE >>
--                 (recodeR >>> appAllR squashCode id)

-- encode a ==> a
unEncode :: ReExpr
unEncode = unCallDE1 "encode"
-- decode b ==> b
unDecode :: ReExpr
unDecode = unCallDE1 "decode"

-- encode (decode e) ==> e
encodeDecode :: ReExpr
encodeDecode = unEncode >>> unDecode

-- isEncode :: Type -> Bool
-- isEncode (TyConApp (tyConName -> name) [_]) = uqName name == "encode"
-- isEncode _                                  = False

unEncodeTy :: ReType
unEncodeTy =
  tyConApp1T (acceptR ((== "Encode") . uqName . tyConName)) id (const id)

-- Rewrite inside of encode applications
inEncode :: Unop ReExpr
inEncode = encodeR <~ unEncode

-- Avoid constructing a new dictionary
-- inEncode r =
--   unEncode >>
--   appAllR id (appAllR id (appAllR id r))  -- encode t dict e

-- -- | Recognize encode with type and dictionary arguments.
-- isEncode :: FilterE
-- isEncode = unEncode >>> mempty

squashCode :: ReExpr
squashCode =
  do (_,[_ty,_dict])
       <- callPredT (flip (const ((`elem` squashNames) . fqVarName)))
     superInlineR
 where
   squashNames = encName <$> [ "encode","decode","recode" ]

{--------------------------------------------------------------------
    Encode transformations
--------------------------------------------------------------------}

-- | Is a variable applied to zero or more types and dictionaries
isVarTyDictAppsT :: FilterE
isVarTyDictAppsT =
  setFailMsg "not a variable applied to types and dictionaries" $
  isVarT <+ appT isVarTyDictAppsT (isTypeE <+ isDictE) mempty

-- isVarTyDictAppsT = do { (Var _,_,[]) <- callSplitT ; return () }

isPrim :: Id -> Bool
isPrim = flip S.member primNames . uqVarName
 where
   primNames :: S.Set String
   primNames = S.fromList
     [ "not", "||" ]  -- for now

-- TODO: Add prims
-- TODO: Use fqVarName

encodeVar :: ReExpr
encodeVar = (unEncode >>> isVarTyDictAppsT) >>
            appAllR superInlineSimplifyR
                    id
                    -- (tryR (unfoldPredR (flip (const (not . isPrim)))))

-- encodeVar =
--   inEncode $
--     do (Var _,_,[]) <- callSplitT
--        unfoldR >>> tryR simplifyAll

-- | encode (u v)  ==> (encode u `cast` (Encode a -> Encode b)) (encode v)
-- where u :: a -> b, v :: a.
encodeDistribApp :: ReExpr
encodeDistribApp =
  do encB <- exprTypeT  -- Encode b
     unEncode >>>
       appT encodeR encodeR (\ encU encV ->
         let encA = exprType' encV
             -- Coerce encU from Encode (ta -> tb) to (Encode ta -> Encode tb).
             co = mkUnivCo repr
                    (exprType' encU) (mkFunTy encA encB)
           in
             App (Cast encU co) encV)

encodeLamR :: ReExpr
encodeLamR = (unEncode >>> lamT id id mempty) >>
             (cleanupUnfoldR . appAllR squashCode id)

-- TODO: Use legit coercion.

-- unfolds :: ReExpr
-- unfolds = watchR "unfolds" $
--           unfoldNamesR $
--   encName <$> ["encode","recode","recode","(-->)"] ++
--   []

-- TODO: For more flexibility, split the transformation in two pieces:
-- 
--    (,) ta' tb (a `cast` coa) b ==> (,) ta tb a b `cast` coab
-- 
-- where `coa :: ta ~R ta'`, and `coab :: (ta,tb) ~R (ta',tb)`.
-- Similarly for tb'.

-- mkTyConAppCo :: Role -> TyCon -> [Coercion] -> Coercion

-- callNameT :: MonadCatch m => String -> Transform c m CoreExpr (CoreExpr, [CoreExpr])

-- | case e of alts  ==>  case recode e of alts
-- Warning, can loop. Must simplify.
recodeScrutineeR :: ReExpr
recodeScrutineeR = caseAllR recodeR id id (const id)

-- caseAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m)
--          => Rewrite c m CoreExpr
--          -> Rewrite c m Id
--          -> Rewrite c m Type
--          -> (Int -> Rewrite c m CoreAlt)
--          -> Rewrite c m CoreExpr

{--------------------------------------------------------------------
    Put it together
--------------------------------------------------------------------}

encoders :: [ReExpr]
encoders =
  [ watchR "encodeVar" encodeVar
  , watchR "encodeDistribApp" encodeDistribApp
  , watchR "encodeLamR" encodeLamR
  -- , watchR "recodeScrutineeR" recodeScrutineeR
  ] 

oneEncode :: ReExpr
oneEncode = orR encoders -- >>> simplifyAll

encodePass :: ReCore
encodePass = watchR "encodePass" $
             anytdR (promoteR oneEncode)

-- simplifyOne :: ReExpr
-- simplifyOne = orR simplifiers
-- -- simplifyOne = foldr (<+) (fail "standardize: nothing to do here") simplifiers

#define UseBash

simplifyAll :: ReExpr

simplifiers :: [ReExpr]
simplifiers =
  [ watchR "letElimTrivialR" letElimTrivialR
  -- , watchR "betaReduceTrivial" betaReduceTrivial
  , watchR "letElimR" letElimR   -- removed unused bindings after inlining
  , watchR "letSubstOneOccR" letSubstOneOccR
  -- , watchR "caseReduceR" (caseReduceR False)  -- let rather than subst  ??
  -- , watchR "castFloatCaseR" castFloatCaseR
  , watchR "etaReduceUnitR" etaReduceUnitR
  , watchR "caseNoVarR" caseNoVarR
  , watchR "inlineWorkerR" inlineWorkerR
  -- Casts
--   , castIntoR

  , watchR "castCastR" castCastR
  , watchR "castIntoPairR" castIntoPairR
  , watchR "castLamCastR" castLamCastR
  , watchR "castFloatAppR'" castFloatAppR'

  , watchR "lamNormalizeVarR" (lamNormalizeVarR repr)

--   , watchR "lamCastVarR" lamCastVarR  -- loops with castLamCastR. specialize.
--  , watchR "lamCastVarCastR" lamCastVarCastR
  -- , watchR "castFloatLamR" castFloatLamR
  , watchR "betaReduceCastR" betaReduceCastR
  -- , watchR "lamFloatCastR" lamFloatCastR

  ]
#ifndef UseBash
  ++ bashSimplifiers

-- From bashComponents.
bashSimplifiers :: [ReExpr]
bashSimplifiers =
  [ watchR "betaReduceR" betaReduceR
  , watchR "(caseReduceR True)" (caseReduceR True)
  , watchR "(caseReduceIdR True)" (caseReduceIdR True)
  , watchR "caseElimSeqR" caseElimSeqR
  , watchR "unfoldBasicCombinatorR" unfoldBasicCombinatorR
  , watchR "inlineCaseAlternativeR" inlineCaseAlternativeR
  , watchR "etaReduceR" etaReduceR
  -- letNonRecSubstSafeR was undoing my dictionary `let` bindings.
  -- , watchR "letNonRecSubstSafeR" letNonRecSubstSafeR
  , watchR "caseFloatAppR" caseFloatAppR
  , watchR "caseFloatCaseR" caseFloatCaseR
  , watchR "caseFloatLetR" caseFloatLetR
  -- , watchR "caseFloatCastR" caseFloatCastR  -- Watch this one
  , watchR "letFloatAppR" letFloatAppR
  , watchR "letFloatArgR" letFloatArgR
  , watchR "letFloatLamR" letFloatLamR
  , watchR "letFloatLetR" letFloatLetR
  , watchR "letFloatCaseR" letFloatCaseR
  , watchR "letFloatCastR" letFloatCastR
  , watchR "castElimReflR" castElimReflR
  , watchR "castElimSymR" castElimSymR
  ]

simplifyAll = watchR "simplifyAll" $
              bashUsingE (promoteR <$> simplifiers)

#else

simplifyAll = watchR "simplifyAll" $
              bashExtendedWithE (promoteR <$> simplifiers)

#endif

simplifyOne :: ReExpr
simplifyOne = orR simplifiers
-- simplifyOne = foldr (<+) (fail "standardize: nothing to do here") simplifiers

simplifyAllRhs :: RewriteH CoreProg
simplifyAllRhs = progRhsAnyR simplifyAll

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals =
    [ externC "simplify-one" simplifyOne
        "Locally simplify for normalization, without inlining"
    , externC "simplify-all" simplifyAll "Bash with normalization simplifiers (no inlining)"
    , externC "simplify-all-rhs" simplifyAllRhs "simplify-all on all top-level RHSs"
    , externC "encode-pass" encodePass "a single top-down encoding pass"
    , externC "one-encode" oneEncode "a single encoding step"
    , externC "encode-distrib-app" encodeDistribApp
        "encode (u v) ==> (encode u) (encode v)"
    , externC "encode-lam" encodeLamR "Encode a lambda"
    , externC "encode-var" encodeVar "Encode a variable applied to zero or more types"
    , externC "unencode" unEncode "drop encode application"
    , externC "encode" encodeR "e ==> encode e"
    , externC "decode" decodeR "e ==> decode e"
    , externC "recode" recodeR "e ==> recode e"
    , externC "super-inline" superInlineR "Transitive inlining with bash"
    , externC "squash-code" squashCode "super-inline on encode-related"
--     , externC "unfolds" unfolds "Misc unfoldings for type encoding"
    , externC "recode-scrutinee" recodeScrutineeR "Recode case scrutinee"
--     , externC "beta-reduce-cast" betaReduceCastR 
--         "betaReduceR but using lamFloatCastR if needed to reveal a lambda."
    , externC "cast-lam-cast" castLamCastR "combine cast-float-lam and cast-cast"
    , externC "cast-lams-float" castLamsFloatR
       "Float a cast through nested lambdas"
    , externC "lam-cast-var" lamCastVarR "move casts from bound variables"
    , externC "lam-cast-var-cast" lamCastVarCastR
       "move casts from bound variables in lambda when cast"
    -- Move to HERMIT.Extras:
    , externC "eta-reduce-unit" etaReduceUnitR
        "\\ x :: () -> f (e :: ())  ==>  f"
    , externC "let-subst-one-occ" letSubstOneOccR
        "letSubstR if at most one occurrence"
    , externC "dump-stash" dumpStashR "Dump the stash into the program"
    , externC "drop-stashed-let" dropStashedLetR "..."
    , externC "cast-float-case" castFloatCaseR
        "Float cast upward through case. Inverse to 'caseFloatCastR', so don't use both rules!"
    , externC "cast-float-app'" castFloatAppR' "cast-float-app with transitivity"
    , externC "cast-cast" castCastR "Coalesce nested casts"
    , externC "un-cast-cast" unCastCastR "Uncoalesce to nested casts"
    , externC "lam-float-cast" lamFloatCastR "Float lambda through cast"
    , externC "cast-float-lam" castFloatLamR "Float cast through lambda"

    , externC "cast-into" castIntoR "Move cast into expression"
    , externC "cast-into-pair"  castIntoPairR "..."
    , externC "cast-into-app"   castIntoAppR "..."
    , externC "cast-into-lam"   castIntoLamR "..."
    , externC "cast-into-tylam" castIntoTyLamR "..."
    , externC "cast-into-let"   castIntoLetR "..."
    , externC "cast-into-case"  castIntoCaseR "..."

    , externC "lam-normalize-var" (lamNormalizeVarR repr) "..."

    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    , externC "case-wild" caseWildR "case of wild ==> let (doesn't preserve evaluation)"
    , external "repeat" (repeatN :: Int -> Unop (RewriteH Core))
       [ "Repeat a rewrite n times." ] .+ Loop
    ]
