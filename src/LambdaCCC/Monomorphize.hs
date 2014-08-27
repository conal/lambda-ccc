{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE OverloadedStrings #-}  -- for HermitName literals
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Monomorphize
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Monomorphization plugin
----------------------------------------------------------------------

module LambdaCCC.Monomorphize where

-- TODO: explicit exports

import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.))
import Data.Functor ((<$>),void)
import Control.Applicative ((<*>))
-- import Control.Monad (unless)
import Data.List (isPrefixOf)

import HERMIT.Core (CoreDef(..))
import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External,external)
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Plugin (hermitPlugin,pass,interactive)

import HERMIT.Extras hiding (findTyConT)
import qualified HERMIT.Extras as Ex

-- import LambdaCCC.CoerceEncode
import LambdaCCC.ReifySimple

{--------------------------------------------------------------------
    Observing
--------------------------------------------------------------------}

observing :: Ex.Observing
observing = False

-- #define LintDie

#ifdef LintDie
watchR, nowatchR :: String -> Unop ReExpr
watchR lab r = lintingExprR lab (labeled observing (lab,r)) -- hard error

#else
-- watchR :: String -> Unop ReExpr
-- watchR lab r = labeled observing (lab,r) >>> lintExprR  -- Fail softly on core lint error.
watchR, nowatchR :: Injection a CoreTC => String -> RewriteH a -> RewriteH a
watchR lab r = labeled observing (lab,r)  -- don't lint

#endif

-- nowatchR = watchR
nowatchR _ = id

skipT :: Monad m => Transform c m a b
skipT = fail "untried"

{--------------------------------------------------------------------
    HERMIT tools
--------------------------------------------------------------------}

-- Tighten the type of (>>). (Alternatively, choose a different operator.)
infixl 1 >>
(>>) :: Monad m => m () -> m b -> m b
(>>) = (Prelude.>>)

-- Turn filters into conditional identities and vice versa.
-- Is this functionality already in HERMIT?

passT :: Monad m => Transform c m a () -> Rewrite c m a
passT t = t >> id

unpassT :: Functor m => Rewrite c m a -> Transform c m a ()
unpassT r = fmap (const ()) r

-- | case e of { Con -> rhs }  ==>  rhs
-- Warning: can gain definedness when e == _|_.
caseNoVarR :: ReExpr
caseNoVarR =
  do Case _ _ _ [(DataAlt _,[],rhs)] <- id
     return rhs

bragMemo :: Bool
bragMemo = False

-- Memoize a transformation. Don't introduce a let binding (for later floating),
-- which would interfere with additional simplification.
memoR :: Outputable a => Unop (TransformH a CoreExpr)
memoR r = do lab <- stashLabel
             findDefT bragMemo lab
               <+ do e' <- r
                     saveDefNoFloatT bragMemo lab $* e'
                     return e'

-- Memoize and float if non-trivial
memoFloatR :: Outputable a => String -> Unop (TransformH a CoreExpr)
memoFloatR lab r = do findDefT bragMemo lab
                        <+ do e' <- r
                              if exprIsTrivial e' then
                                do saveDefNoFloatT bragMemo lab $* e'
                                   return e'
                               else
                                do v <- newIdT lab' $* exprType' e'
                                   saveDefT bragMemo lab $* Def v e'
                                   letIntroR lab' $* e'
 where
   lab' = tweak lab
   tweak = -- fst . break (== '$')
           -- ("s:" ++) . fst . break (== '_')
           fst . break (== '_')
           -- const "x"
           -- id

-- TODO: Refactor

memoFloatLabelR :: Outputable a => Unop (TransformH a CoreExpr)
memoFloatLabelR r = do lab <- stashLabel
                       memoFloatR lab r

filterToBool :: MonadCatch m => Transform c m a () -> Transform c m a Bool
filterToBool t = (t >> return True) <+ return False

-- -- Build a dictionary for a given PredType.
-- memoDict :: TransformH PredType CoreExpr
-- memoDict = memoR buildDictionaryT'

{--------------------------------------------------------------------
    Monomorphization
--------------------------------------------------------------------}

-- Unfold a name applied to some type and/or dictionary arguments
specializeTyDict :: ReExpr
specializeTyDict =
    tryR simplifyAll
  . unfoldPredR okay
  . rejectR (dictResultTy . exprType)
  . rejectR isType
 where
   okay = -- const $ liftA2 (&&) (not.null) (all isTyOrDict)
          -- (\ v args -> isGlobalId v && not (isPrimitive v) && all isTyOrDict args)
          (\ v args -> not (isPrimitive v)
                    && all isTyOrDict args
                    && (isGlobalId v || not (null args)))
          -- const $ all isTyOrDict

#if 1
dictResultTy :: Type -> Bool
dictResultTy (coreView -> Just ty) = dictResultTy ty
dictResultTy (FunTy _ ty)          = dictResultTy ty
dictResultTy (ForAllTy _ ty)       = dictResultTy ty
dictResultTy ty                    = isDictTy ty
#else
dictResultTy :: Type -> Bool
dictResultTy = isDictTy . resultTy

resultTy :: Unop Type
resultTy (coreView -> Just ty) = resultTy ty
resultTy (FunTy _ ty)          = resultTy ty
resultTy (ForAllTy _ ty)       = resultTy ty
resultTy ty                    = ty
#endif

isTyOrDict :: CoreExpr -> Bool
isTyOrDict e = isType e || isDictTy (exprType e)

monomorphize :: ReExpr
monomorphize = memoFloatLabelR (repeatR specializeTyDict)

-- | case c of { False -> a'; True -> a }  ==>  if_then_else c a a'
-- Assuming there's a HasIf instance.
rewriteIf :: ReExpr
rewriteIf = do Case c _wild ty [(_,[],a'),(_,[],a)] <- id
               guardMsg (isBoolTy (exprType c)) "scrutinee not Boolean"
               hasIfTc <- findTyConT (lamName "HasIf")
               dict    <- buildDictionaryT' $* TyConApp hasIfTc [ty]
               apps' (lamName "if_then_else") [ty] [dict,c,a,a']

{--------------------------------------------------------------------
    Simplification
--------------------------------------------------------------------}

replaceBash :: Bool
replaceBash = True

bashWith :: [ReExpr] -> ReExpr
bashWith
  | replaceBash = \ rs -> bashUsingE (promoteR <$> (rs ++ bashSimplifiers))
  | otherwise   = \ rs -> bashExtendedWithE (promoteR <$> rs)

simplifyAll :: ReExpr
simplifyAll = -- watchR "simplifyAll" $
              bashWith mySimplifiers

extraSimplifiers :: [ReExpr]
extraSimplifiers =
  [ letSubstOneOccR
  -- Experiment
  , watchR "standardizeCase" standardizeCase
  , watchR "standardizeCon" standardizeCon
  ]  

fullSimpliers :: [ReExpr]
fullSimpliers = mySimplifiers ++ extraSimplifiers

simplifyAll' :: ReExpr
simplifyAll' = -- watchR "simplifyAll'" $
               bashWith fullSimpliers

mySimplifiers :: [ReExpr]
mySimplifiers = [ castFloatAppUnivR    -- or castFloatAppR'
                , castCastR
                , castTransitiveUnivR
                , letSubstTrivialR  -- instead of letNonRecSubstSafeR
             -- , letSubstOneOccR -- delay
                -- Previous two lead to nontermination. Investigate.
--                 , watchR "recastR" recastR -- Experimental
                , nowatchR "caseReduceUnfoldsDictR" caseReduceUnfoldsDictR
                , caseDefaultR
                , reprAbstR
                , watchR "rewriteIf" rewriteIf
                ]

-- From bashComponents.
bashSimplifiers :: [ReExpr]
bashSimplifiers =
  [ nowatchR "betaReduceR" betaReduceR
  , nowatchR "(caseReduceR True)" (caseReduceR True)
  , nowatchR "(caseReduceUnfoldR True)" (caseReduceUnfoldR True)
  , nowatchR "caseElimSeqR" caseElimSeqR
  , nowatchR "unfoldBasicCombinatorR" unfoldBasicCombinatorR
  , nowatchR "inlineCaseAlternativeR" inlineCaseAlternativeR
  , nowatchR "etaReduceR" etaReduceR
  -- letNonRecSubstSafeR was replicating some monomorphic method
  -- specializations.
  -- , nowatchR "letNonRecSubstSafeR" letNonRecSubstSafeR
  , nowatchR "caseFloatAppR" caseFloatAppR
  , nowatchR "caseFloatCaseR" caseFloatCaseR
  , nowatchR "caseFloatLetR" caseFloatLetR
  , nowatchR "caseFloatCastR" caseFloatCastR  -- Watch this one
  , nowatchR "letFloatAppR" letFloatAppR
  , nowatchR "letFloatArgR" letFloatArgR
  , nowatchR "letFloatLamR" letFloatLamR
  , nowatchR "letFloatLetR" letFloatLetR
  , nowatchR "letFloatCaseR" letFloatCaseR
  , nowatchR "letFloatCastR" letFloatCastR
  , nowatchR "castElimReflR" castElimReflR
  , nowatchR "castElimSymR" castElimSymR
  ]

-- TODO: Trim redundant let floating. See passCore and passE.

-- | Given a case scrutinee of non-standard type, case-reduce the whole
-- expression, or unfold the scrutinee. Warning: can be quite expensive and
-- generate a lot of code. Use only in special circumstances, e.g., dictionaries.
caseReduceUnfoldsR :: ReExpr
caseReduceUnfoldsR =
  caseReduceR True . onScrutineeR (repeatR (tryR simplifyAll' . unfoldR))

caseReduceUnfoldsDictR :: ReExpr
caseReduceUnfoldsDictR =
  void (onScrutineeR (acceptR (isDictTy . exprType))) >> caseReduceUnfoldsR

simplifyAllRhs :: ReProg
simplifyAllRhs = progRhsAnyR simplifyAll

simplifyAllRhs' :: ReProg
simplifyAllRhs' = progRhsAnyR simplifyAll'

simplifyAllBind' :: ReBind
simplifyAllBind' = nonRecAllR id simplifyAll'

letFloatCaseAltR' :: ReExpr
letFloatCaseAltR' = letFloatCaseAltR Nothing

letFloatR :: ReCore
letFloatR = promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR')

-- pruneAltsProg :: ReProg
-- pruneAltsProg = progRhsAnyR ({-bracketR "pruneAltsR"-} pruneAltsR)

-- case scrut wild of p -> body ==> [wild := scrut] body, when p has no free
-- variables where the wildcard variable isn't used. If wild is a dead Id, don't
-- bother substituting.
caseDefaultR :: ReExpr
caseDefaultR =
  do Case scrut wild _ [(_,[],body)] <- id
     return $ case idOccInfo wild of
                IAmDead -> body
                _       -> Let (NonRec wild scrut) body

retypeProgR :: ReProg
retypeProgR = progRhsAnyR ({-bracketR "retypeExprR"-} retypeExprR)

-- NOTE: if unshadowR is moved to later than pruneAltsProg, we can prune too
-- many alternatives. TODO: investigate.

passE :: ReExpr
passE = id
      . tryR (watchR "simplifyAll" simplifyAll)  -- after let floating
      . tryR (anybuE (letFloatExprR <+ letFloatCaseAltR'))
      . tryR (anybuE (letAllR bindUnLetIntroR id))
--       . tryR (watchR "retypeExprR" retypeExprR) -- Needed?
      . tryR (extractR unshadowR)
      . tryR simplifyAll'
--       . tryR (anytdE (repeatR (  watchR "standardizeCase" standardizeCase
--                               <+ watchR "standardizeCon" standardizeCon)))
      . onetdE (watchR "monomorphize" monomorphize)

-- TODO: Find a much more efficient strategy. I think repeated onetdE is very
-- expensive. I went this way to help memoization. Revisit!

-- | 'letSubstR' in non-recursive let if only one occurrence.
letSubstOneOccR :: ReExpr
letSubstOneOccR = oneOccT >> letNonRecSubstR

-- standardizeR' :: (Standardizable a, SyntaxEq a, Injection a CoreTC) => RewriteH a
-- standardizeR' = watchR "standardizeR" $
--                 standardizeR

{--------------------------------------------------------------------
    Yet another go at standardizing types
--------------------------------------------------------------------}

isStandardTy :: Type -> Bool
isStandardTy t = any ($ t) [isUnitTy,isBoolTy,isIntTy,isPairTy]

closedType :: Type -> Bool
closedType = isEmptyVarSet . tyVarsOfType

hasRepMethodF :: TransformH Type (String -> TransformH a CoreExpr)
hasRepMethodF =
  do ty <- id
     -- The following check avoids a problem in buildDictionary.
     guardMsg (closedType ty) "Type has free variables"
     hasRepTc <- findTyConT (repName "HasRep")
     dict  <- buildDictionaryT' $* TyConApp hasRepTc [ty]
     repTc <- findTyConT (repName "Rep")
     (mkEqBox -> eq,ty') <- normaliseTypeT Nominal $* TyConApp repTc [ty]
     return $ \ meth -> apps' (repName meth) [ty] [dict,Type ty',eq]

hasRepMethodT :: TransformH Type (String -> ReExpr)
hasRepMethodT = (\ f -> \ s -> App <$> f s <*> id) <$> hasRepMethodF

-- | e ==> abst (repr e).  In Core, abst is
-- abst ty $hasRepTy ty' (Eq# * ty' (Rep ty) (sym (co :: Rep ty ~ ty'))),
-- where e :: ty, and co normalizes Rep ty to ty'.
abstReprR :: ReExpr
abstReprR = do meth <- hasRepMethodT . exprTypeT
               meth "abst" . meth "repr"

-- Do one unfolding, and then a second one only if the function name starts with
-- "$", as in the case of a method lifted to the top level.
unfoldMethodR :: ReExpr
unfoldMethodR =
    tryR (tryR simplifyAll . unfoldPredR (\ v _ -> isPrefixOf "$" (uqVarName v)))
  . (tryR simplifyAll . unfoldR)

-- unfoldMethodR = repeatR (tryR simplifyAll . unfoldR)

standardizeCase :: ReExpr

-- standardizeCase =
--     tryR (caseReduceR True <+ caseFloatCaseR)
--   . onScrutineeR (unfoldMethodR . {- watchR "abstReprR" -} abstReprR)

standardizeCase =
     caseReduceR True
  <+ caseReduceUnfoldR True
  <+ caseFloatCaseR
  <+ onScrutineeR (unfoldMethodR . watchR "abstReprR" abstReprR)

onScrutineeR :: Unop ReExpr
onScrutineeR r = caseAllR r id id (const id)

standardizeCon :: ReExpr
standardizeCon = go . rejectR isType
 where
   -- Handle both saturated and unsaturated constructors
   go =  (appAllR id unfoldMethodR . (void callDataConT >> abstReprR))
      <+ (lamAllR id standardizeCon . etaExpandR "eta")

-- etaExpandR dies on Type t. Avoided via rejectR isType

-- -- | Replace a cast expression with a recast application.
-- recastR :: ReExpr
-- recastR = do Cast e (coercionKind -> Pair a b) <- id
--              classTc <- findTyConT ("LambdaCCC.Recastable.Recastable")
--              dict    <- buildDictionaryT' $* TyConApp classTc [a,b]
--              apps' ("LambdaCCC.Recastable.recast") [a,b] [dict,e]

-- Try again without a Recastable class.

-- | Construct a recast function from a to b
recastF :: Type -> Type -> TransformH a CoreExpr
recastF (regularizeType -> a) (regularizeType -> b) =
  idRC <+ reprR <+ abstR <+ funR <+ oopsR
 where
    idRC  = do guardMsg (a =~= b) "recast id: types differ"
               idId <- findIdT "id"
               return $ Var idId `App` Type a
    reprR = tryMeth a "repr"
    abstR = tryMeth b "abst"
    tryMeth ty meth = do q <- hasRepMethodF $* ty
                         f <- q meth
                         Just (a',b') <- return (splitFunTy_maybe (exprType f))
--                          str <- showPprT $* ((a,b),(a',b'))
--                          _ <- traceR ("tryMeth " ++ meth ++ ", types: " ++ str)
                         guardMsg (a' =~= a) "recast tryMeth: a' /= a"
                         guardMsg (b' =~= b) "recast tryMeth: b' /= b"
                         return f
    funR = do Just (aDom,aRan) <- return $ splitFunTy_maybe a
              Just (bDom,bRan) <- return $ splitFunTy_maybe b
              f <- recastF bDom aDom  -- contravariant
              h <- recastF aRan bRan  -- covariant
              glueV <- findIdT "LambdaCCC.Monomorphize.-->"
              -- return $ 
              unfoldR $*
                       mkApps (Var glueV)
                              ([Type aDom,Type aRan,Type bDom,Type bRan, f,h])
    oopsR = do str <- showPprT $* (a,b)
               _ <- traceR ("recastF unhandled: " ++ str)
               fail "oopsR"

-- guardMsg' ::  Bool -> String -> TransformH a ()
-- guardMsg' b msg = unless b (do { _ <- traceR msg ; fail msg})

-- | Add pre- and post-processing.
-- Used dynamically by recastF
(-->) :: forall a b a' b'. (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f

-- | Replace a cast expression with the application of a recasting function
recastR :: ReExpr
recastR = do Cast e (coercionKind -> Pair a b) <- id
             f <- recastF a b
             return (App f e)

-- | repr (abst x)  ==>  x, when type preserving.
reprAbstR :: ReExpr
reprAbstR =
  do (_,[Type ty ,_,_,_,e]) <- callNameT (repName "repr")
     (_,[Type ty',_,_,_,x]) <- callNameT (repName "abst") $* e
     guardMsg (regularizeType ty =~= regularizeType ty')
       "reprAbstR: differing types"
     return x

{--------------------------------------------------------------------
    Combine steps
--------------------------------------------------------------------}

-- TODO: Move elsewhere

reifyPrep :: ReExpr
reifyPrep = inReify (
                id
              . tryR unshadowE
              . tryR simplifyAll'
              . tryR (anytdE (watchR "recastR" recastR))             -- Experimental
              . tryR (repeatR ({- watchR "passE" -} passE))
              )
        -- . tryR (unfoldNameR "LambdaCCC.Run.go")

-- I tried moving standardizeCase and standardizeCon into mySimplifiers (used by
-- simplifyAll'), and it appears to loop. To do: investigate. Meanwhile, do it here.

-- TODO: The initial inlineR is probably inadequate. Instead, fix the inlining
-- criterion in specializeTyDict.

doReify :: ReExpr
doReify = tryR unshadowE
        . tryR bashE
        . repeatR (anytdE (repeatR reifyMisc))

compileGo :: ReExpr
compileGo = doReify . reifyPrep


-- Move to HERMIT.Extras
unshadowE :: ReExpr
unshadowE = extractR unshadowR

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (pass 0 . interactive externals)

externals :: [External]
externals =
    [ externC "simplifyAll" simplifyAll "Bash with normalization simplifiers (no inlining)"
    , externC "simplifyAll'" simplifyAll' "simplifyAll plus letSubstOneOccR"
    , externC "simplifyAllRhs" simplifyAllRhs "simplify-all on all top-level RHSs"
    , externC "simplifyAllRhs'" simplifyAllRhs' "simplify-all' on all top-level RHSs"
    , externC "simplifyAllBind'" simplifyAllBind' "simplify-all' on all binding RHS"
    , externC "specializeTyDict" specializeTyDict "..."
    , externC "bindUnLetIntroR" bindUnLetIntroR "..."
    , externC "letFloatCaseAltR'" letFloatCaseAltR' "..."
    , externC "monomorphize" monomorphize "..."
    , externC "passE" passE "..."
    , externC "letSubstOneOccR" letSubstOneOccR "..."
--     , externC "standardizeExpr" (standardizeR' :: ReExpr) "..."
--     , externC "standardizeProg" (standardizeR' :: ReProg) "..."
--     , externC "standardizeBind" (standardizeR' :: ReBind) "..."
    -- Put it together
    , externC "reify-prep" reifyPrep "..."
    , externC "do-reify" doReify "..."
    , externC "compile-go" compileGo "..."
    -- TEMP:
    , externC "recast" recastR "..."
    , externC "abstRepr" abstReprR "..."
    , externC "standardizeCase" standardizeCase "..."
    , externC "standardizeCon" standardizeCon "..."
    , externC "caseReduceUnfoldsR" caseReduceUnfoldsR "..."
    , externC "caseDefaultR" caseDefaultR "..."
    , externC "reprAbstR" reprAbstR "..."
    , externC "unfoldMethodR" unfoldMethodR "..."
    , externC "rewriteIf" rewriteIf "..."
    -- From Reify.
    , externC "reify-misc" reifyMisc "Simplify 'reify e'"
    , externC "reifyEval" reifyEval "..."
    , externC "reifyRepMeth" reifyRepMeth "..."
    , externC "reifyApp" reifyApp "..."
    , externC "reifyLam" reifyLam "..."
    , externC "reifyMonoLet" reifyMonoLet "..."
    , externC "reifyTupCase" reifyTupCase "..."
    , externC "reifyLit" reifyLit "..."
    , externC "reifyPrim" reifyPrim "..."
    -- 
    , external "let-float'"
        (promoteR letFloatTopR <+ promoteR (letFloatExprR <+ letFloatCaseAltR')
         :: RewriteH Core)
        ["let-float with letFloatCaseAltR"]
--     , externC "pruneAltsR" pruneAltsR "..."
--     , externC "pruneAltsProg" pruneAltsProg "..."
    , externC "retypeExprR" retypeExprR "..."
    , externC "retypeProgR" retypeProgR "..."
    , externC "simplify-expr" simplifyExprR "Invoke GHC's simplifyExpr"
    , externC "cast-float-app'" castFloatAppR' "cast-float-app with transitivity"
    , externC "castFloatAppUnivR" castFloatAppUnivR "cast-float-app with coercion cheating"
    , externC "case-wild" caseWildR "case of wild ==> let (doesn't preserve evaluation)"
    , externC "cast-cast" castCastR "..."
    , externC "cast-transitive-univ" castTransitiveUnivR "..."
    ]
