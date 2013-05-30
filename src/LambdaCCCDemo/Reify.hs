module LambdaCCCDemo.Reify where

import GhcPlugins

import qualified Language.Haskell.TH as TH

import Control.Arrow
import Control.Applicative
import Control.Monad

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.GHC
import Language.HERMIT.External
import Language.HERMIT.Primitive.Common

----------------------------------------------------

externals ::  [External]
externals = [ external "reify" (promoteExprR reifyR :: RewriteH Core)
                [ "reify a core expression into the Expr GADT"
                ] .+ Experiment
            ]

----------------------------------------------------

reifyR :: RewriteH CoreExpr
reifyR =  do evalId   <- findEmbeddingId "eval"
             compileE <- findEmbeddingE "compile"
             varE     <- findEmbeddingE "var"
             appE     <- findEmbeddingE "app"
             lamE     <- findEmbeddingE "lam"
             withPatFailMsg (wrongExprForm "App (App 'eval ty) e") $
               do App (App (Var eval) (Type _)) _ <- idR
                  guardMsg (eval == evalId) "cannot reify: not an evaluation of an expression."
                  let reifyR'  :: RewriteH CoreExpr
                      reifyR'  =  varT (\ i -> mkCoreApp varE (varToStringLitE i))
                               <+ appT reifyR' reifyR' (\ e1 e2 -> mkCoreApps appE [e1,e2])
                               <+ lamT reifyR' (\ v e -> mkCoreApps lamE [varToStringLitE v, e])
                   in appAllR (return compileE) reifyR'

-- For now (for testing purposes), just use the variable name.
-- varToStringLitE :: MonadThings m => Var -> m CoreExpr
-- varToStringLitE =  mkStringExpr . var2String

-- mkStringExpr is hanging for some reason, so for now I'm just creating (type-incorrect) unboxed strings
varToStringLitE :: Var -> CoreExpr
varToStringLitE =  Lit . mkMachString . var2String

----------------------------------------------------

embeddingModule :: String
embeddingModule = "Embedding"

type FunctionName = String

findEmbeddingE :: FunctionName -> TranslateH a CoreExpr
findEmbeddingE s = findEmbeddingId s >>^ varToCoreExpr

findEmbeddingId :: FunctionName -> TranslateH a Id
findEmbeddingId s = findIdT (TH.mkName (embeddingModule ++ "." ++ s))

----------------------------------------------------
