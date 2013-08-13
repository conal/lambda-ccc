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
                [ "reify a core expression of the form \"eval e\"",
                  "into a core expression of the form \"compile x\",",
                  "where \"x\" is a representation of the structure of \"e\"",
                  "using the \"Expr\" data type."
                ] .+ Experiment
            ]

----------------------------------------------------

reifyR :: RewriteH CoreExpr
reifyR =  do compileE <- findEmbeddingE "compile"
             varE     <- findEmbeddingE "var"
             appE     <- findEmbeddingE "app"
             lamE     <- findEmbeddingE "lam"
             withPatFailMsg (wrongExprForm "App (App 'eval ty) e") $
               do (_eval, (Type _):_) <- callNameT $ TH.mkName $ addEmbeddingModule "eval"
                  let reifyR'  :: RewriteH CoreExpr
                      reifyR'  =  varT (arr $ \ i -> mkCoreApp varE (varToStringLitE i))
                               <+ appT reifyR' reifyR' (\ e1 e2 -> mkCoreApps appE [e1,e2])
                               <+ lamT (arr varToStringLitE) reifyR' (\ v b -> mkCoreApps lamE [v, b])
                   in appAllR (return compileE) reifyR'

-- For now (for testing purposes), just use the variable name.
-- varToStringLitE :: MonadThings m => Var -> m CoreExpr
-- varToStringLitE =  mkStringExpr . var2String

-- mkStringExpr is hanging for some reason, so for now I'm just creating (type-incorrect) unboxed strings
varToStringLitE :: Var -> CoreExpr
varToStringLitE =  Lit . mkMachString . var2String

----------------------------------------------------

embeddingModule :: String
embeddingModule = "LambdaCCCDemo.Embedding"

addEmbeddingModule :: String -> String
addEmbeddingModule s = embeddingModule ++ "." ++ s

type FunctionName = String

findEmbeddingE :: FunctionName -> TranslateH a CoreExpr
findEmbeddingE s = findEmbeddingId s >>^ varToCoreExpr

findEmbeddingId :: FunctionName -> TranslateH a Id
findEmbeddingId = findIdT . TH.mkName . addEmbeddingModule

----------------------------------------------------
