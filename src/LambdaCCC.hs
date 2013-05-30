{-# LANGUAGE TemplateHaskell #-}
module LambdaCCC where

import GhcPlugins

import qualified Language.Haskell.TH as TH

-- We really should make Language.HERMIT export everything
import Language.HERMIT.External
import Language.HERMIT.Kure
import Language.HERMIT.Optimize
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug

import LambdaCCC.CCC

import qualified LambdaCCCDemo.Reify as Reify

plugin :: Plugin
plugin = optimize (phase 0 . interactive cmds)

cmds :: [External]
cmds =
    Reify.externals ++
    [ external "convert" (promoteExprR (convert UnitP))
        [ "top level lambda->CCC transformation" ]
    , external "convert-lam" (promoteExprR (convertLam UnitP))
        [ "[| \\ x -> e |](k) ==> Curry [| e |]((k,x))" ]
    , external "convert-app" (promoteExprR (convertApp UnitP))
        [ "[| u v |](k) ==> Apply :. [| (u,v) |](k)" ]
    ]

data Pat = UnitP | VarP Id | PairP Pat Pat

convert :: Pat -> RewriteH CoreExpr
convert k =    convertLam k
            <+ convertApp k

-- This project should serve as a useful motivator for finding
-- a more typeful way to build CoreExprs.

-- NB: Neither of these is correct yet...
--     1. We need to supply explicit types to mkCoreApps
--     2. I haven't really thought hard about convertApp

-- convert k (Lam p e)  = Curry (convert (PairP k p) e)
convertLam :: Pat -> RewriteH CoreExpr
convertLam k = do
    Lam p _ <- idR
    observeR "convertLam"
    c <- findIdT 'Curry
    lamT (convert (PairP k $ VarP p)) $ \ _ e -> mkCoreApps (varToCoreExpr c) [{-some types need to go here!-}e]

-- convert k (u :^ v)   = Apply @. (convert k u &&& convert k v)
-- @. = :.
convertApp :: Pat -> RewriteH CoreExpr
convertApp k = do
    App u v <- idR
    observeR "convertApp"
    a   <- findET  'Apply
    c   <- findET' ":."
    amp <- findET' "&&&"
    appT (convert k) (convert k) $ \ u v ->
        let res = mkCoreApps amp [{-types go here-}u,v]
        in mkCoreApps c [{-again types go here-} a,res]

findET :: TH.Name -> TranslateH a CoreExpr
findET = fmap varToCoreExpr . findIdT

findET' :: String -> TranslateH a CoreExpr
findET' = findET . TH.mkName
