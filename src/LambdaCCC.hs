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

plugin :: Plugin
plugin = optimize (phase 0 . interactive cmds)

cmds :: [External]
cmds = 
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
    a <- findIdT 'Apply
    c <- findIdT $ TH.mkName ":."
    amp <- findIdT $ TH.mkName "&&&"
    appT (convert k) (convert k) $ \ u v -> 
        let res = mkCoreApps (varToCoreExpr amp) [{-types go here-}u,v]
        in mkCoreApps (varToCoreExpr c) [{-again types go here-}varToCoreExpr a,res]
