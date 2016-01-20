-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Interactive
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Interactive HERMIT-based plugin
----------------------------------------------------------------------

module LambdaCCC.Interactive where

-- TODO: explicit exports

import GhcPlugins (Plugin)
import HERMIT.Plugin (hermitPlugin,pass,interactive)

import qualified Monomorph.Stuff as Mo
import Monomorph.Plugin (tweakPretty)

import qualified LambdaCCC.Reify as Re

plugin :: Plugin
plugin = hermitPlugin (pass 0 . (tweakPretty >>) . interactive (Re.externals ++ Mo.externals))

-- plugin = hermitPlugin (\ opts -> pass 0 (tweakPretty >> interactive (Re.externals ++ Mo.externals) opts))
