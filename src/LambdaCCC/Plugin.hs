-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Plugin
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Non-interactive HERMIT-based plugin
----------------------------------------------------------------------

module LambdaCCC.Plugin where

-- TODO: explicit exports

import Prelude hiding ((.))

import GhcPlugins (Plugin)
import Language.KURE (tryR)
import HERMIT.Kernel (CommitMsg(..))
import HERMIT.Plugin
-- import HERMIT.Plugin.Builder (CorePass(..))

import Monomorph.Plugin (tweakPretty)
import LambdaCCC.Reify (reifyModule)

plugin :: Plugin
plugin = hermitPlugin (const (firstPass plug))
 where
   plug = tweakPretty >> apply (Always "reify-core") (tryR reifyModule) -- was reifyR

-- I also tried using pass 4, which is after
-- [Simplify,Specialising,FloatOutwards,Simplify]. I thought I needed
-- Specialising, and then the next two to break up the large let-rec. Now I
-- think I don't need specialization for reification. The modular, polymorphic
-- reification works great.

