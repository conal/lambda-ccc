module LambdaCCC where

import GhcPlugins

import Language.HERMIT.External
import Language.HERMIT.Optimize

plugin :: Plugin
plugin = optimize (phase 0 . interactive cmds)

cmds :: [External]
cmds = []
