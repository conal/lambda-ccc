Convert lambda expressions to CCC combinators

# GHC Plugin

This package provides a HERMIT GHC plugin that converts
GHC Core to CCC combinators. You must `cabal install` the
package for the plugin to be available. To invoke the plugin:

hermit File.hs -opt=LambdaCCC +Target.Module.Name

Example:

hermit Simple.hs -opt=LambdaCCC +Main

Note: the `hermit` command simply invokes `ghc` with some
default flags.
