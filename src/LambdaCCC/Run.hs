{-# LANGUAGE TypeOperators, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

#define MealyAsFun

----------------------------------------------------------------------
-- |
-- Module      :  Run
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Run a test: reify, CCC, circuit
----------------------------------------------------------------------

module LambdaCCC.Run
  ( go,go',goSep,run,goM,goM',goMSep
  , goNew, goNew'
  ) where

import Prelude

import LambdaCCC.Lambda (EP,reifyEP)
import LambdaCCC.ToCCC (toCCC')

import Circat.Circuit (GenBuses,Attr,mkGraph,unitize,UU,outDotG)

import Circat.Netlist (saveAsVerilog)
import Circat.Mealy (Mealy(..))

#if defined MealyAsFun
import Circat.Mealy (asFun)
#else
import Circat.Circuit (MealyC(..),unitizeMealyC)
import Control.Arrow (first)
#endif

ranksep :: Double -> Attr
ranksep n = ("ranksep",show n)

go' :: GenBuses a => String -> [Attr] -> (a -> b) -> IO ()
#if defined MealyAsFun
go' = goNew'   -- Tidy up later
#else
go' name attrs f = goM' name attrs (Mealy (first f) ())
#endif

{-# INLINE go' #-}

go :: GenBuses a => String -> (a -> b) -> IO ()
go name = go' name []
{-# INLINE go #-}

goSep :: GenBuses a => String -> Double -> (a -> b) -> IO ()
goSep name s = go' name [ranksep s]

-- Run an example: reify, CCC, circuit.
run :: GenBuses a => String -> [Attr] -> EP (a -> b) -> IO ()
run name attrs e = do print e
                      outGV name attrs (unitize (toCCC' e))
{-# NOINLINE run #-}

goNew' :: GenBuses a => String -> [Attr] -> (a -> b) -> IO ()
goNew' name attrs f = run name attrs (reifyEP f)
{-# INLINE goNew' #-}

goNew :: GenBuses a => String -> (a -> b) -> IO ()
goNew name = goNew' name []
{-# INLINE goNew #-}

-- Diagram and Verilog
outGV :: String -> [Attr] -> UU -> IO ()
outGV name attrs circ =
  do outD ("pdf","")
     -- outD ("svg","") 
     -- outD ("png","-Gdpi=200")
     outV
 where
   g       = mkGraph name circ
   outD ss = outDotG ss attrs g
   outV    = saveAsVerilog g
{-# NOINLINE outGV #-}

-- TODO: Move file-saving code from outD and saveVerilog to here.

{--------------------------------------------------------------------
    State machines
--------------------------------------------------------------------}

goM :: GenBuses a => String -> Mealy a b -> IO ()
goM name = goM' name []
{-# INLINE goM #-}

goMSep :: GenBuses a => String -> Double -> Mealy a b -> IO ()
goMSep name s = goM' name [ranksep s]
{-# INLINE goMSep #-}

goM' :: GenBuses a => String -> [Attr] -> Mealy a b -> IO ()
{-# INLINE goM' #-}

#if defined MealyAsFun
goM' name attrs = go' name attrs . asFun
#else

goM' name attrs m = putStrLn ("Compiling " ++ name) >>
                    runM name attrs (reifyMealy m)

-- Reified Mealy machine
data MealyE a b =
  forall s. (GenBuses s, Show s) => MealyE (EP ((a,s) -> (b,s))) s

-- The Show constraint is just for the following Show, which is handy for debugging.
-- (See the 'print' in toMealyC.)
deriving instance Show (MealyE a b)

reifyMealy :: Mealy a b -> MealyE a b
reifyMealy (Mealy f s) = MealyE (reifyEP f) s
{-# INLINE reifyMealy #-}

toMealyC :: MealyE a b -> MealyC a b
toMealyC (MealyE f s) = MealyC (toCCC' f) s

runM :: GenBuses a => String -> [Attr] -> MealyE a b -> IO ()
runM name attrs e = do print e
                       outGV name attrs (unitizeMealyC (toMealyC e))

-- TODO: When mealyAsArrow works, rewrite goM' via go' instead of vice versa

-- Despite INLINE pragmas, I still have to explicitly tell HERMIT to unfold
-- definitions from this module:
-- 
-- try (any-td (unfold ['go,'go','goM,'goM','reifyMealy]))

-- TODO: Maybe pull unitizeMealyC into toMealyC, renaming to "toMealyU"

#endif
