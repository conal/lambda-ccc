{-# LANGUAGE TypeOperators, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

-- #define MealyToArrow

module LambdaCCC.Run (go,go',run,goM,goM') where

import Prelude
import Control.Arrow (first)

import LambdaCCC.Lambda (EP,reifyEP)
-- import LambdaCCC.CCC ((:->),convertC)
import LambdaCCC.ToCCC (toCCC')
#ifndef MealyToArrow
import LambdaCCC.ToCCC (toCCC)
#endif

import Circat.Circuit
  (GenBuses,Attr,mkGraph,unitize,UU,outDotG,MealyC(..)
#ifdef MealyToArrow
  , mealyAsArrow, unitize
#else
  , unitizeMealyC
#endif
  )
import Circat.Netlist (saveAsVerilog)
import Circat.Mealy (Mealy(..))

go' :: GenBuses a => String -> [Attr] -> (a -> b) -> IO ()
go' name attrs f = goM' name attrs (Mealy (first f) ())
{-# INLINE go' #-}

go :: GenBuses a => String -> (a -> b) -> IO ()
go name = go' name []
{-# INLINE go #-}

-- Broken:
-- #define ViaTerm

-- Run an example: reify, CCC, circuit.
run :: GenBuses a => String -> [Attr] -> EP (a -> b) -> IO ()
run name attrs e = do print e
                      outGV name attrs (unitize (toCCC' e))
{-# NOINLINE run #-}

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

#ifdef MealyToArrow

data MealyE a b =
  forall s. (GenBuses s, Show s) => MealyE (EP ((a,s) -> (b,s))) s

deriving instance Show (MealyE a b)

reifyMealy :: Mealy a b -> MealyE a b
reifyMealy (Mealy f s) = MealyE (reifyEP f) s
{-# INLINE reifyMealy #-}

toMealyC :: MealyE a b -> MealyC a b
toMealyC (MealyE f s) = MealyC (toCCC' f) s

runM :: GenBuses a => String -> [Attr] -> MealyE a b -> IO ()
runM name attrs e = do print e
                       outGV name attrs (unitize (mealyAsArrow (toMealyC e)))

-- TODO: Change outGV to take (a :> b) in place of UU, and drop unitizeC here.

goM :: GenBuses a => String -> Mealy a b -> IO ()
goM name = goM' name []
{-# INLINE goM #-}

goM' :: GenBuses a => String -> [Attr] -> Mealy a b -> IO ()
goM' name attrs m = runM name attrs (reifyMealy m)
{-# INLINE goM' #-}

-- TODO: Rework goM' via go' instead of vice versa

#else

data MealyE a b =
  forall s. GenBuses s => MealyE (EP ((a,s) -> (b,s))) (EP s)

deriving instance Show (MealyE a b)

reifyMealy :: Mealy a b -> MealyE a b
reifyMealy (Mealy f s) = MealyE (reifyEP f) (reifyEP s)
{-# INLINE reifyMealy #-}

toMealyC :: MealyE a b -> MealyC a b
toMealyC (MealyE f s) = MealyC (toCCC' f) (toCCC s)

runM :: GenBuses a => String -> [Attr] -> MealyE a b -> IO ()
runM name attrs e = do print e
                       outGV name attrs (unitizeMealyC (toMealyC e))

goM :: GenBuses a => String -> Mealy a b -> IO ()
goM name = goM' name []
{-# INLINE goM #-}

goM' :: GenBuses a => String -> [Attr] -> Mealy a b -> IO ()
goM' name attrs m = runM name attrs (reifyMealy m)
{-# INLINE goM' #-}

#endif

-- Despite INLINE pragmas, I still have to explicitly tell HERMIT to unfold
-- definitions from this module:
-- 
-- try (any-td (unfold ['go,'go','goM,'goM','reifyMealy]))


-- TODO: Maybe pull unitizeMealyC into toMealyC, renaming to "toMealyU"
