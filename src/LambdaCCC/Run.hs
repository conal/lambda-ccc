{-# LANGUAGE TypeOperators, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module LambdaCCC.Run (go,go',run,goM,goM') where

import Prelude

import LambdaCCC.Misc (Unop)
import LambdaCCC.Lambda (EP,reifyEP)
-- import LambdaCCC.CCC ((:->),convertC)
import LambdaCCC.ToCCC (toCCC',toCCC)

import Circat.Circuit (GenBuses,(:>),Attr,mkGraph,unitize,UU,outDotG,MealyC(..),unitizeMealyC)
import Circat.Netlist (saveAsVerilog)
import Circat.Mealy (Mealy(..))

go' :: GenBuses a => String -> [Attr] -> (a -> b) -> IO ()
go' name attrs f = run name attrs (reifyEP f)
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

data MealyE a b =
  forall s. GenBuses s => MealyE (EP ((s,a) -> (s,b))) (EP s)

deriving instance Show (MealyE a b)

reifyMealy :: Mealy a b -> MealyE a b
reifyMealy (Mealy f s) = MealyE (reifyEP f) (reifyEP s)
{-# INLINE reifyMealy #-}

toMealyC :: MealyE a b -> MealyC a b
toMealyC (MealyE f s) = MealyC (toCCC' f) (toCCC s)
{-# NOINLINE toMealyC #-}

runM :: GenBuses a => String -> [Attr] -> MealyE a b -> IO ()
runM name attrs e = do print e
                       outGV name attrs (unitizeMealyC (toMealyC e))
{-# NOINLINE runM #-}

goM :: GenBuses a => String -> Mealy a b -> IO ()
goM name = goM' name []
{-# INLINE goM #-}

goM' :: GenBuses a => String -> [Attr] -> Mealy a b -> IO ()
goM' name attrs m = runM name attrs (reifyMealy m)
{-# INLINE goM' #-}

-- TODO: Maybe pull unitizeMealyC into toMealyC, renaming to "toMealyU"

