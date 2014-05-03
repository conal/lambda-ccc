{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts #-}
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

module LambdaCCC.Run (run) where

import Prelude

import LambdaCCC.Misc (Unop)
import LambdaCCC.Lambda (EP)
import LambdaCCC.CCC ((:->),convertC)
import LambdaCCC.ToCCC (toCCC')

import Circat.Circuit (IsSourceP2,(:>),outGWith,IsSourceP2)
import Circat.Netlist (outV)

-- go :: IsSourceP2 a b => (a -> b) -> IO ()
-- go f = run (reifyEP f)
-- {-# INLINE go #-}

-- #define ViaTerm

run :: IsSourceP2 a b => String -> EP (a -> b) -> IO ()
#ifdef ViaTerm
run str  expr = do print expr
                   print term
                   outGV str circ
 where
   term = toCCC' expr
   circ = convertC term
#else
run str  e = do print e
                print (idCT (toCCC' e))
                outGV str (toCCC' e)

-- Identity on CCC terms
idCT :: Unop (a :-> b)
idCT = id
#endif

-- Diagram and Verilog
outGV :: IsSourceP2 a b => String -> (a :> b) -> IO ()
outGV s c = do outGWith ("pdf","")      s c
            -- outGWith (t,"-Gdpi=200") s c
               outV                     s c
