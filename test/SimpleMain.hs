{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=34 #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  SimpleMain
-- Copyright   :  (c) 2014 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Test conversion of Haskell source code into circuits. To run:
-- 
--   hermit Simple.hs -v0 -opt=LambdaCCC.ReifyLambda Auto.hss resume && ghc SimpleMain.hs && ./SimpleMain
----------------------------------------------------------------------

import Simple

#define MakeCircuit

import Prelude

import LambdaCCC.Misc (Unop)
import LambdaCCC.Lambda (reifyEP)
import LambdaCCC.ToCCC (toCCC')
-- import LambdaCCC.CCC (convertC,(:->))

#ifdef MakeCircuit
import Circat.Circuit (IsSourceP2,(:>),outGWith)
import Circat.Netlist (outV)
#endif


main :: IO ()
main = do print e
          print (idCT (toCCC' e))
#ifdef MakeCircuit
          outGV "test" (toCCC' e)
#endif
 where
   e       = reified           -- Works
--    e       = reifyEP halfAdd   -- Doesn't

--    -- Both of the following definitions work:
--    ccc     = toCCC' e
--    circuit = convertC ccc

-- Or just one, but explicitly polymorphic:
-- 
--    ccc :: BiCCCC k Prim => (Bool,Bool) `k` (Bool,Bool)
--    ccc = toCCC' e

-- Identity on CCC terms
idCT :: Unop (a :-> b)
idCT = id

-- -- Type-specialized toCCC
-- toCCCTerm' :: EP (a -> b) -> (a :-> b)
-- toCCCTerm' = toCCC'

#ifdef MakeCircuit

-- Diagram and Verilog
outGV :: IsSourceP2 a b => String -> (a :> b) -> IO ()
outGV s c = do outGWith ("pdf","") s c
               outV                s c

#endif
