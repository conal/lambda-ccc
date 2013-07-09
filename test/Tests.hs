{-# LANGUAGE TypeOperators, RebindableSyntax, ConstraintKinds #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

----------------------------------------------------------------------
-- |
-- Module      :  Tests
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Test conversion of Haskell source code into circuits. To run:
-- 
--   hermit Tests.hs -opt=LambdaCCC.ReifyLambda +Main Tests.hss -- -v0 && ./Tests
----------------------------------------------------------------------

module Main where

import Prelude

import LambdaCCC.Misc (Unop,Binop)
import LambdaCCC.Lambda (reifyE,xor,ifThenElse)
import LambdaCCC.ToCCC (toCCC)
import LambdaCCC.ToCircuit

import Circat.Circuit (IsSource2,(:>),outG)
import Circat.Netlist (outV)

-- Needed for resolving names. Bug? Is there an alternative?
import qualified LambdaCCC.Lambda
import qualified LambdaCCC.Ty

{-

constPair :: (Bool,Bool)
constPair = (True,False)

idBool :: Bool -> Bool
idBool a = a

fst1 :: (s,t) -> s
fst1 = fst

fst2 :: (Bool,Int) -> Bool
fst2 = fst

fst3 :: (Bool,Int) -> Bool
fst3 p = fst p

bar :: Bool -> Bool -> Bool
bar = xor

foo :: (Bool,Bool) -> Bool
foo p = fst p `xor` snd p

baz :: (Bool,Bool) -> (Bool,Bool) -> Bool
baz p q = (fst p `xor` snd p) `xor` (fst q `xor` snd q) 

halfAdd :: (Bool,Bool) -> (Bool,Bool)
halfAdd p = (fst p && snd p, fst p `xor` snd p)

halfAdd' :: (Bool,Bool) -> (Bool,Bool)
halfAdd' (a,b) = (a `xor` b, a && b)

quux :: Bool -> (Bool,Bool)
quux p = (p,True)

p1 :: Bool -> (Bool,Bool)
p1 a = (a,not a)

-- Polymorphic
swap :: (s,t) -> (t,s)
swap p = (snd p, fst p)

swapBI :: (Bool,Int) -> (Int,Bool)
swapBI p = (snd p, fst p)

swapBI' :: (Bool,Int) -> (Int,Bool)
swapBI' (a,b) = (b,a)

f3 :: ((Bool,Bool),(Bool,Bool)) -> (Bool,Bool)
f3 ((a,b),(c,d)) = (a && c, b || d)

f4 :: Bool -> (Bool,Bool)
f4 x = (y,y)
 where
   y = not x

f5 :: ((Bool,Bool),Bool) -> Bool
f5 ((_,b),_) = b

f6 :: ((Bool,Bool),Bool) -> (Bool,(Bool,Bool))
f6 ((a,b),c) = (a,(b,c))

f7 :: ((Bool,Bool),Bool) -> (Bool,Bool)
f7 ((a,_),c) = (a,c)

f8 :: ((Bool,Bool),(Bool,Bool)) -> ((Bool,Bool),(Bool,Bool))
f8 ((a,b),(c,d)) = ((c,a),(d,b))

-- CRC examples

type B2 = (Bool,Bool)

step2 :: (B2,B2) -> B2
step2 ((d0,d1),(i0,i1)) = if i0 then (d0 `xor` i0, d1 `xor` i1) else (i0,i1)

type B3 = (Bool,(Bool,Bool))

step3 :: (B3,B3) -> B3
step3 ((d0,(d1,d2)),(i0,(i1,i2))) =
  if i0 then
    (d0 `xor` i0, (d1 `xor` i1, d2 `xor` i2))
  else
    (i0,(i1,i2))

-}

-- Add in left shift, and switch to fourth-degree (five-coefficient) polynomial.

type V5 a = (a,(a,(a,(a,a))))

type Seg5 = V5 Bool

step4c :: (Seg5,(Seg5,Bool)) -> Seg5
step4c (poly,(seg,b)) = shiftL4c seg' b
 where
   seg' = if fst seg then xor5 poly seg else seg

shiftL4c :: Seg5 -> Bool -> Seg5
shiftL4c (_,(a,(b,(c,d)))) e = (a,(b,(c,(d,e))))

liftA2_5 :: (a -> b -> c) ->
            V5 a -> V5 b -> V5 c
liftA2_5 op (a,(b,(c,(d,e)))) (a',(b',(c',(d',e')))) =
  (a `op` a',(b `op` b',(c `op` c',(d `op` d',e `op` e'))))

xor5 :: Seg5 -> Seg5 -> Seg5
xor5 = liftA2_5 xor


-- Help break up the conditional

step4d :: (Seg5,(Seg5,Bool)) -> Seg5
step4d ((aPoly,(bPoly,(cPoly,(dPoly,ePoly)))),((aSeg,(bSeg,(cSeg,(dSeg,eSeg)))),b)) = shiftL4c seg' b
 where
   seg' = if aSeg then
            xor5 (aPoly,(bPoly,(cPoly,(dPoly,ePoly)))) (aSeg,(bSeg,(cSeg,(dSeg,eSeg))))
          else (aSeg,(bSeg,(cSeg,(dSeg,eSeg))))

----

fiddle :: Int
fiddle = length "Fiddle"

-- WEIRD: sometimes when I comment out this fiddle definition, I get the dread
-- "expectJust initTcInteractive" GHC panic.



main :: IO ()
main = do print e
          print c
          outGV "step4c" (cccToCircuit c)
 where
   e = reifyE "step4c" step4c
   c = toCCC e

outGV :: IsSource2 a b => String -> (a :> b) -> IO ()
outGV s c = outG s c >> outV s c

-- TODO: maybe a TH macro for reifyE "foo" foo, "[r|foo]".
-- Maybe additional macros for specialized contexts like toCCC [r|foo].
