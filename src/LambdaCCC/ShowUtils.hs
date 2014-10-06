-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ShowUtils
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Helpers for implementing Show
----------------------------------------------------------------------

module LambdaCCC.ShowUtils
  ( showsApp1, showsApp, showSpaced
  , Prec, Assoc(..), Fixity
  , showsOp2, showsOp2', showsPair
  , module Circat.ShowUtils
  ) where

import Data.List (intersperse)

import Circat.ShowUtils

import LambdaCCC.Misc (compose)

{--------------------------------------------------------------------
    Show helpers
--------------------------------------------------------------------}

-- | Show a simple function application
showsApp1 :: Show a => String -> Prec -> a -> ShowS
showsApp1 s p a = showParen (p > appPrec) $
                  showString s . showChar ' ' . showsPrec (appPrec+1) a

-- | Show a simple function application
showsApp :: (Show a, Show b) => Prec -> a -> b -> ShowS
showsApp p a b = showParen (p > appPrec) $
                 showsPrec appPrec a . showChar ' ' . showsPrec (appPrec+1) b

-- TODO: refactor showsApp1, showsApp

-- Precedence of function application.
-- Hack: use 11 instead of 10 to avoid extraneous parens when a function
-- application is the left argument of a function composition.
appPrec :: Int
appPrec = 11 -- was 10

-- TODO: Refactor showsApp & showsApp1
-- TODO: Resolve argument order

showSpaced :: [ShowS] -> ShowS
showSpaced = compose . intersperse (showChar ' ')

type Prec   = Int
data Assoc  = AssocLeft | AssocRight | AssocNone
type Fixity = (Prec,Assoc)

showsOp2 :: (Show a, Show b) =>
            Bool -> String -> Fixity -> Prec -> a -> b -> ShowS
showsOp2 extraParens sop (p,assoc) q a b =
  showParen (q > p) $
    showSpaced
      [ showsPrec (lf p) a
      , showString sop
      , showsPrec (rf p) b
      ]
 where
   (lf,rf) = case assoc of
               AssocLeft  -> (incr, succ)
               AssocRight -> (succ, incr)
               AssocNone  -> (succ, succ)
   incr | extraParens = succ
        | otherwise   = id

showsOp2' :: (Show a, Show b) =>
             String -> Fixity -> Prec -> a -> b -> ShowS
showsOp2' = showsOp2 False -- no extra parens

-- parend :: ShowS -> Prec -> Prec -> ShowS
-- parend sh p q = showParen (q > p) sh

showsPair :: (Show a, Show b) => Prec -> a -> b -> ShowS
showsPair _ a b = showParen True $
  showsPrec 0 a . showChar ',' . showsPrec 0 b

-- Simpler, but I don't like the resulting spaces around ",":
-- 
-- showsPair = showsOp2 True "," (-1,AssocNone)
