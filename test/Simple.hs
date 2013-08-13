module Main where

import LambdaCCC.CCC -- for findIdT

{-# NOINLINE lam #-}
lam :: Int -> Int
lam x = x + 1

main :: IO ()
main = print $ lam 53
