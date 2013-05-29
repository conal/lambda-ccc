module Main where

{-# NOINLINE lam #-}
lam :: Int -> Int
lam x = x + 1

main :: IO ()
main = print $ lam 53
