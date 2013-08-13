module Plus (plusCode, plus) where

import LambdaCCCDemo.Embedding

---------------------------------------------------

plusCode :: Code
plusCode = eval (\ m n -> plus m n)

plus :: Int -> Int -> Int
plus = (+)

---------------------------------------------------
