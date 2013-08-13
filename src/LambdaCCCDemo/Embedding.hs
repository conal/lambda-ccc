module LambdaCCCDemo.Embedding (Code(..), Expr(..), eval, compile, var, lam, app) where

data Code = Code

data Expr = Var String | Lam String Expr | App Expr Expr

var :: String -> Expr
var = Var

lam :: String -> Expr -> Expr
lam = Lam

app :: Expr -> Expr -> Expr
app = App

---------------------------------------------------

eval :: a -> Code
eval _ = Code

compile :: Expr -> Code
compile _ = Code

---------------------------------------------------
