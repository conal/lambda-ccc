{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, PatternGuards #-}
{-# LANGUAGE MagicHash, ConstraintKinds, ViewPatterns #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Lambda
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Statically typed lambda expressions
----------------------------------------------------------------------

module LambdaCCC.Lambda
  ( xor, ifThenElse  -- From Prim
  , Name
  , V, Pat(..), E(..)
  , occursVP, occursVE, occursPE
  , varTy, patTy, expTy
  , varHasTy, patHasTy, expHasTy
  , var#, varPat#, asPat#, (@^), lam, lamv#, lett
  , varT, constT
  , (#), caseEither, casev#
  , reifyE, reifyE', evalE
  , vars, vars2
  ) where

import Control.Applicative (pure,liftA2)
import Control.Monad (guard)
import Control.Arrow ((&&&))
import Data.Maybe (isJust,fromMaybe,catMaybes,listToMaybe)
import Text.Printf (printf)
import Debug.Trace (trace)

import GHC.Pack (unpackCString#)
import GHC.Prim (Addr#)

import Data.IsTy
import Data.Proof.EQ

import LambdaCCC.Misc
import LambdaCCC.ShowUtils
import LambdaCCC.Prim
import LambdaCCC.Ty

-- Whether to sugar during show, including 'let'
#define Sugared

-- Whether to simplify during construction
#define Simplify

-- | Variable names
type Name = String

-- | Typed variable
data V a = V Name (Ty a)

instance Show (V a) where
  -- showsPrec p (V n ty) = showString n . showString " :: " . showsPrec p ty
  showsPrec _ (V n _) = showString n

instance IsTy V where
  V na tya `tyEq` V nb tyb = guard (na == nb) >> tya `tyEq` tyb

instance Eq (V a) where
  V na _ == V nb _ = nb == na

varTy :: V a -> Ty a
varTy (V _ ty) = ty

varHasTy :: V a -> HasTyJt a
varHasTy = tyHasTy . varTy

infixr 1 :#
infixr 8 :@

-- | Lambda patterns
data Pat :: * -> * where
  UnitPat :: Pat Unit
  VarPat  :: V a -> Pat a
  (:#)    :: Pat a -> Pat b -> Pat (a :* b)
  (:@)    :: Pat a -> Pat a -> Pat a

-- NOTE: ":@" is named to suggest "as patterns", but is more general ("and patterns").

-- TODO: Rename UnitPat and VarPat to PUnit and PVar

instance Eq (Pat a) where
  UnitPat  == UnitPat    = True
  VarPat v == VarPat v'  = v == v'
  (a :# b) == (a' :# b') = a == a' && b == b'
  (a :@ b) == (a' :@ b') = a == a' && b == b'
  _        == _          = False

instance Show (Pat a) where
  showsPrec _ UnitPat    = showString "()"
  showsPrec p (VarPat v) = showsPrec p v
  showsPrec p (a :# b)   = showsPair p a b
  showsPrec p (a :@ b)   = showsOp2' "@" (8,AssocRight) p a b

patTy :: Pat a -> Ty a
patTy UnitPat    = Unit
patTy (VarPat v) = varTy v
patTy (a :# b)   = patTy a :* patTy b
patTy (a :@ _)   = patTy a

patHasTy :: Pat a -> HasTyJt a
patHasTy = tyHasTy . patTy

-- | Does a variable occur in a pattern?
occursVP :: V a -> Pat b -> Bool
occursVP _ UnitPat     = False
occursVP v (VarPat v') = isJust (v `tyEq` v')
occursVP v (a :# b)    = occursVP v a || occursVP v b
occursVP v (a :@ b)    = occursVP v a || occursVP v b

-- TODO: Pull v out of the recursion.

{-
-- | Does any variable from the first pattern occur in the second?
occursPP :: Pat a -> Pat b -> Bool
occursPP UnitPat _ = False
occursPP (VarPat v) q = occursVP v q
occursPP (PairPat a b) q = occursPP a q || occursPP b q
occursPP (AndPat  a b) q = occursPP a q || occursPP b q
-}

#ifdef Simplify
-- | Substitute in a pattern
substVP :: V a -> Pat a -> Unop (Pat b)
substVP v p = substIn
 where
   substIn :: Unop (Pat c)
   substIn (VarPat (tyEq v -> Just Refl)) = p
   substIn (a :# b)                       = substIn a :# substIn b
   substIn (a :@ b)                       = substIn a :@ substIn b
   substIn q                              = q
#endif

infixl 9 :^
-- | Lambda expressions
data E :: * -> * where
  Var    :: forall a     . V a -> E a
  ConstE :: forall a     . Prim a -> Ty a -> E a
  (:^)   :: forall b a   . E (a :=> b) -> E a -> E b
  Lam    :: forall a b   . Pat a -> E b -> E (a :=> b)
  Either :: forall a b c . E (a -> c) -> E (b -> c) -> E (a :+ b -> c)

-- | The type of an expression
expTy :: E a -> Ty a
expTy (Var v)       = varTy v
expTy (ConstE _ ty) = ty
expTy (f :^ _)      = case expTy f of _ :=> b -> b
expTy (Lam p e)     = patTy p :=> expTy e
expTy (Either f g)  = a :+ b :=> c
  where
    (a,c) = splitFunTy (expTy f)
    (b,_) = splitFunTy (expTy g)

-- expTy (Either f g)  =
--   case (expTy f, expTy g) of
--     (a :=> b, _ :=> c) -> a :+ b :=> c

expHasTy :: E a -> HasTyJt a
expHasTy = tyHasTy . expTy

-- | A variable occurs freely in an expression
occursVE :: V a -> E b -> Bool
occursVE v = occ
 where
   occ :: E c -> Bool
   occ (Var v')     = isJust (v `tyEq` v')
   occ (ConstE {})  = False
   occ (f :^ e)     = occ f || occ e
   occ (Lam p e)    = not (occursVP v p) && occ e
   occ (Either f g) = occ f || occ g

-- | Some variable in a pattern occurs freely in an expression
occursPE :: Pat a -> E b -> Bool
occursPE UnitPat    = pure False
occursPE (VarPat v) = occursVE v
occursPE (p :# q)   = liftA2 (||) (occursPE p) (occursPE q)
occursPE (p :@ q)   = liftA2 (||) (occursPE p) (occursPE q)

sameTyE :: E a -> E b -> Maybe (a :=: b)
sameTyE ea eb = expTy ea `tyEq` expTy eb

-- I've placed the quantifiers explicitly to reflect what I learned from GHCi
-- (In GHCi, use ":set -fprint-explicit-foralls" and ":ty (:^)".)
-- When I said "forall a b" in (:^), GHC swapped them back. Oh well.

instance IsTy E where
  type IsTyConstraint E z = HasTy z
  tyEq = tyEq'

instance Eq (E a) where
  Var v      == Var v'                                   = v == v'
  ConstE x _ == ConstE x' _                              = x == x'
  (f :^ a)   == (f' :^ a') | Just Refl <- a `sameTyE` a' = a == a' && f == f'
  Lam p e    == Lam p' e'                                = p == p' && e == e'
  _          == _                                        = False

-- TODO: Replace the ConstE Ty argument with a HasTy constraint for ease of use.
-- I'm waiting until I know how to construct the required dictionaries in Core.
-- 
-- Meanwhile,

varT :: HasTy a => Name -> E a
varT nm = Var (V nm typ)

constT :: HasTy a => Prim a -> E a
constT p = ConstE p typ

var# :: forall a. Addr# -> Ty a -> E a
var# addr ty = Var (V (unpackCString# addr) ty)

varPat# :: forall a. Addr# -> Ty a -> Pat a
varPat# addr ty = VarPat (V (unpackCString# addr) ty)

asPat# :: forall a. Addr# -> Pat a -> Pat a
asPat# addr pat = varPat# addr (patTy pat) :@ pat

infixl 9 @^

-- | Smart application
(@^) :: forall b a . E (a :=> b) -> E a -> E b
#ifdef Simplify
-- ...
#endif
f @^ a = f :^ a

#ifdef Simplify

{-
patToE :: Pat a -> E a
patToE UnitPat       = ConstE (LitP ()) Unit
patToE (VarPat v)    = Var v
patToE (PairPat p q) | HasTy <- patHasTy p, HasTy <- patHasTy q
                     = patToE p # patToE q
patToE (AndPat  _ _) = error "patToE: AndPat not yet handled"
-}

-- Try this instead:

patToEs :: Pat a -> [E a]
patToEs UnitPat    = pure $ ConstE (LitP ()) Unit
patToEs (VarPat v) = pure $ Var v
patToEs (p :# q)   | HasTy <- patHasTy p, HasTy <- patHasTy q
                   = liftA2 (#) (patToEs p) (patToEs q)
patToEs (p :@ q)   | HasTy <- patHasTy p, HasTy <- patHasTy q
                   = patToEs p ++ patToEs q

#endif

-- TODO: watch out for repeated (++)

lam :: Pat a -> E b -> E (a -> b)
#ifdef Simplify
-- Eta-reduction

-- lam p (f :^ u) | Just Refl <- patTy p `tyEq` expTy u
--                , u == patToE p
--                , not (p `occursPE` f)
--                = f

lam p (f :^ u) | Just Refl <- patTy p `tyEq` expTy u
               , u `elem` patToEs p
               , not (p `occursPE` f)
               = f

-- Re-nest lambda patterns
lam p (Lam q w :^ Var v) | occursVP v p && not (occursVE v w) =
  lam (substVP v q p) w
#endif
lam p body = Lam p body

lamv# :: forall a b. Addr# -> Ty a -> E b -> E (a -> b)
lamv# addr ty body = lam (VarPat (V (unpackCString# addr) ty)) body

-- | Let expression (beta redex)
lett :: forall a b. Pat a -> E a -> E b -> E b
lett pat e body = lam pat body @^ e

infixr 1 #
(#) :: E a -> E b -> E (a :* b)
-- (ConstE Exl :^ p) # (ConstE Exr :^ p') | ... = ...
a # b | HasTy <- expHasTy a, HasTy <- expHasTy b
      = constT PairP @^ a @^ b

-- Handle surjectivity in @^ rather than here.

eitherE :: forall a b c . E (a -> c) -> E (b -> c) -> E (a :+ b -> c)
eitherE = Either  -- for now

-- | Encode a case expression on 'Left' & 'Right'.
caseEither :: forall a b c . Pat a -> E c -> Pat b -> E c -> E (a :+ b) -> E c
caseEither p u q v ab = (lam p u `eitherE` lam q v) @^ ab

casev# :: forall a b c. Addr# -> Ty a -> E c -> Addr# -> Ty b -> E c -> E (a :+ b) -> E c
casev# a ta q b tb r = caseEither (varPat# a ta) q (varPat# b tb) r

instance Show (E a) where
#ifdef Sugared
  showsPrec p (Either (Lam q a) (Lam r b) :^ ab) =
    showParen (p > 0) $
    showString "case " . showsPrec 0 ab . showString " of { "
                       . showsPrec 0 q . showString " -> " . showsPrec 0 a . showString " ; "
                       . showsPrec 0 r . showString " -> " . showsPrec 0 b . showString " } "
  showsPrec p (Lam q body :^ rhs) =  -- beta redex as "let"
    showParen (p > 0) $
    showString "let " . showsPrec 0 q . showString " = " . showsPrec 0 rhs
    . showString " in " . showsPrec 0 body
#endif
  showsPrec p (ConstE PairP _ :^ u :^ v) = showsPair p u v
  showsPrec p (ConstE prim _ :^ u :^ v) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2' op fixity p u v
  showsPrec _ (Var (V n _)) = showString n
  showsPrec p (ConstE c _)  = showsPrec p c
  showsPrec p (u :^ v)      = showsApp p u v
  showsPrec p (Lam q e)     =
    showParen (p > 0) $
    showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e
  showsPrec p (Either f g) = showsOp2' "|||" (2,AssocRight) p f g


-- TODO: Multi-line pretty printer with indentation

data OpInfo = OpInfo String Fixity

opInfo :: Prim a -> Maybe OpInfo
opInfo AddP = Just $ OpInfo "+"     (6,AssocLeft )
opInfo AndP = Just $ OpInfo "&&"    (3,AssocRight)
opInfo OrP  = Just $ OpInfo "||"    (2,AssocRight)
opInfo XorP = Just $ OpInfo "`xor`" (2,AssocRight)
opInfo _   = Nothing

-- | Single variable binding
data Bind = forall a. Bind (V a) a
-- | Variable environment
type Env = [Bind]

reifyE :: HasTy a => a -> String -> E a
reifyE a msg = reifyE' a msg typ

reifyE' :: a -> String -> Ty a -> E a
reifyE' _ msg _ = error (printf "Oops -- reifyE' %s was not eliminated" msg)
{-# NOINLINE reifyE' #-}

-- The artificially strange definition of reifyE' prevents it from getting
-- inlined and so allows the reify'/eval rule to fire. The NOINLINE pragma is
-- somehow insufficient, and the reify/eval rule won't fire. I don't know how to
-- get rules with dictionaries to work.

{-# RULES

"reify'/eval" forall e msg t. reifyE' (evalE e) msg t = e
"eval/reify'" forall x msg t. evalE (reifyE' x msg t) = x

  #-}

-- We evaluate *closed* expressions (no free variables)
instance Evalable (E a) where
  type ValT (E a) = a
  eval = evalE

evalE :: E a -> a
evalE e = trace ("evalE: " ++ show e) $
          eval' e []  -- provide empty environment

-- TODO: Rework so that eval' can work independently of env. Will save repeated
-- evals.

-- Expression evaluation requires a binding environment. In other words,
-- expressions evaluate to a function from environments.

eval' :: E a -> Env -> a
eval' (Var v)   env    = fromMaybe (error $ "eval': unbound variable: " ++ show v) $
                         lookupVar v env
eval' (ConstE p _) _   = eval p
eval' (u :^ v)  env    = (eval' u env) (eval' v env)
eval' (Lam p e) env    = \ x -> eval' e (extendEnv p x env)
eval' (Either f g) env = eval' f env `either` eval' g env

extendEnv :: Pat b -> b -> Env -> Env
extendEnv UnitPat       ()  = id
extendEnv (VarPat vb)   b   = (Bind vb b :)
extendEnv (p :# q)    (a,b) = extendEnv q b . extendEnv p a
extendEnv (p :@ q)      b   = extendEnv q b . extendEnv p b

lookupVar :: forall a. V a -> Env -> Maybe a
lookupVar va = listToMaybe . catMaybes . map check
 where
   check :: Bind -> Maybe a
   check (Bind vb b) | Just Refl <- va `tyEq` vb = Just b
                     | otherwise                 = Nothing

-- Oh, hm. I'm using a difference (Hughes) list representation. extendEnv maps
-- UnitPat, VarPat, and PairPat to mempty, singleton, and mappend, respectively.
-- 
-- TODO: adopt another representation, such as Seq. Replace the explicit
-- recursion in lookupVar with a fold or something. It's almost a mconcat.

vars :: HasTy a => Name -> (Pat a, E a)
vars = (VarPat &&& Var) . flip V typ

-- vars n = (VarPat v, Var v) where v = V n typ

vars2 :: HasTy2 a b =>
         (Name,Name) -> (Pat (a,b), (E a,E b))
vars2 (na,nb) = (ap :# bp, (ae,be))
 where
   (ap,ae) = vars na
   (bp,be) = vars nb

{--------------------------------------------------------------------
    Rules
--------------------------------------------------------------------}

kConst :: Prim a -> String -> Ty a -> E a
kConst p _msg ty = ConstE p ty

kLit :: (Show a, Eq a) => a -> String -> Ty a -> E a
kLit = kConst . LitP

{-# RULES
 
"reify/not"   reifyE' not   = kConst NotP
"reify/(&&)"  reifyE' (&&)  = kConst AndP
"reify/(||)"  reifyE' (||)  = kConst OrP
"reify/xor"   reifyE' xor   = kConst XorP
"reify/(+)"   reifyE' (+)   = kConst AddP
"reify/exl"   reifyE' fst   = kConst ExlP
"reify/exr"   reifyE' snd   = kConst ExrP
"reify/pair"  reifyE' (,)   = kConst PairP
"reify/inl"   reifyE' Left  = kConst InlP
"reify/inr"   reifyE' Right = kConst InrP
"reify/if"    reifyE' cond  = kConst CondP
"reify/false" reifyE' False = kLit False
"reify/true"  reifyE' True  = kLit True
 
  #-}

-- TODO: Generalize the false & true rules. I think I'll need to do via an
-- explicit Core transformation. I'll have to be able to find out whether the
-- type is Showable. I suppose I could handle a few known type constructors.

{-# RULES

"True/xor"  forall b. True  `xor` b     = not b
"xor/True"  forall a. a     `xor` True  = not a
"False/xor" forall b. False `xor` b     = b
"xor/False" forall a. a     `xor` False = a

 #-}

{-# RULES
 
"if/pair" forall a b c b' c'.
          ifThenElse a (b,c) (b',c') = (ifThenElse a b c,ifThenElse a b' c')

"condPair" forall q. cond q = condPair q

  #-}

{-# RULES

"if-split" forall a b c.
  ifThenElse a b c = (ifThenElse a (fst b) (fst c),ifThenElse a (fst b) (fst c))

  #-}

condPair :: (Bool,((a,b),(a,b))) -> (a,b)
condPair (a,((b',b''),(c',c''))) = (cond (a,(b',c')),cond (a,(b'',c'')))

-- TODO: if-splitting has gone through a few incarnations. Re-examine, and
-- prune away unused code.
