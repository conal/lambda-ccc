{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, PatternGuards #-}
{-# LANGUAGE MagicHash, ConstraintKinds, ViewPatterns, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
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
  ( Name
  , V(..), Pat(..), E(..)
  , occursVP, occursVE, occursPE
  , (@^), lam, lett
  , (#), caseEither
  , var#, lamv#, varPat#, asPat#, casev#
  , reifyE, evalE
  , vars, vars2
  , xor, condBool   -- from Prim
  , intL
  , vecCaseZ, vecCaseS   -- To remove
  -- , Structured(..), idStruct, idVec
  , idVecZ, idVecS, idPair, idTreeZ, idTreeS
  -- Temporary less polymorphic variants.
  -- Remove when I can dig up Prim as a type in Core
  , EP, appP, lamP, lettP , varP#, lamvP#, letvP#, casevP#, eitherEP, castEP, castEP'
  , evalEP, reifyEP, kPrimEP, oops
  -- Hopefully temporary
  , vecSEP, treeZEP, treeSEP
  ) where

import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)
import Control.Arrow ((&&&))
import Data.Maybe (fromMaybe,catMaybes,listToMaybe)
-- import Data.Coerce (Coercible,coerce)
import Text.Printf (printf)
import Debug.Trace (trace)

import Unsafe.Coerce (unsafeCoerce)  -- TEMP

import GHC.Pack (unpackCString#)
import GHC.Prim (Addr#)

import Data.Proof.EQ

import TypeUnary.Vec (Vec(..),Z,S)

-- import Circat.Classes (VecCat(..))

import Circat.Pair  (Pair(..)) -- ,PairCat(..)
import Circat.RTree (Tree(..),TreeCat(..))

import LambdaCCC.Misc hiding (Eq'(..), (==?))
import LambdaCCC.ShowUtils
import LambdaCCC.Prim

-- Whether to sugar during show, including 'let'
#define Sugared

-- Whether to simplify during construction
#define Simplify

class PrimBasics p where
  unitP :: p Unit
  pairP :: p (a :=> b :=> a :* b)

instance PrimBasics Prim where
  unitP = LitP (UnitL ())
  pairP = PairP

class EvalableP p where evalP :: p a -> a

instance EvalableP Prim where evalP = eval

-- | Variable names
type Name = String

-- | Typed variable. Phantom
data V a = V Name

instance Show (V a) where
  showsPrec _ (V n) = showString n

varName :: V a -> Name
varName (V name) = name

instance Eq (V a) where (==) = (====)

-- instance Eq1' V where
--   (====) = (===)

-- instance Eq' (V a) (V b) where
--   V a === V b = a == b

instance Eq1' V where
  V a ==== V b = a == b

infixr 1 :$
infixr 8 :@

-- | Lambda patterns
data Pat :: * -> * where
  UnitPat :: Pat Unit
  VarPat  :: V a -> Pat a
  (:$)    :: Pat a -> Pat b -> Pat (a :* b)
  (:@)    :: Pat a -> Pat a -> Pat a

-- NOTE: ":@" is named to suggest "as patterns", but is more general ("and patterns").

-- TODO: Rename UnitPat and VarPat to PUnit and PVar

instance Eq1' Pat where
  UnitPat  ==== UnitPat    = True
  VarPat v ==== VarPat v'  = v ==== v'
  (a :$ b) ==== (a' :$ b') = a ==== a' && b ==== b'
  (a :@ b) ==== (a' :@ b') = a ==== a' && b ==== b'
  _        ==== _          = False

instance Eq (Pat a) where (==) = (====)

instance Show (Pat a) where
  showsPrec _ UnitPat    = showString "()"
  showsPrec p (VarPat v) = showsPrec p v
  showsPrec p (a :$ b)   = showsPair p a b
  showsPrec p (a :@ b)   = showsOp2' "@" (8,AssocRight) p a b

-- | Does a variable occur in a pattern?
occursVP :: V a -> Pat b -> Bool
occursVP _ UnitPat     = False
occursVP v (VarPat v') = varName v == varName v'
occursVP v (a :$ b)    = occursVP v a || occursVP v b
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
   substIn (VarPat ((v ===?) -> Just Refl)) = p
   substIn (a :$ b)                         = substIn a :$ substIn b
   substIn (a :@ b)                         = substIn a :@ substIn b
   substIn q                                = q
#endif

infixl 9 :^
-- | Lambda expressions
data E :: (* -> *) -> (* -> *) where
  Var    :: forall p a    . V a -> E p a
  ConstE :: forall p a    . p a -> E p a
  (:^)   :: forall p b a  . E p (a :=> b) -> E p a -> E p b
  Lam    :: forall p a b  . Pat a -> E p b -> E p (a :=> b)
  Either :: forall p a b c. E p (a -> c) -> E p (b -> c) -> E p (a :+ b -> c)
  Cast   :: forall p a b  . a ~ b => E p a -> E p b

-- The explicit universals come from ghci's ":ty" command with ":set
-- -fprint-explicit-foralls", so that I can get the order right when
-- constructing Core programmatically.

-- | A variable occurs freely in an expression
occursVE :: V a -> E p b -> Bool
occursVE v@(V name) = occ
 where
   occ :: E p c -> Bool
   occ (Var (V name')) = name == name'
   occ (ConstE {})     = False
   occ (f :^ e)        = occ f || occ e
   occ (Lam p e)       = not (occursVP v p) && occ e
   occ (Either f g)    = occ f || occ g
   occ (Cast e)        = occ e

-- | Some variable in a pattern occurs freely in an expression
occursPE :: Pat a -> E p b -> Bool
occursPE UnitPat    = pure False
occursPE (VarPat v) = occursVE v
occursPE (p :$ q)   = liftA2 (||) (occursPE p) (occursPE q)
occursPE (p :@ q)   = liftA2 (||) (occursPE p) (occursPE q)

-- I've placed the quantifiers explicitly to reflect what I learned from GHCi
-- (In GHCi, use ":set -fprint-explicit-foralls" and ":ty (:^)".)
-- When I said "forall a b" in (:^), GHC swapped them back. Oh well.

instance Eq1' p => Eq1' (E p) where
  Var v    ==== Var v'     = v ==== v'
  ConstE x ==== ConstE x'  = x ==== x'
  (f :^ a) ==== (f' :^ a') = a ==== a' && f ==== f'
  Lam p e  ==== Lam p' e'  = p ==== p' && e ==== e'
  Cast e   ==== Cast e'    = e ==== e'
  _        ==== _          = False

-- instance Eq1' p => Eq' (E p a) (E p b) where
--   (===) = (====)

instance Eq1' p => Eq (E p a) where (==) = (====)

{-
varT :: HasTy a => Name -> E p a
varT nm = Var (V nm typ)

constT :: HasTy a => Prim a -> E p a
constT p = ConstE p typ

var# :: forall a. Addr# -> Ty a -> E p a
var# addr ty = Var (V (unpackCString# addr) ty)

varPat# :: forall a. Addr# -> Ty a -> Pat a
varPat# addr ty = VarPat (V (unpackCString# addr) ty)

asPat# :: forall a. Addr# -> Pat a -> Pat a
asPat# addr pat = varPat# addr (patTy pat) :@ pat
-}

infixl 9 @^

-- | Smart application
(@^) :: forall b a p . E p (a :=> b) -> E p a -> E p b
#ifdef Simplify
-- ...
#endif
f @^ a = f :^ a

#ifdef Simplify

{-
patToE :: Pat a -> E p a
patToE UnitPat       = ConstE (LitP ()) Unit
patToE (VarPat v)    = Var v
patToE (PairPat p q) | HasTy <- patHasTy p, HasTy <- patHasTy q
                     = patToE p # patToE q
patToE (AndPat  _ _) = error "patToE: AndPat not yet handled"
-}

-- Instead, generate *all* expressions for a pattern, forking at an AndPat.

patToEs :: PrimBasics p => Pat a -> [E p a]
patToEs UnitPat    = pure $ ConstE unitP
patToEs (VarPat v) = pure $ Var v
patToEs (p :$ q)   = liftA2 (#) (patToEs p) (patToEs q)
patToEs (p :@ q)   = patToEs p ++ patToEs q

#endif

-- TODO: watch out for repeated (++)

lam :: (PrimBasics p, Eq1' p) =>
       Pat a -> E p b -> E p (a -> b)
#ifdef Simplify
-- Eta-reduction

-- lam p (f :^ u) | Just Refl <- patTy p `tyEq` expTy u
--                , u == patToE p
--                , not (p `occursPE` f)
--                = f

lam p (f :^ u) | Refl : _ <- catMaybes ((u ===?) <$> patToEs p)
               , not (p `occursPE` f)
               = f

-- TODO: Look for more efficient implementation rather than generate expressions
-- and test for equality.

-- Re-nest lambda patterns
lam p (Lam q w :^ Var v) | occursVP v p && not (occursVE v w) =
  lam (substVP v q p) w
#endif
lam p body = Lam p body

{-
lamv# :: forall a b. Addr# -> Ty a -> E p b -> E p (a -> b)
lamv# addr ty body = lam (VarPat (V (unpackCString# addr) ty)) body
-}

-- | Let expression (beta redex)
lett :: forall a b p. (PrimBasics p, Eq1' p) =>
                      Pat a -> E p a -> E p b -> E p b
lett pat e body = lam pat body @^ e

infixr 1 #
(#) :: PrimBasics p => E p a -> E p b -> E p (a :* b)
-- (ConstE Exl :^ p) # (ConstE Exr :^ p') | ... = ...
a # b = ConstE pairP @^ a @^ b

-- Handle surjectivity in @^ rather than here.

eitherE :: forall p a c b . E p (a -> c) -> E p (b -> c) -> E p (a :+ b -> c)
eitherE = Either  -- for now

-- The order a c b matches either

-- | Encode a case expression on 'Left' & 'Right'.
caseEither :: forall p a b c . (PrimBasics p, Eq1' p) =>
              Pat a -> E p c -> Pat b -> E p c -> E p (a :+ b) -> E p c
caseEither p u q v ab = (lam p u `eitherE` lam q v) @^ ab

castE :: forall p a b . a ~ b => E p a -> E p b
castE = Cast

instance (HasOpInfo prim, Show' prim, PrimBasics prim, Eq1' prim)
  => Show (E prim a) where
#ifdef Sugared
--   showsPrec p (Either (Lam q a) (Lam r b) :^ ab) =
--     showParen (p > 0) $
--     showString "case " . showsPrec 0 ab . showString " of { "
--                        . showsPrec 0 q . showString " -> " . showsPrec 0 a . showString " ; "
--                        . showsPrec 0 r . showString " -> " . showsPrec 0 b . showString " } "
  showsPrec p (Lam q body :^ rhs) =  -- beta redex as "let"
    showParen (p > 0) $
    showString "let " . showsPrec 0 q . showString " = " . showsPrec 0 rhs
    . showString " in " . showsPrec 0 body
  showsPrec p (ConstE ((==== pairP) -> True) :^ u :^ v)
                          = showsPair p u v
#endif
  showsPrec p (ConstE prim :^ u :^ v) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2' op fixity p u v
  showsPrec _ (Var (V n)) = showString n
  showsPrec p (ConstE c)  = showsPrec' p c
  showsPrec p (u :^ v)      = showsApp p u v
  showsPrec p (Lam q e)     =
    showParen (p > 0) $
    showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e
  showsPrec p (Either f g) = showsOp2' "|||" (2,AssocRight) p f g
  showsPrec p (Cast e)     = showsApp1 "cast" p e


-- TODO: Multi-line pretty printer with indentation

data OpInfo = OpInfo String Fixity

class HasOpInfo p where
  opInfo :: p a -> Maybe OpInfo

instance HasOpInfo Prim where
  opInfo AddP = Just $ OpInfo "+"     (6,AssocLeft )
  opInfo AndP = Just $ OpInfo "&&"    (3,AssocRight)
  opInfo OrP  = Just $ OpInfo "||"    (2,AssocRight)
  opInfo XorP = Just $ OpInfo "`xor`" (2,AssocRight)
  opInfo _   = Nothing

-- | Single variable binding
data Bind = forall a. Bind (V a) a
-- | Variable environment
type Env = [Bind]

reifyE :: a -> E p a
reifyE _ = error (printf "reifyE: Oops -- not eliminated.")
{-# NOINLINE reifyE #-}  -- to give reify/eval rules a chance

{-# RULES

"reifyE/evalE" forall e. reifyE (evalE e) = e
-- "evalE/reifyE" forall x. evalE (reifyE x) = x

"reifyEP/evalEP" forall e. reifyEP (evalEP e) = e
-- "evalEP/reifyEP" forall x. evalEP (reifyEP x) = x

  #-}

-- We evaluate *closed* expressions (no free variables)
instance (HasOpInfo p, Show' p, EvalableP p, Eq1' p, PrimBasics p) =>
         Evalable (E p a) where
  type ValT (E p a) = a
  eval = evalE

evalE :: (HasOpInfo p, Show' p, EvalableP p, Eq1' p, PrimBasics p) => 
         E p a -> a
evalE e = trace ("evalE: " ++ show e) $
          eval' e []  -- provide empty environment

-- TODO: Rework so that eval' can work independently of env. Will save repeated
-- evals.

-- Expression evaluation requires a binding environment. In other words,
-- expressions evaluate to a function from environments.

eval' :: (HasOpInfo p, Show' p, EvalableP p) => 
         E p a -> Env -> a

#if 1

eval' (Var v)      env = fromMaybe (error $ "eval': unbound variable: " ++ show v) $
                         lookupVar v env
eval' (ConstE p)   _   = evalP p
eval' (u :^ v)     env = (eval' u env) (eval' v env)
eval' (Lam p e)    env = \ x -> eval' e (extendEnv p x env)
eval' (Either f g) env = eval' f env `either` eval' g env
eval' (Cast e)     env = eval' e env

#else

-- More efficiently, traverse the expression just once, even under lambdas:

eval' (Var v)      = fromMaybe (error $ "eval': unbound variable: " ++ show v) .
                     lookupVar v
eval' (ConstE p)   = const (evalP p)
eval' (u :^ v)     = eval' u <*> eval' v
eval' (Lam p e)    = (fmap.fmap) (eval' e) (flip (extendEnv p))
eval' (Either f g) = liftA2 either (eval' f) (eval' g)
eval' (Cast e)     = eval' e

-- Derivation of Lam case:
-- 
--      \ env -> \ x -> eval' e (extendEnv p x env)
--   == \ env -> \ x -> eval' e (flip (extendEnv p) env x)
--   == \ env -> eval' e . flip (extendEnv p) env
--   == \ env -> fmap (eval' e) (flip (extendEnv p) env)
--   == fmap (eval' e) . flip (extendEnv p)
--   == (fmap.fmap) (eval' e) (flip (extendEnv p))

#endif

extendEnv :: Pat b -> b -> (Env -> Env)
extendEnv UnitPat       ()  = id
extendEnv (VarPat vb)   b   = (Bind vb b :)
extendEnv (p :$ q)    (a,b) = extendEnv q b . extendEnv p a
extendEnv (p :@ q)      b   = extendEnv q b . extendEnv p b

-- TODO: Rewrite extendEnv so that it examines the pattern just once,
-- independently from the value.

lookupVar :: forall a. V a -> Env -> Maybe a
lookupVar va = listToMaybe . catMaybes . map check
 where
   check :: Bind -> Maybe a
   check (Bind vb b) | Just Refl <- va ===? vb = Just b
                     | otherwise               = Nothing

-- Oh, hm. I'm using a difference (Hughes) list representation. extendEnv maps
-- UnitPat, VarPat, and PairPat to mempty, singleton, and mappend, respectively.
-- 
-- TODO: adopt another representation, such as Seq. Replace the explicit
-- recursion in lookupVar with a fold or something. It's almost a mconcat.

vars :: Name -> (Pat a, E p a)
vars = (VarPat &&& Var) . V

-- vars n = (VarPat v, Var v) where v = V n typ

vars2 :: (Name,Name) -> (Pat (a,b), (E p a,E p b))
vars2 (na,nb) = (ap :$ bp, (ae,be))
 where
   (ap,ae) = vars na
   (bp,be) = vars nb

{--------------------------------------------------------------------
    Rules
--------------------------------------------------------------------}

kPrim :: p a -> E p a
kPrim = ConstE

kLit :: HasLit a => a -> EP a
kLit = kPrim . litP

-- Temporary monomorphic specialization of kLit, until I know how to synthesize
-- dictionaries.
intL :: Int -> EP Int
intL = kLit

-- TODO: change the following rules back to reifyE

{-# RULES
 
"reify/not"     reifyEP not      = kPrim NotP
"reify/(&&)"    reifyEP (&&)     = kPrim AndP
"reify/(||)"    reifyEP (||)     = kPrim OrP
"reify/xor"     reifyEP xor      = kPrim XorP
"reify/(+)"     reifyEP (+)      = kPrim AddP
"reify/(*)"     reifyEP (*)      = kPrim MulP
"reify/exl"     reifyEP fst      = kPrim ExlP
"reify/exr"     reifyEP snd      = kPrim ExrP
"reify/pair"    reifyEP (,)      = kPrim PairP
"reify/inl"     reifyEP Left     = kPrim InlP
"reify/inr"     reifyEP Right    = kPrim InrP
"reify/if"      reifyEP condBool = kPrim CondBP

"reify/()"      reifyEP ()       = kLit  ()
"reify/false"   reifyEP False    = kLit  False
"reify/true"    reifyEP True     = kLit  True

-- "reify/ZVec"    reifyEP ZVec     = reifyEP (toVecZ ())
-- "reify/(:<)"    reifyEP (:<)     = reifyEP toVecS

"reify/ZVec"    reifyEP ZVec     = vecZEP
"reify/(:<)"    reifyEP (:<)     = kPrim VecSP

"reify/(:#)"    reifyEP (:#)     = kPrim UPairP
"reify/L"       reifyEP L        = kPrim ToLeafP
"reify/B"       reifyEP B        = kPrim ToBranchP

"reify/unPair"   reifyEP unPair'  = kPrim UnUPairP
"reify/unLeaf"   reifyEP unTreeZ' = kPrim UnLeafP
"reify/unBranch" reifyEP unTreeS' = kPrim UnBranchP

-- TODO: Why reify/unPair' and not reify/unVecZ & reify/unVecS ?
-- TODO: trees

-- -- This one avoids currying
-- "reify/(a:<as)" forall a as. reifyEP (a:<as) = reifyEP (toVecS' (a,as))

-- HACK/experiment.
-- Doesn't fire when the 2 is let-abstracted.
-- TODO: Fix worthLet in Reify.
"reify/square"  reifyEP (^2) = reifyEP square

  #-}

square :: Num a => Unop a
square a = a * a

vecZEP :: EP (Vec Z a)
vecZEP = kPrim ToVecZP @^ kLit ()

-- Temp workaround until I can get reify/(:<) to apply to the bare constructor
vecSEP :: forall n a. EP (a -> Vec n a -> Vec (S n) a)
vecSEP = kPrim VecSP

treeZEP :: forall a. EP (a -> Tree Z a)
treeZEP = kPrim ToLeafP

treeSEP :: forall n a. EP (Pair (Tree n a) -> Tree (S n) a)
treeSEP = kPrim ToBranchP



-- For literals, I'd like to say
-- 
--   "reify/lit"   forall a x. HasLit a => reifyEP x = kLit  x
-- 
-- but I don't think GHC likes constraints here.

{-# RULES

"True/xor"  forall b. True  `xor` b     = not b
"xor/True"  forall a. a     `xor` True  = not a
"False/xor" forall b. False `xor` b     = b
"xor/False" forall a. a     `xor` False = a

"0 + a" forall a. 0 + a = a
"a + 0" forall a. a + 0 = a

 #-}

#if 0
 
-- "reify/if-bool" reifyEP cond     = reifyEP condBool
-- "reify/if-pair" reifyEP cond     = reifyEP condPair

condBool :: (Bool,(Bool,Bool)) -> Bool
condBool (i,(e,t)) = (i && t) || (not i && e)

-- TODO: 
-- Maybe ditch condBool in favor of mux on (->).
-- Or maybe define condBool = eval CondBP.
-- Hm. Might need dictionary argument.

-- condBool (i,(t,e)) = if i then t else e

condPair :: (Bool,((a,b),(a,b))) -> (a,b)
condPair (a,((b',b''),(c',c''))) = (cond (a,(b',c')),cond (a,(b'',c'')))

#endif

#if 0

-- TODO: if-splitting has gone through a few incarnations. Re-examine, and
-- prune away unused code.

{-# RULES
 
"if/pair" forall a b c b' c'.
          ifThenElse a (b,c) (b',c') = (ifThenElse a b c,ifThenElse a b' c')

"condPair" forall q. cond q = condPair q

  #-}

{-# RULES

"if-split" forall a b c.
  ifThenElse a b c = (ifThenElse a (fst b) (fst c),ifThenElse a (fst b) (fst c))

  #-}

#endif

-- Use this rule only we do all the reification we can, in order to finish generating an EP.

-- {-# RULES "reify/oops" forall e. reifyEP e = oops  #-}

-- For translating case of empty vector
vecCaseZ :: forall b a. b -> Vec Z a -> b
vecCaseZ b ZVec = b

-- For translating case of nonempty vector
-- vecCaseS :: forall n a b. (a -> Vec n a -> b) -> Vec (S n) a -> b
vecCaseS :: forall n a b. (a -> Vec n a -> b) -> Vec (S n) a -> b
vecCaseS f (a :< as) = f a as

{--------------------------------------------------------------------
    Restructuring help. Move elsewhere. Needed by Reify.
--------------------------------------------------------------------}

{-
class Structured t where
  type Enc t
  encode :: t -> Enc t
  decode :: Enc t -> t

idStruct :: Structured t => t -> t
idStruct = decode . encode

instance Structured (Vec   Z   a) where
  type Enc (Vec Z a) = ()
  encode = unVecZ
  decode = toVecZ
instance Structured (Vec (S n) a) where
  type Enc (Vec (S n) a) = a :* Vec n a
  encode = unVecS
  decode = toVecS

-- Type specialization. Drop when I can find/construct dictionaries via HERMIT.
idVec :: forall n a. Unop (Vec n a)
idVec = idStruct
-}

-- To eliminate a case-of-vec, wrap the scrutinee by idVecZ or idVecS and
-- simplify. Don't inline vector examination (unVecZ or unVecS), which would
-- yield another case-of-vec. Do inline vector construction (toVecZ or toVecS)
-- to reveal case-of-known constructor.

idVecZ :: forall a. Unop (Vec Z a)
idVecZ = toVecZ' . unVecZ'

idVecS :: forall n a. Unop (Vec (S n) a)
idVecS = toVecS' . unVecS'

idPair :: forall a. Unop (Pair a)
idPair = toPair' . unPair'

idTreeZ :: forall a. Unop (Tree Z a)
idTreeZ = toTreeZ' . unTreeZ'

idTreeS :: forall n a. Unop (Tree (S n) a)
idTreeS = toTreeS' . unTreeS'

-- Bogus method variants to control inlining.

toVecZ' :: () -> Vec Z a
toVecZ' () = ZVec
{-# INLINE toVecZ' #-}

toVecS' :: a :* Vec n a -> Vec (S n) a
toVecS' (a,as) = a :< as
{-# INLINE toVecS' #-}

unVecZ' :: Vec Z a -> ()
unVecZ' ZVec = ()
{-# NOINLINE unVecZ' #-}

unVecS' :: Vec (S n) a -> a :* Vec n a
unVecS' (a :< as) = (a,as)
{-# NOINLINE unVecS' #-}

-- TODO: If these definitions control inlining as I want, try replacing them
-- with ones that call the VecCat methods.

toPair' :: a :* a -> Pair a
toPair' (a,a') = a :# a'
{-# INLINE toPair' #-}

unPair' :: Pair a -> a :* a
unPair' (a :# a') = (a,a')
{-# NOINLINE unPair' #-}


toTreeZ' :: a -> Tree Z a
toTreeZ' = L
{-# INLINE toTreeZ' #-}

toTreeS' :: Pair (Tree n a) -> Tree (S n) a
toTreeS' = B
{-# INLINE toTreeS' #-}

unTreeZ' :: Tree Z a -> a
unTreeZ' = unL
{-# NOINLINE unTreeZ' #-}

unTreeS' :: Tree (S n) a -> Pair (Tree n a)
unTreeS' = unB
{-# NOINLINE unTreeS' #-}

{-# RULES

-- "reify/toVecZ" reifyEP toVecZ' = kPrim ToVecZP
-- "reify/toVecS" reifyEP toVecS' = kPrim ToVecSP

"reify/unVecZ" reifyEP unVecZ' = kPrim UnVecZP
"reify/unVecS" reifyEP unVecS' = kPrim UnVecSP

 #-}

{--------------------------------------------------------------------
    Constructors that take Addr#, for ReifyLambda
--------------------------------------------------------------------}

var# :: forall a p. p ~ Prim => 
        Addr# -> E p a
var# addr = Var (V (unpackCString# addr))

varPat# :: forall a. Addr# -> Pat a
varPat# addr = VarPat (V (unpackCString# addr))

asPat# :: forall a. Addr# -> Pat a -> Pat a
asPat# addr pat = varPat# addr :@ pat

lamv# :: forall a b p. (PrimBasics p, Eq1' p, p ~ Prim) =>
         Addr# -> E p b -> E p (a -> b)
lamv# addr body = lam (VarPat (V (unpackCString# addr))) body

letv# :: forall p a b. (PrimBasics p, Eq1' p) =>
         Addr# -> E p a -> E p b -> E p b
letv# addr body = lett (varPat# addr) body

casev# :: forall a b c p. (PrimBasics p, Eq1' p, p ~ Prim) =>
          Addr# -> E p c -> Addr# -> E p c -> E p (a :+ b) -> E p c
casev# a q b = caseEither (varPat# a) q (varPat# b)

-- TODO: Drop the p ~ Prim constraints, and tweak ReifyLambda to pass in Prim as
-- a type argument.

{--------------------------------------------------------------------
    Less polymorphic versions temporarily
--------------------------------------------------------------------}

type EP = E Prim

appP :: forall b a . EP (a :=> b) -> EP a -> EP b
appP = (@^)

lamP :: forall a b. Pat a -> EP b -> EP (a -> b)
lamP = lam

lettP :: forall a b. Pat a -> EP a -> EP b -> EP b
lettP = lett

varP# :: Addr# -> EP a
varP# = var#

lamvP# :: forall a b. Addr# -> EP b -> EP (a -> b)
lamvP# = lamv#

letvP# :: forall a b. Addr# -> EP a -> EP b -> EP b
letvP# = letv#

casevP# :: forall a b c. Addr# -> EP c -> Addr# -> EP c -> EP (a :+ b) -> EP c
casevP# = casev#

eitherEP :: forall a c b . EP (a -> c) -> EP (b -> c) -> EP (a :+ b -> c)
eitherEP = eitherE

-- The order a c b matches 'either'

castEP :: forall a b . a ~ b => EP a -> EP b
castEP = castE

castEP' :: forall a b . {- a ~ b => -} EP a -> EP b
castEP' = unsafeCoerce  -- TEMPORARY

evalEP :: EP a -> a
evalEP = evalE
{-# NOINLINE evalEP #-}

reifyEP :: a -> EP a
reifyEP = reifyE
{-# NOINLINE reifyEP #-}

-- If reifyEP doesn't get inlined, change the reifyE prim rules below to
-- reifyEP.

kPrimEP :: Prim a -> EP a
kPrimEP = kPrim

oops :: EP a
oops = kPrim OopsP

{--------------------------------------------------------------------
    Move elsewhere
--------------------------------------------------------------------}

-- I'm experimenting with dropping Eq' in favor of Eq1' (and renaming the latter).

-- instance Eq1' Prim where (====) = (===)

instance Eq1' Prim where
  LitP a    ==== LitP b    = a ==== b
  NotP      ==== NotP      = True
  AndP      ==== AndP      = True
  OrP       ==== OrP       = True
  XorP      ==== XorP      = True
  AddP      ==== AddP      = True
  MulP      ==== MulP      = True
  ExlP      ==== ExlP      = True
  ExrP      ==== ExrP      = True
  PairP     ==== PairP     = True
  CondBP    ==== CondBP    = True
  ToVecZP   ==== ToVecZP   = True
  UnVecZP   ==== UnVecZP   = True
  VecSP     ==== VecSP     = True
  UnVecSP   ==== UnVecSP   = True
  UPairP    ==== UPairP    = True
  UnUPairP  ==== UnUPairP  = True
  ToLeafP   ==== ToLeafP   = True
  ToBranchP ==== ToBranchP = True
  UnLeafP   ==== UnLeafP   = True
  UnBranchP ==== UnBranchP = True
  OopsP     ==== OopsP     = True
  _         ==== _         = False

instance Eq1' Lit where
  UnitL x ==== UnitL y = x == y
  BoolL x ==== BoolL y = x == y
  IntL  x ==== IntL  y = x == y
  _       ==== _       = False
