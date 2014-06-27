{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.TransCode
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Transform a Core program to use only standard types
----------------------------------------------------------------------

module LambdaCCC.TransCode where

-- TODO: explicit exports

import Prelude hiding (id,(.),(>>))
import qualified Prelude

import Control.Category (id,(.),(>>>))
import Control.Arrow (arr)
import Control.Monad (unless,(<=<))
import Data.Functor ((<$),(<$>))
import Control.Applicative (pure,(<*>),liftA2)
import Data.Monoid (mempty)
import Data.List (intercalate,isPrefixOf)
import qualified Data.Set as S

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Core (CoreDef(..))
import HERMIT.Dictionary hiding (externals)
import HERMIT.External (External,ExternalName,external,(.+),CmdTag(Loop))
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad (saveDef,newIdH,Label)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import HERMIT.Extras hiding (findTyConT)
import qualified HERMIT.Extras as Ex

import LambdaCCC.Misc ((<~))

class Enc a where enc :: a -> TransformH x a

instance (Enc a, Enc b) => Enc (a,b) where
  enc (a,b) = (,) <$> enc a <*> enc b
instance Enc a => Enc [a] where enc = mapM enc

instance Enc CoreExpr where
  enc e@(Lit _) = return e
  enc (Var v) = Var <$> enc v   -- Revisit for non-local vars
  enc (App u v) = App <$> enc u <*> enc v
  enc (Lam x e) = Lam <$> enc x <*> enc e
  enc (Let b e) = Let <$> enc b <*> enc e
  enc (Case e _w _ty [(_,[v],rhs)]) =
    -- TODO: Check whether _w is in rhs
    return $ Let (NonRec v e) rhs
  enc (Case e w ty [alt]) =
    Case <$> enc e
         <*> enc w
         <*> enc ty
         <*> ((:[]) <$> encAlt alt)
  enc (Case _ _ _ _) = error "enc: Case: not a single alternative"
  enc (Cast e _co) = enc e  -- Experiment
  enc (Tick t e) = Tick t <$> enc e
  enc (Type t) = Type <$> enc t
  enc (Coercion _co) = error "enc: Coercion -- ??"

encAlt :: CoreAlt -> TransformH x CoreAlt
encAlt (_,vs,e) = (DataAlt (tupleCon BoxedTuple (length vs)),vs,) <$> enc e

instance Enc Id where
  enc v | isId v    = newIdT (uqVarName v) . enc (varType v)
        | otherwise = return v

instance Enc Type where
  enc (TyConApp tc tys) | isDistribTC tc = TyConApp tc <$> enc tys
  enc (FunTy a b) = FunTy <$> enc a <*> enc b
  enc t = observeR "enc: unhandled type" $* t

isDistribTC :: TyCon -> Bool
isDistribTC tc = any ($ tc) [isTupleTyCon,isFunTyCon] && tyConArity tc == 2

instance Enc CoreBind where
  enc (NonRec v e) = NonRec <$> enc v <*> enc e
  enc (Rec ws) = Rec <$> enc ws

encode :: Enc a => RewriteH a
encode = id >>= enc

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)
 where
   externals =
     [ externC "encodeBind" (encode :: RewriteH CoreBind) "..."
     ]
