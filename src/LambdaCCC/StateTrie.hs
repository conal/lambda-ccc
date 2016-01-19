{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.StateTrie
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Memoizing State monad
----------------------------------------------------------------------

module LambdaCCC.StateTrie
  ( StateTrieX, StateTrie(..)
  , toState, fromState
  , get, put, runStateTrie, evalStateTrie, execStateTrie
  ) where

import Control.Arrow (first)

import Control.Monad.State -- mtl

import Data.MemoTrie (HasTrie(..),(:->:))

import Circat.Rep (Rep,HasRep(..))

-- | 'StateTrie' inner representation
type StateTrieX s a = s :->: (a,s)

-- | Memoizing state monad
newtype StateTrie s a = StateTrie { unStateTrie :: StateTrieX s a }

-- | Operate inside a 'StateTrie'.
inStateTrie :: (StateTrieX s a -> StateTrieX t b)
            -> (StateTrie  s a -> StateTrie  t b)
inStateTrie = StateTrie <~ unStateTrie
{-# INLINE inStateTrie #-}

{- unused

inStateTrie2 :: (StateTrieX s a -> StateTrieX t b -> StateTrieX u c)
             -> (StateTrie  s a -> StateTrie  t b -> StateTrie  u c)
inStateTrie2 = inStateTrie <~ unStateTrie

-}

-- | Run a memoized stateful computation
runStateTrie :: HasTrie s => StateTrie s a -> s -> (a,s)
runStateTrie (StateTrie t) = untrie t
{-# INLINE runStateTrie #-}

-- | Run a memoized stateful computation and return just value
evalStateTrie :: HasTrie s => StateTrie s a -> s -> a
evalStateTrie = (result.result) fst runStateTrie
{-# INLINE evalStateTrie #-}

-- | Run a memoized stateful computation and return just state
execStateTrie :: HasTrie s => StateTrie s a -> s -> s
execStateTrie = (result.result) snd runStateTrie
{-# INLINE execStateTrie #-}

instance HasTrie s => Functor (StateTrie s) where
  fmap = inStateTrie . fmap . first
  {-# INLINE fmap #-}

instance HasTrie s => Applicative (StateTrie s) where
  pure a = StateTrie (trie (a,))
  (<*>)  = inState2 (<*>)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

-- | 'State'-to-'StateTrie' adapter
fromState :: HasTrie s => State s a -> StateTrie s a
fromState = StateTrie . trie . runState
{-# INLINE fromState #-}

-- | 'StateTrie'-to-'State' adapter
toState :: HasTrie s => StateTrie s a -> State s a
toState = state . untrie . unStateTrie
{-# INLINE toState #-}

-- | Transform using 'State' view
inState :: (HasTrie s, HasTrie t) =>
           (State     s a -> State     t b)
        -> (StateTrie s a -> StateTrie t b)
inState = fromState <~ toState
{-# INLINE inState #-}

-- | Transform using 'State' view
inState2 :: (HasTrie s, HasTrie t, HasTrie u) =>
            (State     s a -> State     t b -> State     u c)
         -> (StateTrie s a -> StateTrie t b -> StateTrie u c)
inState2 = inState <~ toState
{-# INLINE inState2 #-}

instance HasTrie s => Monad (StateTrie s) where
  return  = pure
  m >>= f = joinST (fmap f m)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinST :: HasTrie s => StateTrie s (StateTrie s a) -> StateTrie s a
joinST = fromState . join . fmap toState . toState
{-# INLINE joinST #-}

-- joinST = inState (join . fmap toState)
--        = inState ((=<<) toState)

instance HasTrie s => MonadState s (StateTrie s) where
  state = StateTrie . trie

-- TODO: Perhaps use 'state' in the definitions of pure and fromState.

type instance Rep (StateTrie s a) = StateTrieX s a
instance HasRep (StateTrie s a) where
  repr (StateTrie t) = t
  abst = StateTrie


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | Add post- & pre-processing
(<~) :: (b -> b') -> (a' -> a) -> ((a -> b) -> (a' -> b'))
(h <~ f) g = h . g . f

-- | Add post-processing
result :: (b -> b') -> ((a -> b) -> (a -> b'))
result = (.)
-- result = (<~ id)
