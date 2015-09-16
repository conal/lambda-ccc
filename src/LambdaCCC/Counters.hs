{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.Counters
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Up- and down-counters
----------------------------------------------------------------------

module LambdaCCC.Counters where

-- TODO: explicit exports

import Data.Functor ((<$>))
import Data.Traversable (Traversable)
import Control.Applicative (Applicative(..),liftA2)

import Circat.Misc (Unop)
import Circat.Scan (LScan(..),lAlls,scanlT)
import Circat.Circuit (GS)
import Circat.Mealy

toggleIf :: Bool -> Unop Bool
toggleIf a = if a then not else id

type Counter f = f Bool -> (f Bool, Bool) 

{--------------------------------------------------------------------
    Linear versions
--------------------------------------------------------------------}

-- Increment/decrement a little-endian binary natural number:

upL, downL :: (Applicative f, Traversable f) => Counter f

upL bs = (liftA2 toggleIf alls bs, all')
 where
   (alls,all') = scanlT (&&) True bs

downL bs = (liftA2 toggleIf alls bs, all')
 where
   (alls,all') = scanlT (&&) True (not <$> bs)

-- Now make counters by iterating `upL` or 'downL'
upCounterL, downCounterL :: (GS (f Bool), Applicative f, Traversable f) =>
                            Mealy () (f Bool)
upCounterL   = iterateU (fst .   upL) (pure False)
downCounterL = iterateU (fst . downL) (pure True )

{--------------------------------------------------------------------
    Logarithmic versions
--------------------------------------------------------------------}

upF, downF :: (Applicative f, LScan f) => f Bool -> (f Bool, Bool)

upF bs = (liftA2 toggleIf alls bs, all')
 where
   (alls,all') = lAlls bs

downF bs = (liftA2 toggleIf alls bs, all')
 where
   (alls,all') = lAlls (not <$> bs)

-- Now make counters by iterating `upF` or 'downF'
upCounter, downCounter :: (GS (f Bool), Applicative f, LScan f) =>
                          Mealy () (f Bool)
upCounter   = iterateU (fst .   upF) (pure False)
downCounter = iterateU (fst . downF) (pure True )
