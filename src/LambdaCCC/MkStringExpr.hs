-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.MkStringExpr
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Tweaked mkStringExpr from coreSyn/MkCore in GHC API. The standard version
-- treats single-character strings specially, which makes for more
-- complicated-looking Core.
----------------------------------------------------------------------

module LambdaCCC.MkStringExpr (mkStringExpr) where

import Data.Char (ord)

import GhcPlugins hiding (mkStringExpr,mkStringExprFS)
import PrelNames (unpackCStringName,unpackCStringUtf8Name)

-- | Create a 'CoreExpr' which will evaluate to the given @String@
mkStringExpr   :: MonadThings m => String     -> m CoreExpr  -- Result :: String
mkStringExpr str

--   | null str
--   = return (mkNilExpr charTy)

--   | length str == 1
--   = do let the_char = mkCharExpr (head str)
--        return (mkConsExpr charTy the_char (mkNilExpr charTy))

  | all safeChar str
  = do unpack_id <- lookupId unpackCStringName
       return (App (Var unpack_id) (Lit (mkMachString str)))

  | otherwise
  = do unpack_id <- lookupId unpackCStringUtf8Name
       return (App (Var unpack_id) (Lit (mkMachString str)))

  where
    safeChar c = ord c >= 1 && ord c <= 0x7F
