{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module ALang.Example where

import ALang
import Atl
import Data.Map (Map)
import Data.SBV
import qualified Data.SBV.List as SList
import Store.Model
import Store.Model.Int
import Symbol

{-| Subtract the config amount from the state, if the amount is
  available. -}
takeStock :: Atl IntReq Int () Int
takeStock =
  -- Require that the state's value is greater than or equal to the
  -- transaction's config value.
  request atLeast
  -- Subtract the config value.
  >>> updateS subU 
  -- Then, return the config value.
  >>> getConf

nonNegative :: (Avs a, Avs b) => AtlSpec IntReq Int a b
nonNegative = prePost
  (\s -> s .>= 0)
  (\s -> s .>= 0)
