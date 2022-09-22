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

{-| Subtract the config amount from the state, if the amount is
  available. -}
takeStock :: Atl IntReq Int () (Either String Int)
takeStock =
  -- Check that the state's value is greater than or equal to the
  -- transaction's config value.
   query atLeast
     -- If not, return an explanation of failure.
     (Const "Not enough stock.")
     -- If so, subtract the config value.  Then, return the config value.
     (updateS subU >>> getConf)
