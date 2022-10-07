{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.Map where

import ALang
import ALang.Construct
import Symbol
import qualified Symbol.Map as SMap
import Store.Model

import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.Maybe as SM
import Data.Set (Set)
import qualified Data.Set as Set

data RMap k v = RMap (Map k v) deriving (Show,Eq,Ord)

instance Avs (RMap k v) where
  type Rep (RMap k v) = SMap.Map
  toRep = const forall_
  repc _ _ = sTrue

data MapUpd k v = MapUpd (Map k (Maybe v)) deriving (Show,Eq,Ord)

instance Avs (MapUpd k v) where
  type Rep (MapUpd k v) = SMap.Upd
  toRep = const forall_
  -- If we construct a static update of our own design, rather than
  -- build it up using data from the transaction context, then we
  -- won't know anything about it.
  repc _ _ = sTrue
