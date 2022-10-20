{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.Maybe where

import ALang
import ALang.Construct
import Symbol
import Store.Model

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.Either as SE
import qualified Data.SBV.Maybe as SM

data MaybeUpd a u
  = MaybeUpd (Maybe (Either a u))
  deriving (Show,Eq,Ord)

type U u = MaybeUpd (UState u) u

instance (Avs a, Avs u) => Avs (MaybeUpd a u) where
  type Rep (MaybeUpd a u) = Maybe (Either (Rep a) (Rep u))
  toRep (MaybeUpd a) = toRep a
  repc = undefined

instance (Avs a, Avs u) => AData (MaybeUpd a u) where
  type Content (MaybeUpd a u) = Maybe (Either a u)
  conA = ArrF return MaybeUpd
  deconA = ArrF return (\(MaybeUpd a) -> a)

instance (Update u, UState u ~ a) => Update (MaybeUpd a u) where
  type UState (MaybeUpd a u) = Maybe a
  mkIdU = mkIdU >>> asRight >>> asJust >>> conA
  seqU = undefined
  applyU = undefined
  symU = undefined
