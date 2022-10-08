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

newtype KeyBox k = KeyBox k deriving (Show,Eq,Ord)

instance Avs (KeyBox k) where
  type Rep (KeyBox k) = SMap.Key
  toRep = const forall_
  repc _ _ = sTrue

data RMap k v = RMap (Map k v) deriving (Show,Eq,Ord)

instance Avs (RMap k v) where
  type Rep (RMap k v) = SMap.Map
  toRep = const forall_
  repc _ _ = sTrue

data MapAction v u
  = Insert v
  | Delete
  | Modify u
  deriving (Show,Eq,Ord)

data MapUpd k v u = MapUpd [(k, MapAction v u)] deriving (Show,Eq,Ord)

instance Avs (MapUpd k v u) where
  type Rep (MapUpd k v u) = SMap.Upd
  toRep = const forall_
  -- If we construct a static update of our own design, rather than
  -- build it up using data from the transaction context, then we
  -- won't know anything about it.
  repc _ _ = sTrue

insertU :: (Avs v) => ALang t (KeyBox k,v) (MapUpd k v u)
insertU = ArrP
  (\a b -> do
     m1 <- forall_
     m2 <- forall_
     k <- forall_
     constrain $ (_1 a) ./= k
     return $
       SMap.updM b m1 m2
       .=> (SMap.memberM (_1 a) m2
            .&& SMap.matchesM k m1 m2))

  (\(KeyBox k,v) -> MapUpd [(k, Insert v)])

modifyU :: (Avs u) => ALang t (KeyBox k,u) (MapUpd k v u)
modifyU = ArrP
  (\a b -> do
     m1 <- forall_
     m2 <- forall_
     k <- forall_
     constrain $ (_1 a) ./= k
     return $
       SMap.updM b m1 m2
       .=> ((SMap.memberM (_1 a) m1 .=> SMap.derivesM (_1 a) m1 m2)
            .&& SMap.matchesM k m1 m2))
  (\(KeyBox k,u) -> MapUpd [(k, Modify u)])

seqMapU :: ALang t (MapUpd k v u, MapUpd k v u) (MapUpd k v u)
seqMapU = ArrP
  (\a b -> do
     m1 <- forall_
     m2 <- forall_
     m3 <- forall_
     return $ 
       (SMap.updM (_1 a) m1 m2 .&& SMap.updM (_2 a) m2 m3)
       .=> SMap.updM b m1 m3)
  (\(MapUpd u1, MapUpd u2) -> MapUpd (u1 ++ u2))

idMapU :: ALang t () (MapUpd k v u)
idMapU = ArrP
  (\_ b -> do
     m <- forall_
     return $ SMap.updM b m m)
  (\_ -> MapUpd [])
