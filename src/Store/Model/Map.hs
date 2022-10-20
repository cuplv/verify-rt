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

-- newtype KeyBox k = KeyBox k deriving (Show,Eq,Ord)

-- instance Avs (KeyBox k) where
--   type Rep (KeyBox k) = SMap.Key
--   toRep = const forall_
--   repc _ _ = sTrue

-- instance (Avs k) => AData (KeyBox k) where
--   type Content (KeyBox k) = k
--   conA = ArrF (\_ -> forall_) KeyBox
--   deconA = ArrF (\_ -> forall_) (\(KeyBox k) -> k)

-- data RMap k v = RMap (Map k v) deriving (Show,Eq,Ord)

-- instance Avs (RMap k v) where
--   type Rep (RMap k v) = SMap.Map
--   toRep = const forall_
--   repc _ _ = sTrue

-- data MapAction v u
--   = Insert v
--   | Delete
--   | Modify u
--   deriving (Show,Eq,Ord)

-- data MapUpd k v u = MapUpd [(k, MapAction v u)] deriving (Show,Eq,Ord)

-- instance Avs (MapUpd k v u) where
--   type Rep (MapUpd k v u) = SMap.Upd
--   toRep (MapUpd []) = return SMap.idMapUM
--   toRep _ = forall_
--   -- If we construct a static update of our own design, rather than
--   -- build it up using data from the transaction context, then we
--   -- won't know anything about it.
--   repc _ _ = sTrue

-- insertE 
--   :: (Avs a, Avs v) 
--   => ALang t a (KeyBox k) 
--   -> ALang t a v
--   -> ALang t a (MapUpd k v u)
-- insertE m1 m2 = (m1 &&& m2) >>> insertU

-- insertU :: (Avs v) => ALang t (KeyBox k,v) (MapUpd k v u)
-- insertU = ArrF
--   (\a -> return $ SMap.insertUM (_1 a))
--   (\(KeyBox k,v) -> MapUpd [(k, Insert v)])

-- modifyU :: (Avs u) => ALang t (KeyBox k,u) (MapUpd k v u)
-- modifyU = ArrP
--   (\a b -> do
--      m1 <- forall_
--      m2 <- forall_
--      k <- forall_
--      constrain $ (_1 a) ./= k
--      return $
--        SMap.updM b m1 m2
--        .=> ((SMap.memberM (_1 a) m1 .=> SMap.derivesM (_1 a) m1 m2)
--             .&& SMap.matchesM k m1 m2))
--   (\(KeyBox k,u) -> MapUpd [(k, Modify u)])

-- seqMapU :: ALang t (MapUpd k v u, MapUpd k v u) (MapUpd k v u)
-- seqMapU = ArrF
--   (\a -> return $ SMap.seqUM (_1 a) (_2 a))
--   (\(MapUpd u1, MapUpd u2) -> MapUpd (u1 ++ u2))

-- idMapU :: MapUpd k v u
-- idMapU = MapUpd []

-- applyMapU
--   :: (Ord k, Update u, UState u ~ v)
--   => ALang t (MapUpd k v u, Map k v) (Map k v)
-- applyMapU = ArrF
--   (\a -> do
--      b <- forall_
--      constrain $ SMap.updM (_1 a) (_2 a) b
--      return b)
--   (let f (u:us) m = f us $ case u of
--          (k, Insert v) -> Map.insert k v m
--          (k, Modify u) -> let up v = runFun (applyU u) (u,v)
--                           in Map.adjust up k m
--          (k, Delete) -> Map.delete k m
--        f [] m = m
--    in \(MapUpd us,m) -> f us m)

-- instance Avs (Map k v) where
--   type Rep (Map k v) = SMap.Map
--   toRep m | null m = do
--     k1 <- forall_
--     m1 <- forall_
--     constrain $ sNot (SMap.memberM k1 m1)
--     return m1
--   toRep _ = forall_
--   repc _ _ = sTrue

-- instance (Ord k, Update u, UState u ~ v) => Update (MapUpd k v u) where
--   type UState (MapUpd k v u) = Map k v
--   idU = idMapU
--   seqU _ = seqMapU
--   applyU _ = applyMapU

-- data MapG1 k v u
--   = MapG1 (Maybe (KeyBox k))

-- instance Avs (MapG1 k v u) where
--   type Rep (MapG1 k v u) = Rep (Maybe (KeyBox k))
--   toRep _ = forall_
--   repc _ _ = sTrue

-- instance AData (MapG1 k v u) where
--   type Content (MapG1 k v u) = (Maybe (KeyBox k))
--   conA = ArrF return MapG1
--   deconA = ArrF return (\(MapG1 a) -> a)

-- instance (Ord k, Update u, UState u ~ v) => Grant (MapG1 k v u) where
--   type GUpd (MapG1 k v u) = MapUpd k v u
--   readG _ g s1 s2 = do
--     return $ SM.maybe
--       sTrue
--       (\k -> SMap.matchesM k s1 s2)
--       g
--   writeG _ g s1 s2 = do
--     k1 <- forall_
--     return $ SM.maybe
--       (s1 .== s2)
--       (\k -> (k ./= k1) .=> SMap.matchesM k1 s1 s2)
--       g
--   useG = undefined

-- grantsKey :: ALang t (MapG1 k v u) Bool
-- grantsKey = deconA >>> onJust (ca True) >>> (ca False &&& idA) >>> fromJust

-- freshKey 
--   :: (Ord k, Update u, UState u ~ v, Avs a)
--   => ALang t a (Context (MapG1 k v u))
--   -> ALang t a Bool
-- freshKey m = m >>> (getState &&& (getGrant >>> deconA)) >>> maybeElim
--   (tup2 $ \s k -> notE $ memberE k s)
--   (ca False)

-- unused
--   :: (Ord k, Avs a)
--   => ALang t a (KeyBox k)
--   -> ALang t a (Map k v)
--   -> ALang t a Bool
-- unused k m = notE $ memberE k m

-- memberE
--   :: (Ord k, Avs a)
--   => ALang t a (KeyBox k)
--   -> ALang t a (Map k v)
--   -> ALang t a Bool
-- memberE m1 m2 = (m1 &&& m2) >>> ArrF
--   (\a -> return $ SMap.memberM (_1 a) (_2 a))
--   (\(KeyBox k, m) -> Map.member k m)

-- mapWitness :: (MapG1 Int String (NoUpd String), MapUpd Int String (NoUpd String))
-- mapWitness = (undefined,undefined)
