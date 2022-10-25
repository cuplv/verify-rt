{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.IntMap where

import ALang
import ALang.Construct
import Symbol
import qualified Symbol.IntMap as SMap
import Store.Model
import qualified Store.Model.Int as I
import Transact

import qualified Data.Map as Map
import Data.SBV
import Data.SBV.Maybe
import Data.SBV.Tuple

type Key = Int

data Val a
  = Val { valMain :: Int
        , valAux :: a
        }
  deriving (Show,Eq,Ord)

instance Avs (Val a) where
  type Rep (Val a) = SMap.V

instance Avc (Val a) where
  toRep (Val n _) = toRep n
  repc (Val n1 _) n2 = repc n1 n2

instance (Avs a) => AData (Val a) where
  type Content (Val a) = (Int, a)
  conA = ArrF (pure . _1) (\(a,b) -> Val a b)
  deconA = ArrF
    (\a -> do
      v <- forall_
      return $ tuple (a,v))
    (\(Val a b) -> (a,b))

data Map a = Map (Map.Map Key (Val a)) deriving (Show,Eq,Ord)

type Map' = Map ()

instance Avs (Map a) where
  type Rep (Map a) = SMap.M

empty :: (Avs a) => ALang t a (Map b)
empty = undefined

singleton :: (Avs a) => ALang t a (Key, Val b) -> ALang t a (Map b)
singleton = undefined

data Action a
  = Insert (Val a)
  | Modify I.IntUpd
  | Delete
  deriving (Show,Eq,Ord)

data Upd a = Upd (Map.Map Key (Action a)) deriving (Show,Eq,Ord)

instance Avs (Upd a) where
  type Rep (Upd a) = SMap.U

instance Update (Upd a) where
  type UState (Upd a) = Map a
  mkIdU = arrC SMap.identity (Upd Map.empty)
  seqU _ = ArrF
    undefined
    -- (\a -> pure $ SMap.seq (_1 a) (_2 a))
    undefined
  applyU _ = ArrP
    (\a b -> pure $ SMap.update (_1 a) (_2 a) b)
    undefined

insert' :: (Avs a) => ALang t (Key, Val a) (Upd a)
insert' = ArrF
  (\a -> pure $ SMap.insert (_1 a) (_2 a))
  undefined

insert 
  :: (Avs a, Avs b)
  => ALang t a Key 
  -> ALang t a (Val b)
  -> ALang t a (Upd b)
insert = eform2 insert'

modify 
  :: (Avs a, Avs b)
  => ALang t a Key 
  -> ALang t a I.IntUpd 
  -> ALang t a (Upd b)
modify = eform2 $ ArrF
  (\a -> pure $ SMap.modify (_1 a) (_2 a))
  undefined

delete' :: (Avs a) => ALang t Key (Upd a)
delete' = ArrF
  (\a -> pure $ SMap.delete a)
  undefined

delete
  :: (Avs a, Avs b)
  => ALang t a Key 
  -> ALang t a (Upd b)
delete = eform delete'

-- We don't actually want AData, since we have multiple constructors (insert, modify, delete) and we don't care about deconstructing.

-- instance AData (Upd a b) where

data G1 a
  = G1 (Maybe Key)
  deriving (Show,Eq,Ord)

instance Avs (G1 a) where
  type Rep (G1 a) = Maybe (Rep Key)

instance AData (G1 a) where
  type Content (G1 a) = Maybe Key
  conA = ArrF return G1
  deconA = ArrF return (\(G1 a) -> a)

instance Grant (G1 a) where
  type GUpd (G1 a) = Upd a
  readG _ g s1 s2 = do
    return $ Data.SBV.Maybe.maybe
      sTrue
      (\k -> SMap.match k s1 s2)
      g
  writeG _ g s1 s2 = do
    k1 <- forall_
    return $ Data.SBV.Maybe.maybe
      (s1 .== s2)
      (\k -> (k ./= k1) .=> SMap.match k1 s1 s2)
      g
  useG = undefined

memberE 
  :: (Avs a, Avs b) 
  => ALang t a Key 
  -> ALang t a (Map b) 
  -> ALang t a Bool
memberE = eform2 $ ArrF
  (\a -> pure $ SMap.member (_1 a) (_2 a))
  undefined

lookupE
  :: (Avs a, Avs b)
  => ALang t a Key
  -> ALang t a (Map b)
  -> ALang t a (Maybe (Val b))
lookupE = eform2 $ ArrF
  (\a -> SMap.lookup (_1 a) (_2 a))
  undefined

witness :: (G1 a, Upd a)
witness = (undefined, undefined)

data G2 a
  = G2 { g2Read :: Map ()
       , g2Write :: Map ()
       }
  deriving (Show,Eq,Ord)

instance Avs (G2 a) where
  type Rep (G2 a) = (SMap.M, SMap.M)

instance Grant (G2 a) where
  type GUpd (G2 a) = Upd a
  readG _ g s1 s2 = do
    undefined
  writeG _ g s1 s2 = do
    undefined
  useG = undefined

witness2 :: (G2 a, Upd a)
witness2 = (undefined, undefined)

memSubSet :: (Avs a) => ALang t a Map' -> ALang t a Map' -> ALang t a Bool
memSubSet = eform2 $ ArrF
  (\a -> do
    k <- forall_
    constrain $ SMap.member k (_1 a)
    return $ SMap.member k (_2 a))
  undefined

testMemSubSet = do
  ss <- loadAxioms SMap.axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms SMap.axioms ss
    m1 <- forall "m1"
    constrain $ SMap.empty m1
    m2 <- forall "m2"
    k <- forall_
    v <- forall_
    constrain $ SMap.singleton k v m2
    r <- symbolize (unEform2 memSubSet) (tuple (m1,m2))
    return r

meetIntMaps 
  :: (Avs a)
  => Fun2 Int Int Int
  -> ALang t a Map' 
  -> ALang t a Map'
  -> ALang t a Map'
meetIntMaps f = eform2 $ ArrP
  (\a m3 -> pure $ SMap.diffMap (_1 a) (_2 a) m3)
  -- (\a -> do
  --   let m1 = _1 a
  --       m2 = _2 a
  --   k <- forall_
  --   v1 <- forall_
  --   constrain $ SMap.member k m1 .=> SMap.hasVal k v1 m1
  --   v2 <- forall_
  --   constrain $ SMap.member k m2 .=> SMap.hasVal k v2 m2
  --   v3' <- symbolize (unEform2 f) (tuple (v1,v2))
  --   m3 <- forall_
  --   constrain $ ite
  --     (SMap.member k m1 .&& SMap.member k m2)
  --     (SMap.hasVal k v3' m3)
  --     (sNot $ SMap.member k m3)
  --   return m3)
  undefined

testIntMaps1 = do
  ss <- loadAxioms SMap.axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms SMap.axioms ss
    m1 <- forall "m1"
    constrain $ SMap.empty m1
    m2 <- forall "m2"
    k <- forall_
    v <- forall_
    constrain $ SMap.singleton k v m2
    m3 <- symbolize (unEform2 $ meetIntMaps (eform2 tup2g1)) (tuple (m1,m2))
    return $ m1 .== m3

testIntMaps2 = do
  ss <- loadAxioms SMap.axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms SMap.axioms ss
    m1 <- forall "m1"
    m2 <- forall "m2"
    k <- forall_
    v1 <- forall_
    v2 <- forall_
    constrain $ SMap.singleton k v1 m1
    constrain $ SMap.singleton k v2 m2
    m3 <- symbolize (unEform2 $ meetIntMaps (eform2 tup2g1)) (tuple (m1,m2))
    return $ SMap.hasVal k (v1 - v2) m3
