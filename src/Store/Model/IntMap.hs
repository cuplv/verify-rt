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

data Map a = Map (Map.Map Key (Val a))

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
    (\a -> pure $ SMap.seq (_1 a) (_2 a))
    undefined
  applyU _ = ArrF
    (\a -> pure $ SMap.update (_1 a) (_2 a))
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

intMapLift 
  :: (Avs a, Avs w, Avs r, Avs x)
  => Fun a Key
  -> Transact2 a I.IntG w r
  -> Transact2 a (G1 x) w r
intMapLift k t ctx a =
  requireE (lookupE k (stateE ctx)) $ \v ->
  tup2' (deconE v) $ \n _ ->
  letb (conE (n &&& I.mkUniG)) $ \ctx' ->
  requireE (t ctx' a) $ \r ->
  tup2' r $ \u b ->
  returnE (modify k u &&& b)
