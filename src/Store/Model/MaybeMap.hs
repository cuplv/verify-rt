{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.MaybeMap where

import ALang
import ALang.Construct
import Symbol
import qualified Symbol.MaybeMap as SMap
import Store.Model

import qualified Data.Map as Map
import Data.SBV
import Data.SBV.Maybe
import Data.SBV.Tuple

type Key = Int

data Val a b
  = Val { valMain :: Maybe a
        , valAux :: b
        }
  deriving (Show,Eq,Ord)

instance Avs (Val a b) where
  type Rep (Val a b) = SMap.V

instance Avc (Val a b) where
  toRep (Val (Just _) _) = sJust <$> forall_
  toRep _ = pure sNothing
  repc (Val (Just _) _) = isJust
  repc _ = isNothing

instance (Avs a, Avs b) => AData (Val a b) where
  type Content (Val a b) = (Maybe a, b)
  conA = ArrF
    (\a -> do
      v <- forall_
      return $ ite (isJust (_1 a))
                   (sJust v)
                   sNothing)
    (\(a,b) -> Val a b)
  deconA = ArrF
    (\a -> do
      v1 <- forall_
      v2 <- forall_
      return $ ite (isJust a) 
                   (tuple (sJust v1, v2)) 
                   (tuple (sNothing, v2)))
    (\(Val a b) -> (a,b))

-- data ValUpd a b = ValUpd (Maybe a, b) deriving (Show,Eq,Ord)

-- instance (Avs a, Avs b) => Avs (ValUpd a b) where
--   type Rep (ValUpd a b) = SMap.F

data Map a b = Map (Map.Map Int (Val a b))

instance Avs (Map a b) where
  type Rep (Map a b) = SMap.M
  -- toRep (Map m) | null m = pure SMap.empty
  --               | otherwise = forall_
  -- repc = undefined

empty :: (Avs a) => ALang t a (Map b c)
empty = undefined

singleton :: (Avs a) => ALang t a (Key, Val b c) -> ALang t a (Map b c)
singleton = undefined

data Action a b
  = Insert Key (Val a b)
  | Delete Key
  deriving (Show,Eq,Ord)

data Upd a b = Upd (Map.Map Key (Action a b)) deriving (Show,Eq,Ord)

instance Avs (Upd a b) where
  type Rep (Upd a b) = SMap.U
  -- toRep _ = forall_
  -- repc = error "repc is not defined"

instance Update (Upd a b) where
  type UState (Upd a b) = Map a b
  mkIdU = arrC SMap.identity (Upd Map.empty)
  seqU _ = ArrF
    (\a -> pure $ SMap.seq (_1 a) (_2 a))
    undefined
  applyU _ = ArrF
    (\a -> pure $ SMap.update (_1 a) (_2 a))
    undefined

insert :: (Avs a, Avs b) => ALang t (Key, Val a b) (Upd a b)
insert = ArrF
  (\a -> pure $ SMap.insert (_1 a) (_2 a))
  undefined

insertE 
  :: (Avs a, Avs b, Avs c) 
  => ALang t a Key 
  -> ALang t a (Val b c)
  -> ALang t a (Upd b c)
insertE = eform2 insert

delete :: (Avs a, Avs b) => ALang t Key (Upd a b)
delete = ArrF
  (\a -> pure $ SMap.delete a)
  undefined

deleteE 
  :: (Avs a, Avs b, Avs c) 
  => ALang t a Key 
  -> ALang t a (Upd b c)
deleteE = eform delete

-- We don't actually want AData, since we have multiple constructors (insert, modify, delete) and we don't care about deconstructing.

-- instance AData (Upd a b) where

data G1 a b
  = G1 (Maybe Key)
  deriving (Show,Eq,Ord)

instance Avs (G1 a b) where
  type Rep (G1 a b) = Maybe (Rep Key)

instance AData (G1 a b) where
  type Content (G1 a b) = Maybe Key
  conA = ArrF return G1
  deconA = ArrF return (\(G1 a) -> a)

instance Grant (G1 a b) where
  type GUpd (G1 a b) = Upd a b
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

memberE 
  :: (Avs a, Avs c, Avs b) 
  => ALang t a Key 
  -> ALang t a (Map c b) 
  -> ALang t a Bool
memberE = eform2 $ ArrF
  (\a -> pure $ SMap.member (_1 a) (_2 a))
  undefined

lookupE
  :: (Avs a, Avs c, Avs b)
  => ALang t a Key
  -> ALang t a (Map b c)
  -> ALang t a (Val b c)
lookupE = eform2 $ ArrF
  (\a -> do
    v <- forall_
    constrain $ SMap.hasVal (_1 a) v (_2 a)
    return v)
  undefined

witness :: (G1 a b, Upd a b)
witness = (undefined, undefined)
