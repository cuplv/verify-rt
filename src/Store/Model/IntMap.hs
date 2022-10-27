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
import qualified Data.SBV.Maybe as SMaybe
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

empty :: (Avs a) => ALang t a Map'
empty = ArrP
  (\_ b -> pure $ SMap.empty b)
  undefined

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

mapModify
  :: (Avs a, Avs b, Avs c)
  => ALang t a (Map b)
  -> ALang t a (Upd c)
mapModify = eform $ ArrF
  (\a -> pure $ SMap.mapModify a)
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

instance AData (G2 a) where
  type Content (G2 a) = (Map', Map')
  conA = ArrF
    pure
    (\(a,b) -> G2 a b)
  deconA = ArrF
    pure
    (\(G2 a b) -> (a,b))

mapAsCap :: SBV SMap.M -> SBV SMap.M -> SBV SMap.M -> SBool
mapAsCap g s1 s2 = do
  SMap.mapBound g s1 s2

testMapAsCap = do
  ss <- loadAxioms SMap.axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms SMap.axioms ss
    m1 <- forall_
    m2 <- forall_
    k <- forall_
    -- k2 <- forall_
    v <- forall_
    g <- forall_
    constrain $ SMap.member k g .&& SMap.hasVal k 0 g
    constrain $ mapAsCap g m1 m2
    constrain $ SMap.member k m1 .&& SMap.hasVal k 1 m1
    constrain $ SMap.member k m2 .&& SMap.hasVal k v m2
    return $ v .>= 1

instance Grant (G2 a) where
  type GUpd (G2 a) = Upd a
  -- May need to account for negative values in G2
  readG _ g s1 s2 = return $
    ite
      (SMap.mapLowerBound 0 (_1 g))
      (mapAsCap (_1 g) s1 s2)
      (s1 .== s2)
  writeG _ g s1 s2 = do
    (k,v) <- SMap.anyEntry (_2 g)
    r1 <- SMap.lookup k s1
    r2 <- SMap.lookup k s2
    return $
      (isJust r1 .<=> isJust r2)
      .&& (ite
             (isJust r1 .&& isJust r2 .&& v .>= 0)
             (SMaybe.fromJust r1 - v .<= SMaybe.fromJust r2)
             sTrue)
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

diffMap 
  :: (Avs a)
  => ALang t a Map' 
  -> ALang t a Map'
  -> ALang t a Map'
diffMap = eform2 $ ArrP
  (\a m3 -> pure $ SMap.diffMap (_1 a) (_2 a) m3)
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
    m3 <- symbolize (unEform2 $ diffMap) (tuple (m1,m2))
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
    m3 <- symbolize (unEform2 $ diffMap) (tuple (m1,m2))
    return $ SMap.hasVal k (v1 - v2) m3

testTotalSum = do
  ss <- loadAxioms SMap.axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms SMap.axioms ss
    m1 <- forall "m1"
    m2 <- forall "m2"
    v <- forall_
    constrain $ SMap.update SMap.identity m1 m2
    return $
      SMap.totalSum m1 v .<=> SMap.totalSum m2 v

testTotalSum2 = do
  ss <- loadAxioms SMap.axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms SMap.axioms ss
    m1 <- forall "m1"
    m2 <- forall "m2"
    m3 <- forall "m3"
    k1 <- forall_
    k2 <- forall_
    v1 <- forall "sum1"
    v2 <- forall "sum2"
    constrain $ SMap.update (SMap.modify k1 3) m1 m2
    constrain $ SMap.update (SMap.modify k2 2) m2 m3
    return $
      (SMap.totalSum m1 v1 .&& SMap.totalSum m3 v2)
      .=> (v1 + 5 .== v2)

geq
  :: (Avs a, Avs x) 
  => ALang t a (Map x) 
  -> ALang t a Int 
  -> ALang t a Bool
geq = eform2 $ ArrF
  (\a -> pure $ SMap.mapLowerBound (_2 a) (_1 a))
  undefined

lowerBound :: (Avs a, Avs x) => ALang t a (Context (G2 x)) -> ALang t a Map'
lowerBound = eform $ ArrP
  (\a b -> return $ ite
     (SMap.mapLowerBound 0 (_1 (_2 a)))
     (SMap.diffMap (_1 a) (_1 (_2 a)) b)
     (_1 a .== b))
  undefined

atLeast
  :: (Avs a, Avs x)
  => ALang t a (Context (G2 x))
  -> ALang t a Map'
  -> ALang t a Bool
atLeast ctx amts = diffMap (lowerBound ctx) amts `geq` ca 0

canSub
  :: (Avs a, Avs x)
  => ALang t a (Context (G2 x))
  -> ALang t a Map'
  -> ALang t a Bool
canSub ctx amts =
  tup2' (deconE (grantE ctx)) $ \_ w ->
  diffMap w amts `geq` ca 0
