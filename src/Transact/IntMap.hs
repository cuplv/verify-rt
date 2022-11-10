module Transact.IntMap where

import ALang
import Store.Model
import qualified Store.Model.Int as SInt
import qualified Store.Model.IntMap as IMap
import qualified Symbol.IntMap as SIMap
import Transact
import qualified Transact.Int as Int

import Data.SBV
import qualified Data.SBV.Maybe as SMaybe

type StockG = IMap.G1 ()

takeZeroStock :: (Avs a) => Transact a StockG (Int) Int
takeZeroStock ctx amt =
  requireE (deconE $ grantE ctx) $ \k1 ->
  intMapKey k1 Int.takeStock ctx (ca 0)

takeStock :: (Avs a) => Transact a StockG Int Int
takeStock ctx amt =
  requireE (deconE $ grantE ctx) $ \k1 ->
  intMapKey k1 Int.takeStock ctx amt

-- Given (CustomerId, amt), add the amt to that entry (requiring that
-- the entry exists). Return the observed resulting balance.
addBalance :: (Avs a) => Transact a (IMap.G1 ()) (Int,Int) Int
addBalance ctx cfg = 
  tup2' cfg $ \k amt ->
  assertA (amt $>= ca 0) $
  requireE (deconE $ grantE ctx) $ \_ ->
  requireE (IMap.lookupE k (stateE ctx)) $ \val ->
  tup2' (deconE val) $ \bal _ ->
  returnE (IMap.modify k (SInt.addU amt) &&& (bal $+ amt))

-- Given (CustomerId, amt), subtract the amt from that entry
-- (requiring that the entry exists, and that the resulting balance is
-- not less than 0). Return the observed resulting balance.
--
-- This is just like takeStock, except that we provide a key as input
-- that must match the capability-supplied key, rather than just
-- accepting any key.
subBalance :: (Avs a) => Transact a (IMap.G1 ()) (Int,Int) Int
subBalance ctx cfg = 
  tup2' cfg $ \k amt ->
  requireE (deconE $ grantE ctx) $ \k1 ->
  assertA (k $== k1) $
  intMapKey k1 Int.takeStock ctx amt

badTakeStock1 :: (Avs a) => Transact a StockG Int Int
badTakeStock1 ctx amt =
  requireE (deconE $ grantE ctx) $ \k1 ->
  intMapKey k1 Int.badTakeStock ctx amt

badTakeStock2 :: (Avs a) => Transact a StockG Int Int
badTakeStock2 ctx amt =
  requireE (deconE $ grantE ctx) $ \_ ->
  intMapKey (ca 8) Int.takeStock ctx amt

nonNegative :: Sy (IMap.Map a) -> Sy (IMap.Map a) -> Symbolic SBool
nonNegative s1 s2 = do
  (k,v1) <- SIMap.anyEntry s1
  mv2 <- SIMap.lookup k s2
  return $ SMaybe.maybe
    sTrue
    (\v2 -> (v1 .>= 0) .=> (v2 .>= 0))
    mv2

nonNegative' :: Integer -> Sy (IMap.Map a) -> Sy (IMap.Map a) -> Symbolic SBool
nonNegative' x s1 s2 = do
  (k,v1) <- SIMap.anyEntry s1
  mv2 <- SIMap.lookup k s2
  return $ SMaybe.maybe
    sTrue
    (\v2 -> (v1 .>= literal x) .=> (v2 .>= 0))
    mv2

witness = IMap.witness
axioms = SIMap.axioms

intMapKey
  :: (Avs a, Avs w, Avs r, Avs x)
  => Fun a IMap.Key
  -> Transact a SInt.IntG w r
  -> Transact a (IMap.G1 x) w r
intMapKey k t ctx a =
  requireE (IMap.lookupE k (stateE ctx)) $ \v ->
  tup2' (deconE v) $ \n _ ->
  letb (conE (n &&& SInt.mkUniG)) $ \ctx' ->
  requireE (t ctx' a) $ \r ->
  tup2' r $ \u b ->
  returnE (IMap.modify k u &&& b)

test3 = checkWith witness axioms takeStock nonNegative

witness2 = IMap.witness2

takeStockMulti
  :: (Avs a)
  => Transact a (IMap.G2 ()) (Int,IMap.Map') (Int,Int)
takeStockMulti ctx cfg =
  tup2' cfg $ \a amts ->
  assertA (amts `IMap.geq` ca 0) $
  -- assertA (ctx `IMap.atLeast` amts) $
  assertA (ctx `IMap.canSub` amts) $
  returnE (IMap.mapModify amts &&& (a &&& IMap.totalSum amts))

takeStockMultiBad
  :: (Avs a)
  => Transact a (IMap.G2 ()) IMap.Map' Int
takeStockMultiBad ctx amts =
  assertA (amts `IMap.geq` ca 0) $
  -- Whoops, we are merely checking whether the currently visible
  -- stocks are sufficient, without also considering remote
  -- interference.
  assertA (stateE ctx `IMap.geqMap` amts) $
  assertA (ctx `IMap.canSub` amts) $
  returnE (IMap.mapSubtract amts &&& IMap.totalSum amts)

singleton :: (Avs a) => ALang t a (IMap.Key, IMap.Val b) -> ALang t a (IMap.Map b)
singleton = IMap.singleton

type G2 = IMap.G2
type G1 = IMap.G1
type Map' = IMap.Map'
type Upd = IMap.Upd
