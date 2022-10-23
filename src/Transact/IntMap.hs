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

takeStock :: (Avs a) => Transact a StockG (IMap.Key, Int) Int
takeStock ctx cfg =
  tup2' cfg $ \key amt ->
  requireE (deconE $ grantE ctx) $ \k1 ->
  assertA (key $== k1) $
  IMap.intMapLift key Int.takeStock ctx amt

nonNegative :: Sy (IMap.Map a) -> Sy (IMap.Map a) -> Symbolic SBool
nonNegative s1 s2 = do
  (k,v1) <- SIMap.anyEntry s1
  mv2 <- SIMap.lookup k s2
  return $ SMaybe.maybe
    sTrue
    (\v2 -> (v1 .>= 0) .=> (v2 .>= 0))
    mv2
