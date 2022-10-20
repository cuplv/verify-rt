{-# LANGUAGE TypeFamilies #-}

module Transact where

import ALang
import Store.Model
import Symbol
import Verify

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.Maybe as SM

type Transact g w u b = Fun (Context g, w) (Maybe (u,b))

type Transact' g a b = Transact g a (GUpd g) b

tup2l1
  :: (Avs a, Avs b, Grant g1, Grant g2)
  => Transact' g1 a b
  -> Transact' (g1,g2) a b
tup2l1 t =
  tup2 $ \ctx a ->
  tup2' (tup2Ctx ctx) $ \ctx1 _ ->
  requireE (eform2 t ctx1 a) $ \r ->
  tup2' r $ \u1 b ->
  returnE ((u1 &&& idU) &&& b)

tup2l2
  :: (Avs a, Avs b, Grant g1, Grant g2)
  => Transact' g2 a b
  -> Transact' (g1,g2) a b
tup2l2 t =
  tup2 $ \ctx a ->
  tup2' (tup2Ctx ctx) $ \_ ctx2 ->
  requireE (eform2 t ctx2 a) $ \r ->
  tup2' r $ \u2 b ->
  returnE ((idU &&& u2) &&& b)

seqT
  :: (Avs a, Avs b, Avs c, Grant g)
  => GUpd g
  -> Transact' g a b
  -> Transact' g b c
  -> Transact' g a c
seqT w t1 t2 =
  tup2 $ \ctx a ->
  requireE (eform2 t1 ctx a) $ \r1 ->
  tup2' r1 $ \u1 b ->
  requireE (eform2 t2 ctx b) $ \r2 ->
  tup2' r2 $ \u2 c ->
  returnE (seqE w u1 u2 &&& c)

transactS
  :: (GState g ~ UState u, Grant g, Update u, Avs w, Avs b)
  => u 
  -> Transact g w u b
  -> Sy w
  -> TransactS g
transactS z f w ctx pre = do
  mu <- symbolize f (tuple (ctx, w))
  constrain $ SM.isJust mu
  let u = _1 (SM.fromJust mu)
  symU z u pre

check
  :: (GState g ~ UState u, Grant g, Update u, Avs w, Avs b)
  => (g,u)
  -> Symbolic () -- domain-specific axioms
  -> Transact g w u b
  -> Spec g
  -> IO (ThmResult, ThmResult)
check (gw,uw) ax f p = do
  r1 <- proveWith z3 {satTrackUFs = False} $ do
    ax
    conf <- forall "config"
    let t = transactS uw f conf
    tsSpec gw t p
  r2 <- proveWith z3 {satTrackUFs = False} $ do
    ax
    conf <- forall "config"
    let t = transactS uw f conf
    tsWrite gw t p
  return (r1,r2)

cancelE :: (Avs a, Avs b) => ALang t a (Maybe b)
cancelE = nothingE

requireE
  :: (Avs a, Avs b, Avs c)
  => ALang t a (Maybe b)
  -> (ALang t a b -> ALang t a (Maybe c))
  -> ALang t a (Maybe c)
requireE = bindJust
