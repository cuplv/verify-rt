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

seqT
  :: (Avs a, Avs b, Avs c, Grant g1, Grant g2)
  => (GUpd g1, GUpd g2)
  -> Fun (Context g1, a) (Maybe (GUpd g1, b))
  -> Fun (Context g2, b) (Maybe (GUpd g2, c))
  -> Fun (Context (g1,g2), a) (Maybe (GUpd (g1,g2), c))
seqT (w1,w2) t1 t2 = 
  tup2 $ \ctx a ->
  tup2' (tup2Ctx ctx) $ \ctx1 ctx2 ->
  (ctx2 &&& eform2 t1 ctx1 a)
  >>> maybeElim
    (tup2 $ \ctx2 r ->
     tup2' r $ \u1 b ->
     (u1 &&& eform2 t2 ctx2 b)
     >>> maybeElim
       (tup2 $ \u1 r ->
        tup2' r $ \u2 c ->
        justE (seqE (w1,w2) (u1 &&& ca idU) (ca idU &&& u2) &&& c))
       (ca Nothing))
    (ca Nothing)

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
