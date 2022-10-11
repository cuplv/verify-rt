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
