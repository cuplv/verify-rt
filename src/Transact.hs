{-# LANGUAGE TypeFamilies #-}

module Transact where

import ALang
import ALang.Construct
import Store.Model
import Symbol
import Verify

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.Maybe as SM

type Transact a g w r
  = Fun a (Context g) -> Fun a w -> Fun a (Maybe (GUpd g, r))

type TransactComp g w r
  = Transact (Context g, w) g w r

tup2l1
  :: (Avs a, Avs w, Avs r, Grant g1, Grant g2)
  => Transact a g1 w r
  -> Transact a (g1,g2) w r
tup2l1 t ctx a =
  tup2' (tup2Ctx ctx) $ \ctx1 _ ->
  requireE (t ctx1 a) $ \r ->
  tup2' r $ \u1 b ->
  returnE ((u1 &&& idU) &&& b)

tup2l2
  :: (Avs a, Avs w, Avs r, Grant g1, Grant g2)
  => Transact a g2 w r
  -> Transact a (g1,g2) w r
tup2l2 t ctx a =
  tup2' (tup2Ctx ctx) $ \_ ctx2 ->
  requireE (t ctx2 a) $ \r ->
  tup2' r $ \u2 b ->
  returnE ((idU &&& u2) &&& b)

seqT
  :: (Avs x, Avs a, Avs b, Avs c, Grant g)
  => GUpd g
  -> Transact x g a b
  -> Transact x g b c
  -> Transact x g a c
seqT w t1 t2 ctx a =
  requireE (t1 ctx a) $ \r1 ->
  tup2' r1 $ \u1 b ->
  requireE (t2 ctx b) $ \r2 ->
  tup2' r2 $ \u2 c ->
  returnE (seqE w u1 u2 &&& c)

transactS
  :: (Grant g, Avs a, Avs b)
  => GUpd g
  -> Fun (Context g, a) (Maybe (GUpd g, b))
  -> Sy a
  -> TransactS g
transactS z f w ctx pre = do
  mu <- symbolize f (tuple (ctx, w))
  constrain $ SM.isJust mu
  let u = _1 (SM.fromJust mu)
  symU z u pre

trueThm :: ThmResult -> Bool
trueThm t =
  not (modelExists t)
  && case t of
       (ThmResult (Unknown _ UnknownTimeOut)) -> False
       _ -> True

iResult :: (ThmResult, ThmResult) -> Either () ()
iResult (a,b) = if trueThm a && trueThm b
                   then Right ()
                   else Left ()

checkWith
  :: (Grant g, Avs w, Avs r)
  => (g, GUpd g)
  -> Axioms -- domain-specific axioms
  -> TransactComp g w r
  -> Spec g
  -> IO (ThmResult, ThmResult)
checkWith (gw,uw) ax f p = do
  ss <- loadAxioms ax
  r1 <- proveWith z3 {satTrackUFs = False} $ do
    setTimeOut 2000
    applyAxioms ax ss
    conf <- forall "config"
    let t = transactS uw (f tup2g1 tup2g2) conf
    tsSpec gw t p
  r2 <- proveWith z3 {satTrackUFs = False} $ do
    setTimeOut 2000
    applyAxioms ax ss
    conf <- forall "config"
    let t = transactS uw (f tup2g1 tup2g2) conf
    tsWrite gw t p
  return (r1,r2)

check
  :: (Grant g, Avs w, Avs r)
  => (g, GUpd g)
  -> TransactComp g w r
  -> Spec g
  -> IO (ThmResult, ThmResult)
check (gw,uw) f p = do
  r1 <- proveWith z3 {satTrackUFs = False} $ do
    setTimeOut 2000
    conf <- forall "config"
    let t = transactS uw (f tup2g1 tup2g2) conf
    tsSpec gw t p
  r2 <- proveWith z3 {satTrackUFs = False} $ do
    setTimeOut 2000
    conf <- forall "config"
    let t = transactS uw (f tup2g1 tup2g2) conf
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
