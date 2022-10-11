{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.Map where

import Prelude hiding (insert)

import Data.SBV
import Data.SBV.Control (registerUISMTFunction)
import Data.SBV.Internals (SolverContext)
import Data.SBV.Set

data Map

mkUninterpretedSort ''Map

data Key

mkUninterpretedSort ''Key

data Upd

mkUninterpretedSort ''Upd

memberM :: SKey -> SMap -> SBool
memberM = uninterpret "memberM"

matchesM :: SKey -> SMap -> SMap -> SBool
matchesM = uninterpret "matchesM"

derivesM :: SKey -> SMap -> SMap -> SBool
derivesM = uninterpret "derivesM"

updM :: SUpd -> SMap -> SMap -> SBool
updM = uninterpret "updM"

idMapUM :: SUpd
idMapUM = uninterpret "idMapUM"

insertsM :: SKey -> SUpd -> SBool
insertsM = uninterpret "insertsM"

insertUM :: SKey -> SUpd
insertUM = uninterpret "insertUM"

seqUM :: SUpd -> SUpd -> SUpd
seqUM = uninterpret "seqUM"

mapAx =
  -- Matches with membership implies derives
  ["(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (and (matchesM k m1 m2) (memberM k m1) (memberM k m2)) (derivesM k m1 m2))))"
  -- Derives implies membership
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (derivesM k m1 m2) (and (memberM k m1) (memberM k m2)))))"
  -- Derives is reflexive when member
  ,"(assert (forall ((k Key) (m1 Map))"
  ,"  (=> (memberM k m1) (derivesM k m1 m1))))"
  -- Derives is transitive
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map) (m3 Map))"
  ,"  (=> (and (derivesM k m1 m2) (derivesM k m2 m3)) (derivesM k m1 m3))))"
  -- Matches is reflexive
  ,"(assert (forall ((k Key) (m1 Map))"
  ,"  (matchesM k m1 m1)))"
  -- Matches is symmetric
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (matchesM k m1 m2) (matchesM k m2 m1))))"
  -- Matches is transitive
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map) (m3 Map))"
  ,"  (=> (and (matchesM k m1 m2) (matchesM k m2 m3)) (matchesM k m1 m3))))"
  -- Matches implies membership agreement
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (matchesM k m1 m2) (=> (memberM k m1) (memberM k m2)))))"
  -- Maps that match on all keys are equivalent
  ,"(assert (forall ((m1 Map) (m2 Map)) (= (= m1 m2) (forall ((k Key)) (matchesM k m1 m2)))))"
  -- Updates are total functions
  ,"(assert (forall ((u Upd) (m1 Map) (m2 Map) (m3 Map))"
  ,"  (=> (and (updM u m1 m2) (updM u m1 m3)) (= m2 m3))))"
  ,"(assert (forall ((u Upd) (m1 Map))"
  ,"  (exists ((m2 Map)) (updM u m1 m2))))"
  -- idMapUM
  ,"(assert (forall ((k Key)) (not (insertsM k idMapUM))))"
  -- insertsM
  ,"(assert (forall ((k Key) (u Upd) (m1 Map) (m2 Map))"
  ,"  (and (=> (and (updM u m1 m2) (not (insertsM k u))) (matchesM k m1 m2))"
  ,"       (=> (and (updM u m1 m2) (insertsM k u)) (memberM k m2)))))"
  -- insertUM
  ,"(assert (forall ((k Key)) (insertsM k (insertUM k))))"
  ,"(assert (forall ((k1 Key) (k2 Key)) (=> (distinct k1 k2) (not (insertsM k2 (insertUM k1))))))"
  -- seqUM
  ,"(assert (forall ((k Key) (u1 Upd) (u2 Upd)) (= (insertsM k (seqUM u1 u2)) (or (insertsM k u1) (insertsM k u2)))))"

  -- There are at least two distinct keys? Technically not always true,
  -- since our key domain could be Unit.  It also doesn't help with
  -- any tests so far, so I'm leaving it out for now.

  -- ,"(assert (exists ((k1 Key) (k2 Key)) (distinct k1 k2)))"
  ]

axioms :: Symbolic ()
axioms = do
  addAxiom "mapAx" mapAx
  u1 <- forall_
  k1 <- forall_
  m1 <- forall_
  m2 <- forall_
  constrain $
    memberM k1 m1
    .|| matchesM k1 m1 m2
    .|| derivesM k1 m1 m2
    .|| updM u1 m1 m2
    .|| insertsM k1 (seqUM (seqUM u1 idMapUM) (insertUM k1))

test :: IO ThmResult
test = do
  proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    axioms
    k <- forall_
    m1 <- forall_
    m2 <- forall_
    constrain $ memberM k m1
    return $ (matchesM k m1 m2) .=> memberM k m2
