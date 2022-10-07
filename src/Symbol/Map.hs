{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.Map
  ( SMap
  , SKey
  , test
  ) where

import Prelude hiding (insert)

import Data.SBV
import Data.SBV.Control (registerUISMTFunction)
import Data.SBV.Internals (SolverContext)
import Data.SBV.Set

data Map

mkUninterpretedSort ''Map

data Key

mkUninterpretedSort ''Key

data MapMod

mkUninterpretedSort ''MapMod

type MapU = SKey -> MapMod

memberM :: SKey -> SMap -> SBool
memberM = uninterpret "memberM"

insertM :: SMapMod
insertM = uninterpret "insertM"

insertAx =
  ["(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (mapMod (insert k) m1 m2)"
  ,"      (member k m2))))"
  ,"(assert (forall ((k1 Key) (k2 Key) (m1 Map) (m2 Map))"
  ,"  (=> (and (mapMod (insert k1) m1 m2) (distinct k1 k2) (member k2 m1))"
  ,"      (matches k2 m1 m2))))"
  ,"(assert (forall ((k1 Key) (k2 Key) (m1 Map) (m2 Map))"
  ,"  (=> (and (mapMod (insert k1) m1 m2) (distinct k1 k2) (not (member k2 m1)))"
  ,"      (not (member k2 m2)))))"
  ]

modifyM :: SMapMod
modifyM = uninterpret "modifyM"

deleteM :: SMapMod
deleteM = uninterpret "deleteM"

retainM :: SMapMod
retainM = uninterpret "retainM"

seqMapMod :: SMapMod -> SMapMod -> SMapMod
seqMapMod x1 x2 = ite (x2 .== retainM) x1 x2

mapModAx =
  ["(assert (forall ((x MapU))"
  ,"  (or (= x insertM) (= x modifyM) (= x deleteM) (= x retainM))"]

mapMod :: SMapMod -> SMap -> SMap -> SBool
mapMod = uninterpret "mapMod"

matches :: SKey -> SMap -> SMap -> SBool
matches = uninterpret "matches"

ancestor :: SKey -> SMap -> SMap -> SBool
ancestor = uninterpret "ancestor"

ancestorAx =
  ["(assert (forall ((k Key) (m1 Map)) (ancestor k m1 m1)))"
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map) (m3 Map)) (=> (and (ancestor k m1 m2) (ancestor k m2 m3)) (ancestor k m1 m3))))"
  ]

axioms :: Symbolic ()
axioms = do
  addAxiom "ancestor" ancestorAx
  addAxiom "insert" insertAx 
  k1 <- forall_
  m1 <- forall_
  m2 <- forall_
  constrain $
    mapMod (insert k1) m1 m2
  constrain $
    member k1 m1
    .|| matches k1 m1 m2
    .|| ancestor k1 m1 m2

test :: IO ThmResult
test = do
  proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    axioms
    k1 <- forall_
    m1 <- forall_
    m2 <- forall_
    k2 <- forall_
    constrain $ k1 ./= k2
    constrain $ mapMod (insert k1) m1 m2
    constrain $ sNot (member k2 m1)
    return $ sNot (member k2 m2)
