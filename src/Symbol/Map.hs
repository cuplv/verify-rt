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
  -- Matches is symmetric
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (matchesM k m1 m2) (matchesM k m2 m1))))"
  -- Matches is transitive
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map) (m3 Map))"
  ,"  (=> (and (matchesM k m1 m2) (matchesM k m2 m3)) (matchesM k m1 m3))))"
  -- Matches implies membership agreement
  ,"(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (matchesM k m1 m2) (=> (memberM k m1) (memberM k m2)))))"
  -- Updates are total functions
  ,"(assert (forall ((u Upd) (m1 Map) (m2 Map) (m3 Map))"
  ,"  (=> (and (updM u m1 m2) (updM u m1 m3)) (= m2 m3))))"
  ,"(assert (forall ((u Upd) (m1 Map))"
  ,"  (exists ((m2 Map)) (updM u m1 m2))))"
  ]

-- insertAx =
--   ["(assert (forall ((k Key) (m1 Map) (m2 Map))"
--   ,"  (=> (mapMod (insert k) m1 m2)"
--   ,"      (member k m2))))"
--   ,"(assert (forall ((k1 Key) (k2 Key) (m1 Map) (m2 Map))"
--   ,"  (=> (and (mapMod (insert k1) m1 m2) (distinct k1 k2) (member k2 m1))"
--   ,"      (matches k2 m1 m2))))"
--   ,"(assert (forall ((k1 Key) (k2 Key) (m1 Map) (m2 Map))"
--   ,"  (=> (and (mapMod (insert k1) m1 m2) (distinct k1 k2) (not (member k2 m1)))"
--   ,"      (not (member k2 m2)))))"
--   ]

-- modifyM :: SMapMod
-- modifyM = uninterpret "modifyM"

-- deleteM :: SMapMod
-- deleteM = uninterpret "deleteM"

-- retainM :: SMapMod
-- retainM = uninterpret "retainM"

-- seqMapMod :: SMapMod -> SMapMod -> SMapMod
-- seqMapMod x1 x2 = ite (x2 .== retainM) x1 x2

-- mapModAx =
--   ["(assert (forall ((x MapU))"
--   ,"  (or (= x insertM) (= x modifyM) (= x deleteM) (= x retainM))"]

-- mapMod :: SMapMod -> SMap -> SMap -> SBool
-- mapMod = uninterpret "mapMod"


-- ancestorAx =
--   ["(assert (forall ((k Key) (m1 Map)) (ancestor k m1 m1)))"
--   ,"(assert (forall ((k Key) (m1 Map) (m2 Map) (m3 Map)) (=> (and (ancestor k m1 m2) (ancestor k m2 m3)) (ancestor k m1 m3))))"
--   ]

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

test :: IO ThmResult
test = do
  proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    axioms
    k <- forall_
    m1 <- forall_
    m2 <- forall_
    constrain $ memberM k m1
    return $ (matchesM k m1 m2) .=> memberM k m2
    -- k1 <- forall_
    -- m1 <- forall_
    -- m2 <- forall_
    -- k2 <- forall_
    -- constrain $ k1 ./= k2
    -- constrain $ mapMod (insert k1) m1 m2
    -- constrain $ sNot (member k2 m1)
    -- return $ sNot (member k2 m2)
