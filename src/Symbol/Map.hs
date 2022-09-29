{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.Map
  ( SMap
  , SKey
  , SValue
  , test
  ) where

import Prelude hiding (insert)

import Data.SBV
import Data.SBV.Control (registerUISMTFunction)
import Data.SBV.Internals (SolverContext)

data Map

mkUninterpretedSort ''Map

data Key

mkUninterpretedSort ''Key

data Value

mkUninterpretedSort ''Value

data Update

mkUninterpretedSort ''Update

member :: SKey -> SMap -> SBool
member = uninterpret "member"

insert :: SKey -> SUpdate
insert = uninterpret "insert"

insertAx =
  ["(assert (forall ((k Key) (m1 Map) (m2 Map))"
  ,"  (=> (update (insert k) m1 m2)"
  ,"      (member k m2))))"
  ,"(assert (forall ((k1 Key) (k2 Key) (m1 Map) (m2 Map))"
  ,"  (=> (and (update (insert k1) m1 m2) (distinct k1 k2) (member k2 m1))"
  ,"      (matches k2 m1 m2))))"
  ,"(assert (forall ((k1 Key) (k2 Key) (m1 Map) (m2 Map))"
  ,"  (=> (and (update (insert k1) m1 m2) (distinct k1 k2) (not (member k2 m1)))"
  ,"      (not (member k2 m2)))))"
  ]

modify :: SKey -> SUpdate
modify = uninterpret "modify"

delete :: SKey -> SUpdate
delete = uninterpret "delete"

update :: SUpdate -> SMap -> SMap -> SBool
update = uninterpret "update"

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
    update (insert k1) m1 m2
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
    constrain $ update (insert k1) m1 m2
    constrain $ sNot (member k2 m1)
    return $ sNot (member k2 m2)
