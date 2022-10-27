{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.IntMap where

import Symbol

import Prelude hiding (insert,seq,lookup)

import Data.SBV
import Data.SBV.Control (registerUISMTFunction)
import Data.SBV.Maybe
import qualified Data.SBV.Maybe as SMaybe
import Data.SBV.Internals (SolverContext)

data IntMap

mkUninterpretedSort ''IntMap

data IntMapUpd

mkUninterpretedSort ''IntMapUpd

fname s = s ++ "XZIntMap"

type M = IntMap
type K = Integer
type V = Integer
type U = IntMapUpd
type F = Integer

empty :: SBV M -> SBool
empty = uninterpret $ fname "empty"

singleton :: SBV K -> SBV V -> SBV M -> SBool
singleton = uninterpret $ fname "singleton"

member :: SBV K -> SBV M -> SBool
member = uninterpret $ fname "member"

hasVal :: SBV K -> SBV V -> SBV M -> SBool
hasVal = uninterpret $ fname "hasVal"

match :: SBV K -> SBV M -> SBV M -> SBool
match = uninterpret $ fname "match"

update :: SBV U -> SBV M -> SBV M -> SBool
update = uninterpret $ fname "update"

identity :: SBV U
identity = uninterpret $ fname "identity"

insert :: SBV K -> SBV V -> SBV U
insert = uninterpret $ fname "insert"

modify :: SBV K -> SBV F -> SBV U
modify = uninterpret $ fname "modify"

delete :: SBV K -> SBV U
delete = uninterpret $ fname "delete"

seq :: SBV U -> SBV U -> SBV U -> SBool
seq = uninterpret $ fname "seq"

offset :: SBV K -> SBV F -> SBV M -> SBV M -> SBool
offset = uninterpret $ fname "offset"

diffMap :: SBV M -> SBV M -> SBV M -> SBool
diffMap = uninterpret $ fname "diffMap"

totalSum :: SBV M -> SBV V -> SBool
totalSum = uninterpret $ fname "totalSum"

mapBound :: SBV M -> SBV M -> SBV M -> SBool
mapBound = uninterpret $ fname "mapBound"

mapModify :: SBV M -> SBV U
mapModify = uninterpret $ fname "mapModify"

mapLowerBound :: SBV V -> SBV M -> SBool
mapLowerBound = uninterpret $ fname "mapLowerBound"

addAxioms' :: [String] -> Symbolic ()
addAxioms' ss = do
  addAxiom "IntMapAxioms" ss
  k <- forall_
  v <- forall_
  m <- forall_
  u <- forall_
  f <- forall_
  constrain $
    member k m .== member k m
    .|| hasVal k v m .== hasVal k v m
    .|| empty m .== empty m
    .|| singleton k v m .== singleton k v m
    .|| match k m m .== match k m m
    .|| modify k f .== modify k f
    .|| update u m m .== update u m m
    .|| insert k v .== insert k v
    .|| delete k .== delete k
    .|| seq identity identity identity .== seq identity identity identity
    .|| sJust u .== sJust u
  constrain $
    offset k 1 m m .== offset k 1 m m
    .|| diffMap m m m .== diffMap m m m
    .|| totalSum m v .== totalSum m v
    .|| mapBound m m m .== mapBound m m m
    .|| mapModify m .== mapModify m
    .|| mapLowerBound v m .== mapLowerBound v m

axioms :: Axioms
axioms = mkAxiomLoader "IntMap" addAxioms'

test :: IO ThmResult
test = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms axioms ss
    k <- forall_
    m1 <- forall_
    m2 <- forall_
    constrain $ member k m1
    return $ match k m1 m2 .=> member k m2
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    addAxioms' ss
    k <- forall_
    m <- forall_
    return $ match k m m

anyMember :: SBV M -> Symbolic (SBV K)
anyMember s = do
  k <- forall "k"
  constrain $ member k s
  return k

lookup :: SBV K -> SBV M -> Symbolic (SBV (Maybe V))
lookup k s = do
  v <- forall "lookupV"
  constrain $ hasVal k v s
  return $ ite (member k s) (sJust v) sNothing

anyEntry :: SBV M -> Symbolic (SBV K, SBV V)
anyEntry s = do
  k <- anyMember s
  v <- forall "entryV"
  constrain $ hasVal k v s
  return (k, v)

test3 :: IO ThmResult
test3 = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms axioms ss
    m1 <- forall "m1"
    (k,v1) <- anyEntry m1
    -- mr <- forall_
    -- constrain $ match k m1 mr
    m2 <- forall "m2"
    -- u <- forall "u"
    -- constrain $
    --   ite (v1 .>= 3)
    --       (u .== modify k (-3))
    --       (u .== identity)
    -- constrain $ update u m1 m2
    constrain $ update (modify k 1) m1 m2
    (k2,v21) <- anyEntry m1
    -- constrain $ k2 ./= k
    mv2 <- lookup k2 m2
    mv2' <- forall_
    constrain $ mv2 .== mv2'
    return $ SMaybe.maybe
      sTrue
      (\v2 -> (v21 .>= 0) .=> (v2 .>= 0))
      mv2'

test4 :: IO ThmResult
test4 = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms axioms ss
    m1 <- forall "m1"
    m2 <- forall "m2"
    k <- forall "k"
    constrain $ update (modify k 2) m1 m2
    v1 <- forall "v1"
    constrain $ hasVal k v1 m1
    v2 <- forall "v2"
    constrain $ hasVal k v2 m2
    return $ v2 .== (v1 + 4)

test5 :: IO ThmResult
test5 = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms axioms ss
    m1 <- forall "m1"
    m2 <- forall "m2"
    k <- forall "k"
    v1 <- forall "v1"
    constrain $ hasVal k v1 m1
    v2 <- forall "v2"
    constrain $ hasVal k v2 m2
    return $ (v1 .== v2)
