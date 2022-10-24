{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.MaybeMap where

import Symbol

import Prelude hiding (insert,seq,lookup)

import Data.SBV
import Data.SBV.Control (registerUISMTFunction)
import Data.SBV.Maybe
import Data.SBV.Internals (SolverContext)

data MaybeMap

mkUninterpretedSort ''MaybeMap

data MaybeMapUpd

mkUninterpretedSort ''MaybeMapUpd

data MaybeMapVal

mkUninterpretedSort ''MaybeMapVal

data MaybeMapValUpd

mkUninterpretedSort ''MaybeMapValUpd

fname s = s ++ "XZMaybeMap"

type M = MaybeMap
type K = Integer
type V = Maybe MaybeMapVal
type U = MaybeMapUpd
type F = MaybeMapValUpd

empty :: SBV M
empty = uninterpret $ fname "empty"

singleton :: SBV K -> SBV V -> SBV M
singleton = uninterpret $ fname "singleton"

member :: SBV K -> SBV M -> SBool
member = uninterpret $ fname "member"

hasVal :: SBV K -> SBV V -> SBV M -> SBool
hasVal = uninterpret $ fname "hasVal"

match :: SBV K -> SBV M -> SBV M -> SBool
match = uninterpret $ fname "match"

valUpdate :: SBV F -> SBV V -> SBV V
valUpdate = uninterpret $ fname "valUpdate"

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

addAxioms' :: [String] -> Symbolic ()
addAxioms' ss = do
  addAxiom "MaybeMapAxioms" ss
  -- registerUISMTFunction member
  k <- forall_
  v <- forall_
  m <- forall_
  u <- forall_
  f <- forall_
  constrain $
    member k m .== member k m
    .|| hasVal k v m .== hasVal k v m
    .|| empty .== empty
    .|| singleton k v .== singleton k v
    .|| match k m m .== match k m m
    .|| modify k f .== modify k f
    .|| update u m m .== update u m m
    .|| insert k v .== insert k v
    .|| delete k .== delete k
    .|| seq identity identity identity .== seq identity identity identity
    .|| sJust u .== sJust u

axioms :: Axioms
axioms = mkAxiomLoader "MaybeMap" addAxioms'

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
  k <- forall_
  constrain $ member k s
  return k

lookup :: SBV K -> SBV M -> Symbolic (SBV (Maybe V))
lookup k s = do
  v <- forall_
  constrain $ hasVal k v s
  return $ ite (member k s) (sJust v) sNothing

anyEntry :: SBV M -> Symbolic (SBV K, SBV V)
anyEntry s = do
  k <- anyMember s
  v <- forall_
  constrain $ hasVal k v s
  return (k, v)

hasEmptyEntry :: SBV K -> SBV M -> Symbolic SBool
hasEmptyEntry k s = do
  v <- lookup k s
  return (isJust v .&& isNothing (fromJust v))

test3 :: IO ThmResult
test3 = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    applyAxioms axioms ss
    k <- forall_
    v <- forall_
    m <- forall_
    return $ hasVal k v m
