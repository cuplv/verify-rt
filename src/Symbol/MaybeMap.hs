{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.MaybeMap where

import Symbol.Axioms

import Prelude hiding (insert,seq)

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

member :: SBV K -> SBV M -> SBool
member = uninterpret $ fname "member"

hasVal :: SBV K -> SBV V -> SBV M -> SBool
hasVal = uninterpret $ fname "hasVal"

match :: SBV K -> SBV M -> SBV M -> SBool
match = uninterpret $ fname "match"

valUpdate :: SBV F -> SBV V -> SBV V
valUpdate = uninterpret $ fname "valUpdate"

update :: SBV U -> SBV M -> SBV M
update = uninterpret $ fname "update"

identity :: SBV U
identity = uninterpret $ fname "identity"

insert :: SBV K -> SBV V -> SBV U
insert = uninterpret $ fname "insert"

modify :: SBV K -> SBV F -> SBV U
modify = uninterpret $ fname "modify"

delete :: SBV K -> SBV U
delete = uninterpret $ fname "delete"

seq :: SBV U -> SBV U -> SBV U
seq = uninterpret $ fname "seq"

addAxioms' :: [String] -> Symbolic ()
addAxioms' ss = do
  addAxiom "MaybeMapAxioms" ss
  k <- forall_
  v <- forall_
  m <- forall_
  u <- forall_
  f <- forall_
  constrain $
    member k m
    .|| hasVal k v m
    .|| match k m m
    .|| valUpdate f v .== v
    .|| modify k f .== identity
    .|| update u m .== m
    .|| insert k v .== delete k
    .|| seq identity identity .== identity
    .|| empty .== empty
    .|| sJust u .== sJust identity

test :: IO ThmResult
test = do
  ss <- loadAxioms "MaybeMap"
  proveWith (z3 {verbose = True, satTrackUFs = False}) $ do
    addAxioms' ss
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