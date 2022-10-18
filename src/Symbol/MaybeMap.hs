{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Symbol.MaybeMap where

import Symbol.Axioms

import Prelude hiding (insert,seq)

import Data.SBV
import Data.SBV.Control (registerUISMTFunction)
import Data.SBV.Internals (SolverContext)

data MaybeMap

mkUninterpretedSort ''MaybeMap

data MaybeMapUpd

mkUninterpretedSort ''MaybeMapUpd

fname s = s ++ "XZMaybeMap"

type M = SBV MaybeMap

type K = SBV Integer

type V = SBV Bool

type U = SBV MaybeMapUpd

empty :: M
empty = uninterpret $ fname "empty"

member :: K -> M -> SBool
member = uninterpret $ fname "member"

hasVal :: K -> V -> M -> SBool
hasVal = uninterpret $ fname "hasVal"

match :: K -> M -> M -> SBool
match = uninterpret $ fname "match"

update :: U -> M -> M
update = uninterpret $ fname "update"

identity :: U
identity = uninterpret $ fname "identity"

insert :: K -> V -> U
insert = uninterpret $ fname "insert"

delete :: K -> U
delete = uninterpret $ fname "delete"

seq :: U -> U -> U
seq = uninterpret $ fname "seq"

addAxioms' :: [String] -> Symbolic ()
addAxioms' ss = do
  addAxiom "MaybeMapAxioms" ss
  k <- forall_
  v <- forall_
  m <- forall_
  u <- forall_
  constrain $
    member k m
    .|| hasVal k v m
    .|| match k m m
    .|| update u m .== m
    .|| insert k v .== delete k
    .|| seq identity identity .== identity
    .|| empty .== empty

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
