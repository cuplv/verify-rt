{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.Int where

import ALang
import Symbol
import Store.Model
import ValDomain

data IntUpd = IntUpd Int

instance Avs IntUpd where
  type Rep IntUpd = Integer
  toRep (IntUpd i) = fromIntegral i

instance Update IntUpd where
  type UState IntUpd = Int
  idU = IntUpd 0
  seqU =
    ATimes (VdTerm IntUpdE) (VdTerm IntUpdE)
    >>> VdTerm Sum
    >>> VdTerm IntUpdI
  applyU =
    firstA (VdTerm IntUpdE)
    >>> VdTerm Sum

data IntCap = IntCap (Maybe Int)

instance Avs IntCap where
  type Rep IntCap = Maybe Integer
  toRep (IntCap m) = fromIntegral <$> m

instance Capability IntCap where
  type KUpd IntCap = IntUpd

data IntReq
  = IntReq { irAtLeast :: Maybe Int
           , irAbsSub :: Maybe Int
           , irDiffSub :: Maybe Int
           }

instance Avs IntReq where
  type Rep IntReq = (Maybe Integer, Maybe Integer, Maybe Integer)

instance Request IntReq where
  type Cap IntReq = IntCap

data IntSd a b where
  IntUpdI :: IntSd Int IntUpd
  IntUpdE :: IntSd IntUpd Int
  IntCapI :: IntSd (Maybe Int) IntCap
  IntCapE :: IntSd IntCap (Maybe Int)

instance ValDomain IntSd where
  vdSymbol l = case l of
    IntUpdI -> VSpec return
    IntUpdE -> VSpec return
    IntCapI -> VSpec return
    IntCapE -> VSpec return
  vdFun l = case l of
    IntUpdI -> IntUpd
    IntUpdE -> \(IntUpd i) -> i
    IntCapI -> IntCap
    IntCapE -> \(IntCap m) -> m
