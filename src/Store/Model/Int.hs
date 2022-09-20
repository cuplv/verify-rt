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

data IntView
  = IntView { ivLow :: Maybe Int
            , ivHigh :: Maybe Int
            , ivAdd :: Maybe Int
            , ivSub :: Maybe Int
            }

data IntSd a b where
  IntUpdI :: IntSd Int IntUpd
  IntUpdE :: IntSd IntUpd Int

instance ValDomain IntSd where
  vdSymbol l = case l of
    IntUpdI -> VSpec return
    IntUpdE -> VSpec return
  vdFun l = case l of
    IntUpdI -> IntUpd
    IntUpdE -> \(IntUpd i) -> i
