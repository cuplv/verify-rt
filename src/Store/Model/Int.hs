{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.Int where

import ALang
import ALang.Construct
import Atl
import Symbol
import Store.Model

data IntUpd = IntUpd Int

instance Avs IntUpd where
  type Rep IntUpd = Integer
  toRep (IntUpd i) = fromIntegral i

instance AData IntUpd where
  type Content IntUpd = Int
  conA = Arr return IntUpd
  deconA = Arr return (\(IntUpd n) -> n)

instance Update IntUpd where
  type UState IntUpd = Int
  idU = IntUpd 0
  seqU =
    ATimes deconA deconA
    >>> sumA
    >>> conA
  applyU =
    fstA deconA
    >>> sumA

data IntCap = IntCap (Maybe Int)

instance Avs IntCap where
  type Rep IntCap = Maybe Integer
  toRep (IntCap m) = fromIntegral <$> m

instance AData IntCap where
  type Content IntCap = Maybe Int
  conA = Arr return IntCap
  deconA = Arr return (\(IntCap a) -> a)

instance Capability IntCap where
  type KUpd IntCap = IntUpd

data IntReq
  = IntReq { irAtLeast :: Maybe Int
           , irAbsSub :: Maybe Int
           , irDiffSub :: Maybe Int
           }

instance Request IntReq where
  type Cap IntReq = IntCap

atLeast :: ReqMake Int IntReq
atLeast = ReqMake
  (\i -> IntReq (Just i) Nothing Nothing)
  (sndA (getEnv >>> deconA >>> m2eA)
   >>> distA
   >>> (constA False ||| leA))

addU :: ALang t Int IntUpd
addU = conA

subU :: ALang t Int IntUpd
subU = negateA >>> conA
