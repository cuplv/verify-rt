{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.Int where

import ALang
import ALang.Construct
import Atl
import Symbol
import Store.Model

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.Maybe as SM

data IntUpd = IntUpd Int deriving (Show)

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
  seqU _ =
    ATimes deconA deconA
    >>> sumA
    >>> conA
  applyU _ =
    fstA deconA
    >>> sumA
  symU _ u s1 s2 = return $ s1 + u .== s2

data IntCap = IntCap (Maybe Int)

intWitness :: (IntCap, IntUpd)
intWitness = (undefined, undefined)

instance Avs IntCap where
  type Rep IntCap = Maybe Integer
  toRep (IntCap m) = fromIntegral <$> m

instance AData IntCap where
  type Content IntCap = Maybe Int
  conA = Arr return IntCap
  deconA = Arr return (\(IntCap a) -> a)

instance Capability IntCap where
  type KUpd IntCap = IntUpd
  reachC _ k s1 s2 = return $
    (s1 .>= s2)
    .&& SM.maybe (sTrue) (\n -> s1 .<= s2 + n) k
  constrainC _ = SM.maybe sTrue (\n -> n .>= 0)
  permitC _ = Arr
    (\a -> return $ SM.maybe sTrue (\n -> n .>= (-(_1 a))) (_2 a))
    (\(IntUpd u, IntCap m) -> case m of
                                Just n -> n >= u
                                Nothing -> True)
  -- permitC _ =
  --   fstA (deconA >>> negateA)
  --   >>> sndA (deconA >>> m2eA)
  --   >>> distA
  --   >>> (constA True ||| leA)

lowerBound :: ALang t (Context IntCap) (Either () Int)
lowerBound =
  (getState &&& (getEnv >>> deconA >>> m2eA))
  >>> distA
  >>> (constA () +++ diffA)

atLeast :: ALang t (Int, Context IntCap) Bool'
atLeast =
  sndA lowerBound
  >>> distA
  >>> (constA (Left ()) ||| (leA >>> b2eA))

canSub :: ALang t (Int, Context IntCap) (Either () ())
canSub =
  sndA (getCap >>> deconA >>> m2eA)
  >>> distA
  >>> (constA (Right ()) ||| (leA >>> b2eA))

-- lowerBound' :: ALang t (Context IntCap) (Either () (Either () (Int,Int)))
-- lowerBound' =
--   -- Context IntCap
--   (lowerBound &&& (getCap >>> deconA >>> m2eA))
--   -- (Either () Int, Either () Int)
--   >>> distA
--   -- Either () (Either () Int, Int)
--   >>> onRight (flipA >>> distA)
--   -- Either () (Either () (Int,Int))

data IntReq
  = IntReq { irAtLeast :: Maybe Int
           , irAbsSub :: Maybe Int
           , irDiffSub :: Maybe Int
           }

instance Request IntReq where
  type Cap IntReq = IntCap
  emptyReq = IntReq { irAtLeast = Nothing
                    , irAbsSub = Just 0
                    , irDiffSub = Nothing
                    }
  reqPred (IntReq al as ds) = andAllA [b1,b2]
    where b1 = case al of
                 Just s -> lowerBound
                           >>> onLeft (constA False)
                           >>> onRight ((constA s &&& idA) >>> leA)
                           >>> selectA
                 Nothing -> constA True
          b2 = case as of
                 Just n -> getCap >>> deconA >>> m2eA
                           >>> onLeft (constA False)
                           >>> onRight ((constA n &&& idA) >>> geA)
                           >>> selectA
                 Nothing -> constA True

atLeastR :: ReqMake Int IntReq
atLeastR = ReqMake
  (\i -> IntReq (Just i) Nothing Nothing)
  (sndA (getEnv >>> deconA >>> m2eA)
   >>> distA
   >>> (constA False ||| leA))

addU :: ALang t Int IntUpd
addU = conA

subU :: ALang t Int IntUpd
subU = negateA >>> conA
