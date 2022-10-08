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
  toRep (IntUpd i) = pure . fromIntegral $ i
  repc (IntUpd i) = repc i

instance AData IntUpd where
  type Content IntUpd = Int
  conA = ArrF return IntUpd
  deconA = ArrF return (\(IntUpd n) -> n)

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

intWitness :: (IntG, IntUpd)
intWitness = (undefined, undefined)

data IntG
  = IntG { envSub :: Maybe Int
         , capSub :: Maybe Int
         }

instance Avs IntG where
  type Rep IntG = (Maybe Integer, Maybe Integer)
  toRep (IntG e c) = fmap tuple $
    (,) <$> toRep e <*> toRep c
  repc (IntG e c) = repc (e,c)

instance AData IntG where
  type Content IntG = (Maybe Int, Maybe Int)
  conA = ArrF return (\(e,c) -> IntG e c)
  deconA = ArrF return (\(IntG e c) -> (e,c))

instance Grant IntG where
  type GUpd IntG = IntUpd
  readG _ g s1 s2 = return $
    (s1 .>= s2)
    .&& SM.maybe sTrue (\n -> s1 .<= s2 + n) (_1 g)
  writeG _ g s1 s2 = return $
    (s1 .>= s2)
    .&& SM.maybe sTrue (\n -> s1 .<= s2 + n) (_2 g)
  useG _ = ArrF
    (\a -> let u = _1 a
               g = _2 a
               f n = ite (n .>= (-u) .&& u .<= 0) 
                         (SM.sJust $ tuple (_1 g, SM.sJust (n + u))) 
                         SM.sNothing
           in return $ SM.maybe (SM.sJust g) f (_2 g))
    (\(IntUpd u,g) -> case capSub g of
                        Just n | n >= (-u) && u <= 0 -> Just $ g { capSub = Just $ n + u }
                        Just n -> Nothing
                        Nothing -> Just g)

lowerBound :: ALang t (Context IntG) (Either () Int)
lowerBound =
  (getState &&& (getGrant >>> deconA >>> tup2g1 >>> m2eA))
  >>> distA
  >>> (constA () +++ diffA)

atLeast :: ALang t (Int, Context IntG) Bool
atLeast =
  sndA lowerBound
  >>> distA
  >>> (constA False ||| leA)

canSub :: ALang t (Int, Context IntG) Bool
canSub =
  sndA (getGrant >>> deconA >>> tup2g2 >>> m2eA)
  >>> distA
  >>> (constA True ||| leA)

data IntReq
  = IntReq { irAtLeast :: Maybe Int
           , irAbsSub :: Maybe Int
           , irDiffSub :: Maybe Int
           }

instance Avs IntReq where
  type Rep IntReq = (Maybe Integer, Maybe Integer, Maybe Integer)
  toRep (IntReq a b c) = fmap tuple $
    (,,) <$> toRep a <*> toRep b <*> toRep c
  repc (IntReq a b c) = repc (a,b,c)

instance AData IntReq where
  type Content IntReq = (Maybe Int, Maybe Int, Maybe Int)
  conA = ArrF return (\(a,b,c) -> IntReq a b c)
  deconA = ArrF return (\(IntReq a b c) -> (a,b,c))

instance Request IntReq where
  type Gr IntReq = IntG
  seqR = undefined
  seqCR = undefined
  minReq = undefined
  emptyReq = IntReq { irAtLeast = Nothing
                    , irAbsSub = Just 0
                    , irDiffSub = Nothing
                    }
  reqPred = undefined
  -- reqPred (IntReq al as ds) = andAllA [b1,b2]
  --   where b1 = case al of
  --                Just s -> lowerBound
  --                          >>> onLeft (constA False)
  --                          >>> onRight ((constA s &&& idA) >>> leA)
  --                          >>> selectA
  --                Nothing -> constA True
  --         b2 = case as of
  --                Just n -> getGrant >>> deconA >>> tup2g2 >>> m2eA
  --                          >>> onLeft (constA False)
  --                          >>> onRight ((constA n &&& idA) >>> geA)
  --                          >>> selectA
  --                Nothing -> constA True

-- atLeastR :: ReqMake Int IntReq
-- atLeastR = ReqMake
--   (\i -> IntReq (Just i) Nothing Nothing)
--   (sndA (getGrant >>> deconA >>> tup2g1 >>> m2eA)
--    >>> distA
--    >>> (constA False ||| leA))

addU :: ALang t Int IntUpd
addU = conA

subU :: ALang t Int IntUpd
subU = negateA >>> conA
