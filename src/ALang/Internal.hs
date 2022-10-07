{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang.Internal where

import Data.SBV
import Data.SBV.Either
import Data.SBV.Tuple
import Symbol

data ALang t a b where
  PipeRL
    :: (Avs a, Avs b, Avs c)
    => ALang t b c -> ALang t a b -> ALang t a c
  ATimes
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang t a1 b1 -> ALang t a2 b2 -> ALang t (a1,a2) (b1,b2)
  ASum
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang t a1 b1
    -> ALang t a2 b2
    -> ALang t (Either a1 a2) (Either b1 b2)
  AIte
    :: (Avs a, Avs b)
    => ALang t a b
    -> ALang t a b
    -> ALang t (Bool,a) b
  ArrF :: (Avs a, Avs b) => FSpec a b -> (a -> b) -> ALang t a b
  ArrP :: (Avs a, Avs b) => PSpec a b -> (a -> b) -> ALang t a b
  FxTerm :: (Avs a, Avs b) => t a b -> ALang t a b

data NoFx a b

noFx :: Fun a b -> ALang t a b
noFx a = case a of
  PipeRL a1 a2 -> PipeRL (noFx a1) (noFx a2)
  ATimes a1 a2 -> ATimes (noFx a1) (noFx a2)
  ASum a1 a2 -> ASum (noFx a1) (noFx a2)
  AIte a1 a2 -> AIte (noFx a1) (noFx a2)
  ArrF s f -> ArrF s f
  ArrP p f -> ArrP p f

type Fun a b = ALang NoFx a b

runFun :: Fun a b -> a -> b
runFun m = case m of
  PipeRL ml mr -> runFun ml . runFun mr 
  ATimes a1 a2 -> \(a,b) -> (runFun a1 a, runFun a2 b)
  ASum a1 a2 -> \m -> case m of
                        Left a -> Left $ runFun a1 a
                        Right a -> Right $ runFun a2 a
  AIte a1 a2 -> \m -> case m of
                        (True,a) -> runFun a1 a
                        (False,a) -> runFun a2 a
  ArrF _ f -> f
  ArrP _ f -> f

symbolize :: (Avs a, Avs b) => Fun a b -> PSpec a b
symbolize m a b = case m of
  PipeRL ml mr -> do
    z <- forall "step"
    constrain =<< symbolize mr a z
    symbolize ml z b
  ATimes m1 m2 -> (.&&)
    <$> symbolize m1 (_1 a) (_1 b)
    <*> symbolize m2 (_2 a) (_2 b)
  ASum ml mr -> do
    pl <- symbolize ml (fromLeft a) (fromLeft b)
    pr <- symbolize mr (fromRight a) (fromRight b)
    return $
      (isLeft a .=> (isLeft b .&& pl))
      .&& (isRight a .=> (isRight b .&& pr))
  AIte mT mF -> do
    pT <- symbolize mT (_2 a) b
    pF <- symbolize mF (_2 a) b
    return $ ite (_1 a) pT pF
  ArrF f _ -> do
    b' <- f a
    return (b' .== b)
  ArrP p _ -> p a b
