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
  Arr :: (Avs a, Avs b) => (VSpec a b) -> (a -> b) -> ALang t a b
  FxTerm :: (Avs a, Avs b) => t a b -> ALang t a b

data NoFx a b

noFx :: Fun a b -> ALang t a b
noFx a = case a of
  PipeRL a1 a2 -> PipeRL (noFx a1) (noFx a2)
  ATimes a1 a2 -> ATimes (noFx a1) (noFx a2)
  ASum a1 a2 -> ASum (noFx a1) (noFx a2)
  Arr s f -> Arr s f

type Fun a b = ALang NoFx a b

runFun :: Fun a b -> a -> b
runFun m = case m of
  PipeRL ml mr -> runFun ml . runFun mr 
  ATimes a1 a2 -> \(a,b) -> (runFun a1 a, runFun a2 b)
  ASum a1 a2 -> \m -> case m of
                        Left a -> Left $ runFun a1 a
                        Right a -> Right $ runFun a2 a
  Arr _ f -> f

symbolize :: (Avs a, Avs b) => Fun a b -> VSpec a b
symbolize m a = case m of
  PipeRL ml mr -> do
    b <- symbolize mr a
    symbolize ml b
  ATimes m1 m2 -> do 
    b1 <- symbolize m1 (_1 a)
    b2 <- symbolize m2 (_2 a)
    return $ tuple (b1, b2)
  ASum ml mr -> do
    bl <- symbolize ml (fromLeft a)
    br <- symbolize mr (fromRight a)
    let b = Data.SBV.Either.either (const $ sLeft bl) (const $ sRight br) a
    return b
  Arr s _ -> s a
