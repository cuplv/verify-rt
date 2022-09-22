{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang.Internal where

import Data.SBV
import Data.SBV.Either
import Data.SBV.Tuple
import Symbol

type FxSpec t a b = (Sy (FxRep t), Sy a) -> Symbolic (Sy (FxRep t), Sy b)

class (Avs (FxRep t)) => Fx t where
  type FxRep t :: *
  fxSym :: (Avs a, Avs b) => t a b -> FxSpec t a b

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
  FxTerm :: (Fx t, Avs a, Avs b) => t a b -> ALang t a b

symbolize :: (Fx t, Avs a, Avs b) => ALang t a b -> FxSpec t a b
symbolize m (s,a) = case m of
  PipeRL ml mr -> do
    (s1,b) <- symbolize mr (s,a)
    symbolize ml (s1,b)
  ATimes m1 m2 -> do 
    (s1,b1) <- symbolize m1 (s, _1 a)
    (s2,b2) <- symbolize m2 (s1, _2 a)
    return (s2, tuple (b1, b2))
  ASum ml mr -> do
    (sl,bl) <- symbolize ml (s, fromLeft a)
    (sr,br) <- symbolize mr (s, fromRight a)
    let s' = Data.SBV.Either.either (const sl) (const sr) a
        b = Data.SBV.Either.either (const $ sLeft bl) (const $ sRight br) a
    return (s',b)

data NoFx a b

instance Fx NoFx where
  type FxRep NoFx = ()
  fxSym = undefined

noFx :: Fun a b -> ALang t a b
noFx a = case a of
  PipeRL a1 a2 -> PipeRL (noFx a1) (noFx a2)
  ATimes a1 a2 -> ATimes (noFx a1) (noFx a2)
  ASum a1 a2 -> ASum (noFx a1) (noFx a2)
  Arr s f -> Arr s f

type Fun a b = ALang NoFx a b
