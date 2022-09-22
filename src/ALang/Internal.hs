{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang.Internal where

import Data.SBV
import Symbol

type FxSpec t a b = (Sy (FxRep t), Sy a) -> Symbolic (Sy (FxRep t), Sy b)

class (Avs (FxRep t)) => Fx t where
  type FxRep t :: *
  fxSym :: (Avs a, Avs b) => t a b -> FxSpec t a b

data ALang t a b where
  Id :: (Avs a) => ALang t a a
  Fun :: (Avs a, Avs b) => (a -> b) -> ALang t a b
  Const :: (Avs b) => b -> ALang t () b
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

  Split :: (Avs a) => ALang t a (a,a)
  Flip :: (Avs a1, Avs a2) => ALang t (a1,a2) (a2,a1)
  Take :: (Avs a1, Avs a2) => ALang t (a1,a2) a1

  Alt :: (Avs a1, Avs a2) => ALang t a1 (Either a1 a2)
  Swap :: (Avs a1, Avs a2) => ALang t (Either a1 a2) (Either a2 a1)
  Join :: (Avs a) => ALang t (Either a a) a

  Dist
    :: (Avs a1, Avs a2, Avs a3)
    => ALang t (a1, Either a2 a3) (Either (a1, a2) (a1, a3))
  UnDist
    :: (Avs a1, Avs a2, Avs a3)
    => ALang t (Either (a1, a2) (a1, a3)) (a1, Either a2 a3)

  Forget :: (Avs a) => ALang t a ()

  Arr :: (Avs a, Avs b) => (VSpec a b) -> (a -> b) -> ALang t a b

  FxTerm :: (Fx t, Avs a, Avs b) => t a b -> ALang t a b
