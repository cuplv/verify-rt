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
