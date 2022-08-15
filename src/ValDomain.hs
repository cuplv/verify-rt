{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ValDomain where

import Symbol

import Data.SBV
import Data.SBV.Either
import Data.SBV.Tuple

class ValDomain l where
  vdSymbol :: l a b -> VSpec a b

data IntVd a b where
  Sum :: IntVd (Int,Int) Int
  Negate :: IntVd Int Int
  VdLE :: IntVd (Int,Int) (Either () ())
  VdGE :: IntVd (Int,Int) (Either () ())

instance ValDomain IntVd where
  vdSymbol l = case l of
    Sum -> VSpec $ \a -> return (_1 a + _2 a)
    Negate -> VSpec $ \a -> return (negate a)
    VdLE -> VSpec $ \a -> return (ite (_1 a .<= _2 a)
                                      (sRight su)
                                      (sLeft su))
    VdGE -> VSpec $ \a -> return (ite (_1 a .>= _2 a)
                                      (sRight su)
                                      (sLeft su))
