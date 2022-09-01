{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ValDomain where

import Symbol

import Data.SBV
import Data.SBV.Either
import Data.SBV.Tuple

{-| A 'ValDomain' provides terms for manipulating input and output
  values, which the verifier knows how to track. -}
class ValDomain l where
  {-| Symbolic representation for a term's behavior. -}
  vdSymbol :: l a b -> VSpec a b

{-| Terms for manipulating 'Int' values. -}
data IntVd a b where

  {-| Take a pair of 'Int' values and add the together. -}
  Sum :: IntVd (Int,Int) Int

  {-| Negate the input value. -}
  Negate :: IntVd Int Int

  {-| Given input @(n1,n2)@, return @Right ()@ iff @n1 <= n2@. -}
  VdLE :: IntVd (Int,Int) (Either () ())

  {-| Given input @(n1,n2)@, return @Right ()@ iff @n1 >= n2@. -}
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
