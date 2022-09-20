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
  vdFun :: l a b -> a -> b

{-| Terms for manipulating standard values. -}
data BaseVd a b where

  {-| Take a pair of 'Int' values and add them together. -}
  Sum :: BaseVd (Int,Int) Int

  {-| Negate the input value. -}
  Negate :: BaseVd Int Int

  {-| Given input @(n1,n2)@, return @Right ()@ iff @n1 <= n2@. -}
  VdLE :: BaseVd (Int,Int) (Either () ())

  {-| Given input @(n1,n2)@, return @Right ()@ iff @n1 >= n2@. -}
  VdGE :: BaseVd (Int,Int) (Either () ())

  Tup2T3 :: BaseVd (a1,(a2,a3)) (a1,a2,a3)

  Tup3T2 :: BaseVd (a1,a2,a3) (a1,(a2,a3))

  Tup3T4 :: BaseVd (a1,a2,(a3,a4)) (a1,a2,a3,a4)

  Tup4T3 :: BaseVd (a1,a2,a3,a4) (a1,a2,(a3,a4))

instance ValDomain BaseVd where
  vdSymbol l = case l of
    Sum -> VSpec $ \a -> return (_1 a + _2 a)
    Negate -> VSpec $ \a -> return (negate a)
    VdLE -> VSpec $ \a -> return (ite (_1 a .<= _2 a)
                                      (sRight su)
                                      (sLeft su))
    VdGE -> VSpec $ \a -> return (ite (_1 a .>= _2 a)
                                      (sRight su)
                                      (sLeft su))
  vdFun l = case l of
    Sum -> \(a1,a2) -> a1 + a2
    Negate -> \a -> (-a)
    VdLE -> \(a1,a2) -> if a1 <= a2
                           then Right ()
                           else Left ()
    VdGE -> \(a1,a2) -> if a1 >= a2
                           then Right ()
                           else Left ()
    Tup2T3 -> \(a1,(a2,a3)) -> (a1,a2,a3)
    Tup3T2 -> \(a1,a2,a3) -> (a1,(a2,a3))
