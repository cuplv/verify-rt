module ALang.Prelude 
  ( module ALang
  , module Service
  , module Symbol
  , module ValDomain

  , plus
  , effectAdd
  , effectSub
  , queryAtLeast
  , iteA
  ) where

import ALang
import Service
import Symbol
import ValDomain

plus :: (Avs d) => Int -> ALang d Int Int 
plus n = Split >>> ATimes (Const n) Id >>> VdTerm Sum

effectAdd :: ALang Int Int Int
effectAdd = SvTerm SvAdd

effectSub :: ALang Int Int Int
effectSub = VdTerm Negate >>> SvTerm SvAdd >>> VdTerm Negate

queryAtLeast :: ALang Int Int (Either () Int)
queryAtLeast = SvTerm SvGE

iteA
  :: (Avs d, Avs a, Avs b1, Avs b2)
  => ALang d a (Either b1 b2)
  -> ALang d a (Either a a)
iteA a = Split >>> secondA a >>> DistL >>> ASum TakeL TakeL
