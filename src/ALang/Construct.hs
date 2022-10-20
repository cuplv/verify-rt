module ALang.Construct (ALang (..), arrC, arrC') where

import ALang.Internal
import Symbol

import Data.SBV

arrC :: (Avs a, Avs b) => Sy b -> b -> ALang t a b
arrC s a = arrC' (pure s) a

arrC' :: (Avs a, Avs b) => Symbolic (Sy b) -> b -> ALang t a b
arrC' s a = ArrF (const s) (const a)
