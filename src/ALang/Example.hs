module ALang.Example where

import ALang.Prelude
import Data.SBV

{-| Subtract the input amount from the state, if the amount is
  available. -}
takeStock :: ALang Int Int (Either String Int)
takeStock =
  -- Check that the state's value is greater than or equal to the
  -- transaction's input value.  This term passes the input value thru
  -- as a Left/Right result.
  iteA queryAtLeast
      -- If so, subtract the input value.
  >?> effectSub
      -- If not, return an explanation of failure.
  >!> Const "Not enough stock."

badTakeStock :: ALang Int Int (Either String Int)
badTakeStock =
  iteA queryAtLeast
      -- Subtract 1 more than the input value.
  >?> plus 1 >>> effectSub
  >!> Const "Not enough stock."

test = do
  r1 <- takeStock `checkSpec` nonNegative
  r2 <- badTakeStock `checkSpec` nonNegative
  return $ r1 && not r2

{-| The state remains non-negative, as an invariant. -}
nonNegative :: (Avs a, Avs b) => TSpec Int a b
nonNegative = invarS $ \d1 d2 -> (d1 .>= 0) .=> (d2 .>= 0)

{-| Add the given 'Int' to the input value. -}
plus :: (Avs d) => Int -> ALang d Int Int 
plus n = Split >>> ATimes (Const n) Id >>> VdTerm Sum

{-| Apply a Left/Right term to the input value, and then put the input
  value into the Left or Right result. -}
iteA
  :: (Avs d, Avs a, Avs b1, Avs b2)
  => ALang d a (Either b1 b2)
  -> ALang d a (Either a a)
iteA a = Split >>> secondA a >>> DistL >>> ASum TakeL TakeL

-- The following convenience terms wrap primitive IntSV terms defined
-- in ./src/Service.hs

effectAdd :: ALang Int Int Int
effectAdd = SvTerm SvAdd

effectSub :: ALang Int Int Int
effectSub = VdTerm Negate >>> SvTerm SvAdd >>> VdTerm Negate

queryAtLeast :: ALang Int Int (Either () Int)
queryAtLeast = SvTerm SvGE
