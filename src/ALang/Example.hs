module ALang.Example where

import ALang.Prelude
import Data.SBV

{-| The state remains non-negative, as an invariant. -}
nonNegative :: (Avs a, Avs b) => TSpec Int a b
nonNegative = invarS $ \d1 d2 -> (d1 .>= 0) .=> (d2 .>= 0)

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
