{-# LANGUAGE FlexibleContexts #-}

module ALang.Example where

import ALang.Prelude
import Data.Map (Map)
import Data.SBV
import qualified Data.SBV.List as SList

{-| Subtract the input amount from the state, if the amount is
  available. -}
takeStock :: ALang IntSv Int (Either String Int)
takeStock =
  -- Check that the state's value is greater than or equal to the
  -- transaction's input value.  This term passes the input value thru
  -- as a Left/Right result.
  iteA queryAtLeast
      -- If so, subtract the input value.
  >?> effectSub
      -- If not, return an explanation of failure.
  >!> Const "Not enough stock."

badTakeStock :: ALang IntSv Int (Either String Int)
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
nonNegative = invarS $ \d -> return (d .>= 0)

{-| Add the given 'Int' to the input value. -}
plus :: Int -> ALang d Int Int 
plus n = Split >>> ATimes (Const n) Id >>> VdTerm Sum

{-| Apply a Left/Right term to the input value, and then put the input
  value into the Left or Right result. -}
iteA
  :: (Avs a, Avs b1, Avs b2)
  => ALang v a (Either b1 b2)
  -> ALang v a (Either a a)
iteA a = Split >>> secondA a >>> DistL >>> ASum TakeL TakeL

-- The following convenience terms wrap primitive IntSV terms defined
-- in ./src/Service.hs

effectAdd :: ALang IntSv Int Int
effectAdd = SvTerm SvAdd

effectSub :: ALang IntSv Int Int
effectSub = VdTerm Negate >>> SvTerm SvAdd >>> VdTerm Negate

queryAtLeast :: ALang IntSv Int (Either () Int)
queryAtLeast = SvTerm SvGE

-- Map insertion example

noOverwrite
  :: (Ord (Rep k), Avs k, Avs w, Avs a, Avs b)
  => TSpec (Map k w) a b
noOverwrite = prePostS $ \m1 m2 -> do
  i1 <- exists "i1"
  i2 <- exists "i2"
  i3 <- forall "i3"
  i4 <- forall "i4"

  let p1 = 0 .<= i1 .&& i1 .< SList.length m1
           .&& 0 .<= i2 .&& i2 .< SList.length m1
           .&& i1 ./= i2
           .&& SList.elemAt m1 i1 .== SList.elemAt m1 i2

      p2 = (0 .<= i3 .&& i3 .< SList.length m2
           .&& 0 .<= i4 .&& i4 .< SList.length m2
           .&& i3 ./= i4)
           .=> SList.elemAt m2 i3 ./= SList.elemAt m2 i4

  return $ p1 .|| p2

type Customer = String

type ReportId = Int

reportSale
  :: Customer
  -> ALang (MapSv ReportId String) Int ReportId
reportSale cust =
  Split
  >>> ATimes (Const () >>> SvTerm SvFreshKey)
             (Fun $ mkReport cust)
  >>> Split
  >>> ATimes TakeL
             (SvTerm SvInsert)
  >>> TakeL
  where mkReport c n = show n
                       ++ " products were purchased by"
                       ++ c

badReportSale
  :: Customer
  -> ALang (MapSv ReportId String) Int ReportId
badReportSale cust =
  Split
  >>> ATimes (Const 1)
             (Fun $ mkReport cust)
  >>> Split
  >>> ATimes TakeL
             (SvTerm SvInsert)
  >>> TakeL
  where mkReport c n = show n
                       ++ " products were purchased by"
                       ++ c

-- Just hangs while trying to prove the correct transaction safe...
test2 = do
  r1 <- reportSale "Alice" `checkSpec` noOverwrite
  r2 <- badReportSale "Alice" `checkSpec` noOverwrite
  return (r1 && not r2)
