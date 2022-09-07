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

{-| Replace a term's output with it's input, so that the input can be
  used again.  The term's actual output is ignored. -}
passThru :: (Avs a, Avs b) => ALang v a b -> ALang v a a
passThru a = Split >>> secondA a >>> TakeL

-- The following convenience terms wrap primitive IntSV terms defined
-- in ./src/Service.hs

effectAdd :: ALang IntSv Int Int
effectAdd = passThru $ SvTerm SvAdd

effectSub :: ALang IntSv Int Int
effectSub = passThru $ VdTerm Negate >>> SvTerm SvAdd

queryAtLeast :: ALang IntSv Int (Either () Int)
queryAtLeast = SvTerm SvGE


-- Map insertion example

{-| A limited safety condition ensuring uniqueness of keys added to a
  map.

  The map is modeled as a list of keys, representing the history of
  key-insertions on the map.  It every key in the history is unique,
  it means that no entries have been overwritten.

  Rather than assume the pre-condition that no overwrites have
  occurred in the past, it assumes the stronger pre-condition that at
  most one key has been inserted in the past.  The solver seemed
  unable to terminate when the weaker pre-condition was used.
-}
noOverwrite1
  :: (Ord (Rep k), Avs k, Avs w, Avs a, Avs b)
  => TSpec (Map k w) a b
noOverwrite1 = prePostS $ \m1 m2 -> do
  constrain $ SList.length m1 .<= 1
  k <- forall "k"
  return $ sNot (seenTwice k m2)

tailAfter k m = SList.drop (SList.indexOf m (SList.singleton k) + 1) m

seenTwice k m = SList.elem k m .&& SList.elem k (tailAfter k m)

test2 = do
  r1 <- reportSale "Alice" `checkSpec` noOverwrite1
  r2 <- reportSale2 "Alice" `checkSpec` noOverwrite1
  r3 <- badReportSale "Alice" `checkSpec` noOverwrite1
  return (r1 && r2 && not r3)

{-| Insert a report of a sale into a map, using a unique key to avoid
  overwriting existing reports. -}
reportSale
  :: Customer
  -> ALang (MapSv ReportId String) Int ReportId
reportSale cust =
  (freshKey &&& Fun mkReport)
  >>> passThru insertKV
  >>> TakeL
  where mkReport n = show n
                     ++ " products were purchased by"
                     ++ cust

{-| Insert two reports for the same customer and quantity.  The two
  reports get distinct unique keys. -}
reportSale2
  :: Customer
  -> ALang (MapSv ReportId String) Int (ReportId,ReportId)
reportSale2 cust =
  reportSale cust &&& reportSale cust

{-| Insert a report using the hard-coded key @1@.  There is no guarantee
  that this key will be unique. -}
badReportSale
  :: Customer
  -> ALang (MapSv ReportId String) Int ReportId
badReportSale cust =
  (Const 1 &&& Fun mkReport)
  >>> passThru insertKV
  >>> TakeL
  where mkReport n = show n
                     ++ " products were purchased by"
                     ++ cust


-- Helper definitions for reportSale

type Customer = String

type ReportId = Int

freshKey :: (Ord (Rep k), Avs k, Avs w, Avs a) => ALang (MapSv k w) a k
freshKey = Const () >>> SvTerm SvFreshKey

insertKV :: (Ord (Rep k), Avs k, Avs w) => ALang (MapSv k w) (k,w) ()
insertKV = SvTerm SvInsert
