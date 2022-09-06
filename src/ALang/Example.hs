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
  k1 <- exists "k1"
  -- k1 appears in m1, and appears again in the suffix that comes
  -- after that first appearance.
  let p1 = SList.elem k1 m1
           .&& SList.elem k1 (SList.drop (SList.indexOf (SList.singleton k1) m1 + 1) m1)
  -- k2, if it appears in m2, does not appear in the suffix that comes
  -- after that first appearance.
  k2 <- forall "k2"
  let p2 = SList.elem k2 m2
           .=> SList.notElem k2 (SList.drop (SList.indexOf m2 (SList.singleton k2) + 1) m2)

  -- p1 is true when an overwrite has already occurred in the
  -- pre-state.  p2 is true when the post-state contains no
  -- overwrites.  We are only obligated to show p2 when the pre-state
  -- satisfies the invariant---that is, when p1 is false.
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

test2 = do
  r1 <- reportSale "Alice" `checkSpec` noOverwrite
  r2 <- badReportSale "Alice" `checkSpec` noOverwrite
  return (r1 && not r2)
