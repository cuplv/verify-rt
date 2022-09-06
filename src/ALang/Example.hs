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

-- newEntries
--   :: (Ord (Rep k), Avs k, Avs w, Avs a, Avs b)
--   => Integer 
--   -> TSpec (Map k w) a b
-- newEntries i = prePostS $ \pre post -> do
--   n <- forall_
--   return $ hasSize pre n .=> hasSize post (n + literal i)

noOverwrite
  :: (Ord (Rep k), Avs k, Avs w, Avs a, Avs b)
  => TSpec (Map k w) a b
noOverwrite = invarS $ \m -> forAll ["i1","i2"] $ \i1 i2 ->
  -- i1 <- forall "ix1"
  -- i2 <- forall "ix2"
  (i1 .>= 0 .&& i1 .< SList.length m
   .&& i2 .>= 0 .&& i2 .< SList.length m
   .&& i1 ./= i2)
  .=> (SList.elemAt m i1 ./= SList.elemAt m i2)

test3 = prove $
  let m = literal [1::Integer,1]
      a = forAll_ $ do
            i1 <- free "ix1"
            i2 <- free "ix2"
            return $ (i1 .>= 0 .&& i1 .< SList.length m
                      .&& i2 .>= 0 .&& i2 .< SList.length m
                      .&& i1 ./= i2)
                     .=> (SList.elemAt m i1 ./= SList.elemAt m i2)
  in do r1 <- a 
        -- r2 <- forAll ["x"] $ \x -> (x :: SInteger) .> 2
        return (sNot r1)

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
