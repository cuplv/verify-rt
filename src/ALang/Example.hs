{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module ALang.Example where

import ALang
import Atl
-- import Data.Map (Map)
import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.List as SList
import qualified Data.SBV.Maybe as SMaybe
import Store.Model
import Store.Model.Int
import Symbol
import qualified Store.Model.IntMap as IMap
import qualified Symbol.IntMap as SIMap
import qualified Store.Model.MaybeMap as MMap
import qualified Symbol.MaybeMap as SMMap
import Transact
import Verify

type IMap = IMap.Map
type MMap = MMap.Map

mapWitness = MMap.witness

-- Properties to verify.

-- Main TPCC spec, combining specs on the two data model components:
-- the stock integer and the record table
tpccSpec = tup2Spec (nonN, noLoss2)

-- Spec for stock integer: it never goes negative
nonN :: Sy Int -> Sy Int -> Symbolic SBool
nonN s1 s2 = return $ (s1 .>= 0) .=> (s2 .>= 0)

nonN2 :: Sy (IMap a) -> Sy (IMap a) -> Symbolic SBool
nonN2 s1 s2 = do
  (k,v1) <- SIMap.anyEntry s1
  mv2 <- SIMap.lookup k s2
  return $ SMaybe.maybe
    sTrue
    (\v2 -> (v1 .>= 0) .=> (v2 .>= 0))
    mv2

-- Spec for record table: no inserted record is ever deleted or
-- modified.  For complete application, we will also want to allow
-- certain modifications.
noLoss :: Sy (MMap a b) -> Sy (MMap a b) -> Symbolic SBool
noLoss s1 s2 = do
  -- forall k's that are present in the pre-state
  k <- forall_
  constrain $ SMMap.member k s1
  -- they must match their value in the post-state
  return (SMMap.match k s1 s2)

-- More detailed record table spec: No inserted record is ever
-- deleted, and once an inserted record has its Maybe field filled in,
-- it is no longer modified at all.
noLoss2 :: Sy (MMap a b) -> Sy (MMap a b) -> Symbolic SBool
noLoss2 s1 s2 = do
  -- For any (k,v1) entry in the pre-state
  (k,v1) <- SMMap.anyEntry s1
  -- Lookup the corresponding v2 in the post-state
  mv2 <- SMMap.lookup k s2
  -- Ask whether the corresponding v2 exists
  return $ SMaybe.maybe
    -- If not, we've lost information.  Failure.
    sFalse
    -- If v2 exists, consider the value of v1.
    (\_ -> SMaybe.maybe
       -- If it's a Nothing value, then any value of v2 counts as
       -- succeeding it.  Success.
       sTrue
       -- If it's a Just value, we must preserve that value.  And so
       -- we require that v1 and v2 match for success.
       (const $ SMMap.match k s1 s2)
       -- (const $ v1 .== v2)
       v1)
    mv2

-- Transactions

-- Grant type for top-level Tpcc transactions
type TpccG = (IntG,MapG')

-- Take the given amount from the stock field, and record the order in
-- the record table.  If either sub-transaction fails, the whole
-- transaction returns Nothing.
newOrder :: (Avs a) => Transact a TpccG Int ()
newOrder = seqT
  (snd intWitness, snd mapWitness)
  (tup2l1 takeStock)
  (tup2l2 addRecord)
-- newOrder = seqT -- sequence two transactions
--   (snd intWitness, snd mapWitness) -- (ignore.. fixes ambiguous type issues)
--   (tup2l1 takeStock') -- subtracts, outputs the subtracted amount
--   (tup2l2 addRecord) -- records the subtracted amount

takeStock' :: (Avs a) => Transact a StockG (IMap.Key, Int) Int
takeStock' ctx cfg =
  tup2' cfg $ \key amt ->
  requireE (deconE $ grantE ctx) $ \k1 ->
  assertA (key $== k1) $
  IMap.intMapLift key takeStock ctx amt

-- Take given amount from the stock field, return the amount subtracted.
takeStock :: (Avs a) => Transact a IntG Int Int
takeStock ctx amt =
  -- Check that input 'amt' is a natural number
  assertA (amt $>= ca 0) $
  -- Check that store has at least 'amt'
  assertA (ctx `atLeast` amt) $
  -- Check that we have permission to subtract 'amt'
  assertA (ctx `canSub` amt) $
  -- Subtract 'amt', and also pass 'amt' on as the return value
  returnE (subU amt &&& amt)

-- Given an amount-subtracted Int, insert a record of that order in
-- the order table.
addRecord :: (Avs a) => Transact a MapG' Int ()
addRecord ctx amt =
  -- Extract the key from the grant.  When the grant holds a key, it
  -- means we have the exclusive permission to insert/modify/delete on
  -- that key.  If the grant is empty, we stop here and cancel the
  -- transaction.
  requireE (deconE $ grantE ctx) $ \key ->
  -- Check the that this key has not already been used in the state.
  -- If it has, we stop here and cancel the transaction.
  assertA (notE $ MMap.memberE key (stateE ctx)) $
  -- Our update inserts a string, based on the order amount, into
  -- the table using the provided key.
  let v = conE (nothingE &&& makeRecord amt)
      upd = MMap.insert key v
  -- The output is a pair: our update, and the transaction's return
  -- value.  This transaction only returns a () unit value.
  in returnE (upd &&& unitE)

  -- The record is simply a string message including the amount.
  where makeRecord amt = funE amt $ \n ->
          "Order for " ++ show n ++ " units."

-- Update the delivery info for an order record.
deliverRecord :: (Avs a) => Transact a MapG' String ()
deliverRecord ctx deliv =
  -- Require an exclusive key.
  requireE (deconE $ grantE ctx) $ \key ->
  -- Get that key's existing value (must be present).
  requireE (MMap.lookupE key (stateE ctx)) $ \val ->
  -- Unpack value into delivery info and order info.
  tup2' (deconE val) $ \deliv1 order ->
  -- Existing delivery info must be empty, to avoid overwriting it.
  assertA (isNothingE deliv1) $
  -- The new value we insert includes our input value (deliv) and the
  -- previously existing order information.
  let v = conE (justE deliv &&& order)
      upd = MMap.insert key v
  in returnE (upd &&& unitE)

-- Unsafe versions that do not verify.

-- Unsafe version subtracts 1 more than it asks about.  It therefore
-- fails both the application property "store stays >= 0" and the
-- coordination property "transaction updates do not exceed
-- capabilities."
takeStockUnsafe :: (Avs a) => Transact a IntG Int Int
takeStockUnsafe ctx amt =
  assertA (amt $>= ca 0) $
  assertA (ctx `atLeast` amt) $
  assertA (ctx `canSub` amt) $
  justE (subU (amt $+ ca 1) &&& amt)

type StockG = IMap.G1 ()

type StockU = IMap.Upd ()

-- The first string is the delivery info (starting as Nothing), and
-- the second string is the rest of the order information.
type MapG' = MMap.G1 String String

type MapU' = MMap.Upd String String

-- Uses key given by user, with no guarantee that it has not been used
-- in the map already.
addRecordBad :: (Avs a) => Transact a MapG' Int ()
addRecordBad ctx cfg =
  ((stateE ctx &&& cfg) &&& deconE (grantE ctx)) >>> maybeElim
    -- When key is granted
    (tup2 $ \s key ->
      tup2' s $ \records amt ->
        -- Check that it has not been used
        assertA (notE $ MMap.memberE key records) $
        -- Use a key unrelated to the granted key... unsafe!
        let v = conE (nothingE &&& makeRecord amt)
        in justE (MMap.insert (ca 1) v &&& ca ()))
    -- When no key is granted
    nothingE

  where makeRecord amt = funE amt $ \n ->
          "Order for " ++ show n ++ " units."

trueThm :: ThmResult -> Bool
trueThm t =
  not (modelExists t)
  && case t of
       (ThmResult (Unknown _ UnknownTimeOut)) -> False
       _ -> True

tup2dist ((a,b),(c,d)) = ((a,c),(b,d))

-- Somehow this seemed more convenient than setting up a real test
-- suite...
test :: IO ()
test = do
  (r1,r2) <- check intWitness takeStock nonN
  (r3,r4) <- check intWitness takeStockUnsafe nonN
  (r5,r6) <- checkWith mapWitness SMMap.axioms addRecord noLoss2
  (r7,r8) <- checkWith
               (tup2dist (intWitness,mapWitness)) 
               SMMap.axioms
               newOrder 
               tpccSpec
  if not $ trueThm r1
     then putStrLn "Error: good failed spec" >> print r1
     else return ()
  if not $ trueThm r2
     then putStrLn "Error: good failed write" >> print r2
     else return ()
  if trueThm r3
     then putStrLn "Error: bad passed spec" >> print r3
     else return ()
  if trueThm r4
     then putStrLn "Error: bad passed write" >> print r4
     else return ()
  if not $ trueThm r5
     then putStrLn "Error: good map failed spec" >> print r5
     else return ()
  if not $ trueThm r6
     then putStrLn "Error: good map failed write" >> print r6
     else return ()
  if not $ trueThm r7
     then putStrLn "Error: newOrder failed spec" >> print r7
     else return ()
  if not $ trueThm r8
     then putStrLn "Error: newOrder failed write" >> print r8
     else return ()

  if trueThm r1 && trueThm r2 && not (trueThm r3) && not (trueThm r4) && trueThm r5 && trueThm r6 && trueThm r7 && trueThm r8
     then putStrLn "[OK]"
     else putStrLn "[ERROR]"

test2 :: IO ()
test2 = do
  ss <- loadAxioms SMMap.axioms
  r <- proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    applyAxioms SMMap.axioms ss
    a <- forall "pre"
    b <- symbolize (plusA 1 >>> plusA 1) a
    return $ b .== a + 2
  print r
