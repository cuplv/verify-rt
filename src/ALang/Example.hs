{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module ALang.Example where

import ALang
import Atl
-- import Data.Map (Map)
import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.List as SList
import Store.Model
import Store.Model.Int
import Symbol
import qualified Symbol.MaybeMap as SMap
import Store.Model.MaybeMap (Map)
import qualified Store.Model.MaybeMap as MMap
import Transact
import Verify

mapWitness = MMap.witness

-- Properties to verify.

-- Main TPCC spec, combining specs on the two data model components:
-- the stock integer and the record table
tpccSpec = tup2Spec (nonN, noLoss)

tpccSpec2 s1 s2 = do
  k <- forall_
  constrain $ SMap.member k (_2 s1)
  return (SMap.match k (_2 s1) (_2 s2))

-- Spec for stock integer: it never goes negative
nonN :: Sy Int -> Sy Int -> Symbolic SBool
nonN s1 s2 = return $ (s1 .>= 0) .=> (s2 .>= 0)

-- Spec for record table: no inserted record is ever deleted or
-- modified.  For complete application, we will also want to allow
-- certain modifications.
noLoss :: Sy (Map a b) -> Sy (Map a b) -> Symbolic SBool
noLoss s1 s2 = do
  -- forall k's that are present in the pre-state
  k <- forall_
  constrain $ SMap.member k s1
  -- they must match their value in the post-state
  return (SMap.match k s1 s2)

-- Transactions

type TpccG k = (IntG,MapG')

-- Take the given amount from the stock field, and record the order in
-- the record table.  If either sub-transaction fails, the whole
-- transaction returns Nothing.
newOrder :: Fun (Context (TpccG Int), Int) (Maybe (GUpd (TpccG Int), ()))
newOrder = seqT -- sequence two transactions
  (snd intWitness, snd mapWitness) -- (ignore.. fixes ambiguous type issues)
  takeStock -- subtracts, outputs the subtracted amount
  addRecord -- records the subtracted amount

-- Take given amount from the stock field, return the amount subtracted.
takeStock :: Fun (Context IntG, Int) (Maybe (IntUpd, Int))
takeStock =
  -- Unpack our two inputs: the state+grant context, and the amount to
  -- subtract from the stock.
  tup2 $ \ctx amt ->
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
addRecord :: Fun (Context (MapG'), Int) (Maybe (MapU', ()))
addRecord =
  -- Unpack our two inputs: the state+grant context, and the order
  -- amount.
  tup2 $ \ctx amt ->
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
  let v = conE (justE (makeRecord amt) &&& unitE)
      upd = MMap.insertE key v
  -- The output is a pair: our update, and the transaction's return
  -- value.  This transaction only returns a () unit value.
  in returnE (upd &&& unitE)

  -- The record is simply a stringe message including the amount.
  where makeRecord amt = funE amt $ \n ->
          "Order for " ++ show n ++ " units."


-- Unsafe versions that do not verify.

-- Unsafe version subtracts 1 more than it asks about.  It therefore
-- fails both the application property "store stays >= 0" and the
-- coordination property "transaction updates do not exceed
-- capabilities."
takeStockUnsafe :: Fun (Context IntG, Int) (Maybe (IntUpd, Int))
takeStockUnsafe = tup2 $ \ctx amt ->
  assertA (amt $>= ca 0) $
  assertA (ctx `atLeast` amt) $
  assertA (ctx `canSub` amt) $
  justE (subU (amt $+ ca 1) &&& amt)

type MapG' = MMap.G1 String ()

type MapU' = MMap.Upd String ()

-- Uses key given by user, with no guarantee that it has not been used
-- in the map already.
addRecordBad :: Fun (Context (MapG'), (Int)) (Maybe (MapU', ()))
addRecordBad = tup2 $ \ctx cfg ->
  ((stateE ctx &&& cfg) &&& deconE (grantE ctx)) >>> maybeElim
    -- When key is granted
    (tup2 $ \s key ->
      tup2' s $ \records amt ->
        -- Check that it has not been used
        assertA (notE $ MMap.memberE key records) $
        -- Use a key unrelated to the granted key... unsafe!
        let v = conE (justE (makeRecord amt) &&& ca ())
        in justE (MMap.insertE (ca 1) v &&& ca ()))
    -- When no key is granted
    nothingE

  where makeRecord amt = funE amt $ \n ->
          "Order for " ++ show n ++ " units."


trueSpec :: Sy (Map k v) -> Sy (Map k v) -> Symbolic SBool
trueSpec _ _ = return sTrue

trueThm :: ThmResult -> Bool
trueThm = not . modelExists

tup2dist ((a,b),(c,d)) = ((a,c),(b,d))

-- Somehow this seemed more convenient than setting up a real test
-- suite...
test :: IO ()
test = do
  ss <- SMap.loadAxioms'
  (r1,r2) <- check intWitness (pure ()) takeStock nonN
  (r3,r4) <- check intWitness (pure ()) takeStockUnsafe nonN
  (r5,r6) <- check mapWitness (SMap.addAxioms' ss) addRecord noLoss
  (r7,r8) <- check 
               (tup2dist (intWitness,mapWitness)) 
               (SMap.addAxioms' ss)
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
  ss <- SMap.loadAxioms'
  r <- proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    SMap.addAxioms' ss
    a <- forall "pre"
    b <- symbolize (plusA 1 >>> plusA 1) a
    return $ b .== a + 2
  print r
