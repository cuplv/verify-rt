module Transact.MaybeMap where

import ALang
import Store.Model
import qualified Store.Model.MaybeMap as MMap
import qualified Symbol.MaybeMap as SMMap
import Transact

import Data.SBV
import qualified Data.SBV.Maybe as SMaybe

type CustomerId = Int
type MMap = MMap.Map
type MapG = MMap.G1
type MapG' = MMap.G1 String String
type MapU' = MMap.Upd String String

-- Given an amount-subtracted Int, insert a record of that order in
-- the order table.
addRecord'
  :: (Avs a) 
  => Transact a (MapG String (CustomerId,Int)) (CustomerId,Int) ()
addRecord' ctx cfg =
  tup2' cfg $ \customer amt ->
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
  let v = conE (nothingE &&& (customer &&& amt))
      upd = MMap.insert key v
  -- The output is a pair: our update, and the transaction's return
  -- value.  This transaction only returns a () unit value.
  in returnE (upd &&& unitE)

-- Uses hard-coded key, rather than one from the context
addRecordBad'
  :: (Avs a) 
  => Transact a (MapG String (CustomerId,Int)) (CustomerId,Int) ()
addRecordBad' ctx cfg =
  tup2' cfg $ \customer amt ->
  -- Extract the key from the grant.  When the grant holds a key, it
  -- means we have the exclusive permission to insert/modify/delete on
  -- that key.  If the grant is empty, we stop here and cancel the
  -- transaction.
  requireE (deconE $ grantE ctx) $ \key ->
  -- Check the that this key has not already been used in the state.
  -- If it has, we stop here and cancel the transaction.
  assertA (notE $ MMap.memberE key (stateE ctx)) $
  -- Our update inserts a string, based on the order amount, into
  -- the table using a hardcoded (unsafe) key.
  let unsafeKey = ca 1
      v = conE (nothingE &&& (customer &&& amt))
      upd = MMap.insert unsafeKey v
  -- The output is a pair: our update, and the transaction's return
  -- value.  This transaction only returns a () unit value.
  in returnE (upd &&& unitE)

-- Given an amount-subtracted Int, insert a record of that order in
-- the order table.
addRecord 
  :: (Avs a) 
  => Transact a MapG' Int ()
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
  let v = conE (nothingE &&& (funE amt show))
      upd = MMap.insert key v
  -- The output is a pair: our update, and the transaction's return
  -- value.  This transaction only returns a () unit value.
  in returnE (upd &&& unitE)

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

-- Update the delivery info for an order record.
-- Return value is (CustomerId, charge amt)
deliverRecord 
  :: (Avs a) 
  => Transact a (MapG String (Int,Int)) (Int,String) (Int,Int)
deliverRecord ctx cfg =
  tup2' cfg $ \orderId deliv ->
  -- Require an exclusive key.
  requireE (deconE $ grantE ctx) $ \key ->
  assertA (key $== orderId) $
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
  in returnE (upd &&& order)

-- Spec for record table: no inserted record is ever deleted or
-- modified.  For complete application, we will also want to allow
-- certain modifications.
foreverEntries :: Sy (MMap a b) -> Sy (MMap a b) -> Symbolic SBool
foreverEntries s1 s2 = do
  -- forall k's that are present in the pre-state
  k <- forall_
  constrain $ SMMap.member k s1
  -- they must match their value in the post-state
  return (SMMap.match k s1 s2)

-- More permissive record table spec: No inserted record is ever
-- deleted, and once an inserted record has its Maybe field filled in,
-- it is no longer modified at all.
orderedEntries :: Sy (MMap a b) -> Sy (MMap a b) -> Symbolic SBool
orderedEntries s1 s2 = do
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

witness = MMap.witness

axioms = SMMap.axioms

type Upd = MMap.Upd
