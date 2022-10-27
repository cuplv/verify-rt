module Transact.Tpcc where

import ALang
import Store.Model.Int (IntG)
import Transact
import qualified Transact.Int as Int
import qualified Transact.IntMap as IMap
import qualified Transact.MaybeMap as MMap
import Verify (tup3Spec)

type CustomerId = Int
type StockId = Int
type OrderId = Int
type G = 
  (IMap.G2 () -- Stock table
  ,MMap.MapG String (CustomerId,Int) -- Order table
  ,IMap.G1 () -- Customer table
  )

tpccSpec = tup3Spec 
  (IMap.nonNegative
  ,MMap.orderedEntries
  ,IMap.nonNegative)

-- Take the given amount from the stock field, and record the order in
-- the record table.  If either sub-transaction fails, the whole
-- transaction returns Nothing.
newOrder :: (Avs a) => Transact a G (CustomerId, IMap.Map') ()
newOrder =
  seqT
    seqWitness
    (tup3l1 IMap.takeStockMulti)
    (tup3l2 MMap.addRecord')

-- Add delivery info for the given order, and add the corresponding
-- cost to the order customer's balance. Return the customer's new
-- balance.
deliver :: (Avs a) => Transact a G (OrderId,String) Int
deliver =
  seqT
    seqWitness
    (tup3l2 MMap.deliverRecord)
    (tup3l3 IMap.addBalance)

-- Subtract the given amount from the given customer's balance,
-- requiring that the balance does not go below 0. Return the
-- customer's new balance.
payment :: (Avs a) => Transact a G (CustomerId,Int) Int
payment = tup3l3 IMap.subBalance

witness = ((undefined,undefined), (undefined,undefined), (undefined,undefined))

seqWitness = (snd IMap.witness2, snd MMap.witness, snd IMap.witness)
