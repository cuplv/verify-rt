module Transact.Tpcc.Simple where

import ALang
import Store.Model.Int (IntG)
import Transact
import qualified Transact.Int as Int
import qualified Transact.MaybeMap as MMap
import Verify (tup2Spec)

tpccSpec = tup2Spec (Int.nonNegative, MMap.orderedEntries)

tooStrict = tup2Spec (Int.nonNegative, MMap.foreverEntries)

superStrict = tup2Spec (Int.freezeTo 5, MMap.orderedEntries)

type G = (IntG, MMap.MapG')

witness = ((undefined,undefined), (undefined,undefined))

-- Take the given amount from the stock field, and record the order in
-- the record table.  If either sub-transaction fails, the whole
-- transaction returns Nothing.
newOrder :: (Avs a) => Transact a G Int ()
newOrder = seqT
  (snd Int.witness, snd MMap.witness)
  (tup2l1 Int.takeStock)
  (tup2l2 MMap.addRecord)

axioms = MMap.axioms
