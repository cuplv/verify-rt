module Transact.Int where

import ALang
import Store.Model.Int
import Transact

import Data.SBV

-- Int never goes negative
nonN :: Sy Int -> Sy Int -> Symbolic SBool
nonN s1 s2 = return $ (s1 .>= 0) .=> (s2 .>= 0)

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

-- Unsafe version subtracts 1 more than it asks about.  It therefore
-- fails both the application property "store stays >= 0" and the
-- coordination property "transaction updates do not exceed
-- capabilities."
badTakeStock :: (Avs a) => Transact a IntG Int Int
badTakeStock ctx amt =
  assertA (amt $>= ca 0) $
  assertA (ctx `atLeast` amt) $
  assertA (ctx `canSub` amt) $
  justE (subU (amt $+ ca 1) &&& amt)

witness :: (IntG,IntUpd)
witness = undefined
