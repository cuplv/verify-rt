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
