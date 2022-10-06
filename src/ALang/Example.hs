{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module ALang.Example where

import ALang
import Atl
import Data.Map (Map)
import Data.SBV
import qualified Data.SBV.List as SList
import Store.Model
import Store.Model.Int
import Symbol
import Transact
import Verify

-- {-| Subtract the config amount from the state, if the amount is
--   available. -}
-- takeStock :: Atl IntReq Int () Int
-- takeStock =
--   -- Require that the state's value is greater than or equal to the
--   -- transaction's config value.
--   request atLeastR
--   -- Subtract the config value.
--   >>> updateS subU 
--   -- Then, return the config value.
--   >>> getConf

takeStockTest :: Fun (Context IntG, Int) (Maybe (IntUpd, Int))
takeStockTest = assertA ((tup2g2 &&& constA 0) >>> geA) $
  flipA
  >>> (reqs &&& tup2g1)
  >>> iteA ((subU &&& idA) >>> asJust)
           (constA Nothing)
  where reqs = (atLeast &&& canSub) >>> andA

takeStockUnsafe :: Fun (Context IntG, Int) (Maybe (IntUpd, Int))
takeStockUnsafe = assertA ((tup2g2 &&& constA 0) >>> geA) $
  flipA
  >>> (reqs &&& tup2g1)
  >>> iteA (((plusA 1 >>> subU) &&& idA) >>> asJust)
           (constA Nothing)
  where reqs = (atLeast &&& canSub) >>> andA

nonN :: Sy Int -> Sy Int -> Symbolic SBool
nonN s1 s2 = return $ (s1 .>= 0) .=> (s2 .>= 0)

test :: IO ()
test = do
  putStrLn "[Safe]"
  (r1,r2) <- check intWitness takeStockTest nonN
  putStrLn "spec:"
  print r1
  putStrLn "write:"
  print r2

  putStrLn "[Unsafe]"
  (r1,r2) <- check intWitness takeStockUnsafe nonN
  putStrLn "spec:"
  print r1
  putStrLn "write:"
  print r2
