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

-- nonNegative :: (Avs a, Avs b) => AtlSpec IntReq Int a b
-- nonNegative = prePost
--   (\s -> s .>= 0)
--   (\s -> s .>= 0)

-- takeStockTest :: Fun (Context IntCap, Int) (Maybe (IntUpd, Int))
-- takeStockTest =
--   flipA
--   >>> (tup2g1 &&& reqs)
--   >>> distA
--   >>> (constA Nothing ||| (tup2g1 >>> (subU &&& idA) >>> asJust))
--   where reqs = (atLeast &&& canSub) >>> bothA

-- takeStockUnsafe :: Fun (Context IntCap, Int) (Maybe (IntUpd, Int))
-- takeStockUnsafe =
--   flipA
--   >>> (tup2g1 &&& reqs)
--   >>> distA
--   >>> (constA Nothing ||| (tup2g1 >>> ((plusA 1 >>> subU) &&& idA) >>> asJust))
--   where reqs = (atLeast &&& canSub) >>> bothA

-- ge0 :: Sy Int -> Symbolic SBool
-- ge0 w = return $ w .>= 0

-- nonN :: Sy Int -> Sy Int -> Symbolic SBool
-- nonN s1 s2 = return $ (s1 .>= 0) .=> (s2 .>= 0)

-- test :: IO ()
-- test = do
--   putStrLn "Safe:"
--   print =<< prove (stateSpec intWitness takeStockTest ge0 nonN)
--   print =<< prove (capSpec intWitness takeStockTest ge0)
--   putStrLn ""
--   putStrLn "Unsafe:"
--   print =<< prove (stateSpec intWitness takeStockUnsafe ge0 nonN)
--   print =<< prove (capSpec intWitness takeStockUnsafe ge0)
