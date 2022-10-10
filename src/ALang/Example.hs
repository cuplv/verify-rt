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
takeStockTest = tup2 $ \ctx amt ->
  assertA (amt $>= ca 0) $
  assertA (ctx `atLeast` amt) $
  assertA (ctx `canSub` amt) $
  justE (subU amt &&& amt)

takeStockUnsafe :: Fun (Context IntG, Int) (Maybe (IntUpd, Int))
takeStockUnsafe = tup2 $ \ctx amt ->
  assertA (amt $>= ca 0) $
  assertA (ctx `atLeast` amt) $
  assertA (ctx `canSub` amt) $
  justE (subU (amt $+ ca 1) &&& amt)

nonN :: Sy Int -> Sy Int -> Symbolic SBool
nonN s1 s2 = return $ (s1 .>= 0) .=> (s2 .>= 0)

trueThm :: ThmResult -> Bool
trueThm = not . modelExists

test :: IO ()
test = do
  (r1,r2) <- check intWitness takeStockTest nonN
  (r3,r4) <- check intWitness takeStockUnsafe nonN
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

  if trueThm r1 && trueThm r2 && not (trueThm r3) && not (trueThm r4)
     then putStrLn "[OK]"
     else putStrLn "[ERROR]"

test2 :: IO ()
test2 = do
  r <- proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    a <- forall "a"
    b <- symbolize (plusA 1 >>> plusA 1) a
    return $ b .== a + 2
  print r
