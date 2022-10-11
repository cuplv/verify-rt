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
import Store.Model.Map
import Symbol
import qualified Symbol.Map as SMap
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

type TpccG k = (IntG,MapG' k)

-- newOrder :: (Ord k) => Fun (Context (TpccG k)) (Maybe (GUpd (TpccG k), ()))
-- newOrder =
--   tup2 $ \ctx amt ->
--   tup2' ctx $ \stockCtx  -> undefined

takeStock :: Fun (Context IntG, Int) (Maybe (IntUpd, Int))
takeStock = tup2 $ \ctx amt ->
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

type MapG' k = MapG1 k String (NoUpd String)

type MapU' k = MapUpd k String (NoUpd String)

addRecord :: (Ord k) => Fun (Context (MapG' k), Int) (Maybe (MapU' k, ()))
addRecord = tup2 $ \ctx amt ->
  ((stateE ctx &&& amt) &&& deconE (grantE ctx)) >>> maybeElim
    -- When key is granted
    (tup2 $ \s key -> 
      tup2' s $ \records amt ->
        -- Check that it has not been used
        assertA (notE $ memberE key records) $
        justE (insertE key (makeRecord amt) &&& ca ()))
    -- When no key is granted
    (ca Nothing)

  where makeRecord amt = funE amt $ \n ->
          "Order for " ++ show n ++ " units."

addRecordBad :: (Ord k, Avs k) => Fun (Context (MapG' k), (Int, k)) (Maybe (MapU' k, ()))
addRecordBad = tup2 $ \ctx cfg ->
  ((stateE ctx &&& cfg) &&& deconE (grantE ctx)) >>> maybeElim
    -- When key is granted
    (tup2 $ \s key ->
      tup2' s $ \records cfg -> tup2' cfg $ \amt k ->
        -- Check that it has not been used
        assertA (notE $ memberE key records) $
        -- Use a key unrelated to the granted key... unsafe!
        justE (insertE (k >>> conA) (makeRecord amt) &&& ca ()))
    -- When no key is granted
    (ca Nothing)

  where makeRecord amt = funE amt $ \n ->
          "Order for " ++ show n ++ " units."

noLoss :: Sy (Map k v) -> Sy (Map k v) -> Symbolic SBool
noLoss s1 s2 = do
  k <- forall_
  constrain $ SMap.memberM k s1
  return (SMap.matchesM k s1 s2)

trueSpec :: Sy (Map k v) -> Sy (Map k v) -> Symbolic SBool
trueSpec _ _ = return sTrue

trueThm :: ThmResult -> Bool
trueThm = not . modelExists

test :: IO ()
test = do
  (r1,r2) <- check intWitness (pure ()) takeStock nonN
  (r3,r4) <- check intWitness (pure ()) takeStockUnsafe nonN
  (r5,r6) <- check mapWitness SMap.axioms addRecordBad noLoss
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

  if trueThm r1 && trueThm r2 && not (trueThm r3) && not (trueThm r4) && trueThm r5 && trueThm r6
     then putStrLn "[OK]"
     else putStrLn "[ERROR]"

test2 :: IO ()
test2 = do
  r <- proveWith (z3 { verbose = True, satTrackUFs = False }) $ do
    SMap.axioms
    a <- forall "pre"
    b <- symbolize (plusA 1 >>> plusA 1) a
    return $ b .== a + 2
  print r
