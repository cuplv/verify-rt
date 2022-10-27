module Main (main) where

import Transact
import qualified Transact.Int as Int
import qualified Transact.IntMap as IMap
import qualified Transact.MaybeMap as MMap
import qualified Transact.Tpcc.Simple as TpccSimple

import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ intTests
  , maybeMapTests
  , intMapTests
  , tpccTests
  ]

intTests = testGroup "Int"
  [testCase "Good takeStock" $
     checkTest (check Int.witness Int.takeStock Int.nonNegative) checkSuccess
  ,testCase "Bad takeStock" $
     checkTest (check Int.witness Int.badTakeStock Int.nonNegative) checkFail
  ]

maybeMapTests = testGroup "MaybeMap"
  [testCase "addRecord forever" $
    checkTest 
      (checkWith MMap.witness MMap.axioms MMap.addRecord MMap.foreverEntries) 
      checkSuccess
  ,testCase "addRecord ordered" $
    checkTest 
      (checkWith MMap.witness MMap.axioms MMap.addRecord MMap.orderedEntries) 
      checkSuccess
  ,testCase "addRecordBad ordered" $
    checkTest
      (checkWith MMap.witness MMap.axioms MMap.addRecordBad MMap.orderedEntries)
      checkFail
  ,testCase "deliverRecord forever" $
    checkTest
      (checkWith MMap.witness MMap.axioms MMap.deliverRecord MMap.foreverEntries)
      (CheckResult Falsified Proven)
  ,testCase "deliverRecord ordered" $
    checkTest
      (checkWith MMap.witness MMap.axioms MMap.deliverRecord MMap.orderedEntries)
      checkSuccess
  ]

intMapTests = testGroup "IntMap"
  [testCase "IntMap takeStock" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock IMap.nonNegative)
       checkSuccess
  ,testCase "IntMap takeStock1" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 1)
       checkSuccess
  ,testCase "IntMap takeStock2" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 2)
       checkSuccess
  ,testCase "IntMap takeStock3" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 3)
       checkSuccess
  ,testCase "IntMap takeStock4" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 4)
       checkSuccess
  ,testCase "IntMap takeStock5" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 5)
       checkSuccess
  ,testCase "IntMap takeStock6" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 6)
       checkSuccess
  ,testCase "IntMap takeStock7" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 7)
       checkSuccess
  ,testCase "IntMap takeStock8" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeStock $ IMap.nonNegative' 8)
       checkSuccess
  ,testCase "IntMap takeZeroStock" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.takeZeroStock IMap.nonNegative)
       checkSuccess
  ,testCase "IntMap badTakeStock1" $
     checkTest'
       (checkWith IMap.witness IMap.axioms IMap.badTakeStock1 IMap.nonNegative)
       (timeOutFalse, proven) -- because key grants infinite subtr.
  ,testCase "IntMap badTakeStock2" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.badTakeStock2 IMap.nonNegative)
       checkTO -- no clear reason why this must time out...
  ,testCase "IntMap takeStockMulti" $
     checkTest
       (checkWith IMap.witness2 IMap.axioms IMap.takeStockMulti IMap.nonNegative)
       checkSuccess
  ]

tpccTests = testGroup "TPC-C Simple"
  [testCase "Simple newOrder tpccSpec" $
    checkTest
      (checkWith TpccSimple.witness TpccSimple.axioms TpccSimple.newOrder TpccSimple.tpccSpec)
      checkSuccess
  ,testCase "Simple newOrder tooStrict" $
    checkTest
      (checkWith TpccSimple.witness TpccSimple.axioms TpccSimple.newOrder TpccSimple.tooStrict)
      checkSuccess
  ,testCase "Simple newOrder superStrict" $
    checkTest
      (checkWith TpccSimple.witness TpccSimple.axioms TpccSimple.newOrder TpccSimple.superStrict)
      (CheckResult Falsified Proven)
  ]

checkTest :: IO (SBVThmResult,SBVThmResult) -> CheckResult -> IO ()
checkTest c r = c >>= (\r' -> iResult r' @?= r)

checkTest' :: IO (SBVThmResult,SBVThmResult) -> (ResultSpec, ResultSpec) -> IO ()
checkTest' c (r1,r2) = do
  CheckResult r1' r2' <- iResult <$> c
  (r1 r1', r2 r2') @?= (True,True)
