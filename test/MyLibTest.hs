module Main (main) where

import Transact
import qualified Transact.Int as Int
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
      checkTO
  ,testCase "deliverRecord forever" $
    checkTest
      (checkWith MMap.witness MMap.axioms MMap.deliverRecord MMap.foreverEntries)
      (CheckResult TimeOutFail ThmSuccess)
  ,testCase "deliverRecord ordered" $
    checkTest
      (checkWith MMap.witness MMap.axioms MMap.deliverRecord MMap.orderedEntries)
      checkSuccess
  ]

tpccTests = testGroup "TPC-C"
  [testCase "TPC-C Simple" $
    checkTest
      (checkWith TpccSimple.witness TpccSimple.axioms TpccSimple.newOrder TpccSimple.tpccSpec)
      checkSuccess
  ,testCase "TPC-C Simple tooStrict" $
    checkTest
      (checkWith TpccSimple.witness TpccSimple.axioms TpccSimple.newOrder TpccSimple.tooStrict)
      checkSuccess
  ,testCase "TPC-C Simple superStrict" $
    checkTest
      (checkWith TpccSimple.witness TpccSimple.axioms TpccSimple.newOrder TpccSimple.superStrict)
      (CheckResult TimeOutFail ThmSuccess)
  ]

checkTest :: IO (SBVThmResult,SBVThmResult) -> CheckResult -> IO ()
checkTest c r = c >>= (\r' -> iResult r' @?= r)
