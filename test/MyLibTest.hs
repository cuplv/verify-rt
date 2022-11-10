module Main (main) where

import ALang
import Store.Model
import Transact
import qualified Transact.Courseware as CW
import qualified Transact.Int as Int
import qualified Transact.IntMap as IMap
import qualified Transact.MaybeMap as MMap
import qualified Transact.Set as Set
import qualified Transact.Tpcc.Simple as TpccSimple
import qualified Transact.Tpcc as Tpcc
import Verify

import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ intTests
  , setTests
  , maybeMapTests
  , intMapTests
  , tpccSimpleTests
  , tpccMainTests
  , tpccSplitTests
  , coursewareTests
  ]

intTests = testGroup "Int"
  [testCase "Good takeStock" $
     checkTest (check Int.witness Int.takeStock Int.nonNegative) checkSuccess
  ,testCase "Bad takeStock" $
     checkTest (check Int.witness Int.badTakeStock Int.nonNegative) checkFail
  ]

setTests = testGroup "Set" $
  checkTests "Good insertLeft"
    Set.witness2 noAxioms Set.insertLeft (Set.subsetLR')
    (proven,proven)
  ++
  checkTests "Bad insertLeft"
    Set.witness2 noAxioms Set.badInsertLeft (Set.subsetLR')
    (falsified, proven)
  ++
  checkTests "Good insertRight"
    Set.witness2 noAxioms Set.insertRight (Set.subsetLR')
    (proven,proven)
  ++
  checkTests "Bad insertRight"
    Set.witness2 noAxioms Set.capFailInsertRight (Set.subsetLR')
    (proven,falsified)
  ++
  checkTests "Good deleteLeft"
    Set.witness2 noAxioms Set.deleteLeft (Set.subsetLR')
    (proven,proven)
  ++
  checkTests "Bad deleteLeft"
    Set.witness2 noAxioms Set.capFailDeleteLeft (Set.subsetLR')
    (proven,falsified)
  ++
  checkTests "Good deleteRight"
    Set.witness2 noAxioms Set.deleteRight (Set.subsetLR')
    (proven,proven)
  ++
  checkTests "Bad deleteRight"
    Set.witness2 noAxioms Set.badDeleteRight (Set.subsetLR')
    (falsified,proven)

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
  ,testCase "IntMap takeStockMultiBad" $
     checkTest'
       (checkWith IMap.witness2 IMap.axioms IMap.takeStockMultiBad IMap.nonNegative)
       (timeOutFalse, proven)
  ,testCase "IntMap addBalance" $
     checkTest
       (checkWith IMap.witness IMap.axioms IMap.addBalance IMap.nonNegative)
       checkSuccess
  ]

tpccSimpleTests = testGroup "TPC-C Simple"
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

tpccMainTests = testGroup "TPC-C Main" $
  checkTests "Main newOrder" 
    Tpcc.witness Tpcc.axioms Tpcc.newOrder Tpcc.tpccSpec 
    (proven,proven)
  ++
  checkTests "Main newOrderBad" 
    Tpcc.witness Tpcc.axioms Tpcc.newOrderBad Tpcc.tpccSpec 
    (timeOutFalse,timeOutFalse)
  ++
  checkTests "Main deliver" 
    Tpcc.witness Tpcc.axioms Tpcc.deliver Tpcc.tpccSpec 
    (proven,proven)
  ++
  checkTests "Main payment" 
    Tpcc.witness Tpcc.axioms Tpcc.payment Tpcc.tpccSpec 
    (proven,proven)

tpccSplitTests = testGroup "TPC-C Split" $
  checkTests "Split newOrder stock" 
    Tpcc.witness Tpcc.axioms Tpcc.newOrder Tpcc.tpccSpecA
    (proven,proven)
  ++
  checkTests "Split newOrder orders" 
    Tpcc.witness Tpcc.axioms Tpcc.newOrder Tpcc.tpccSpecB
    (proven,proven)
  ++
  checkTests "Split newOrder customer" 
    Tpcc.witness Tpcc.axioms Tpcc.newOrder Tpcc.tpccSpecC
    (proven,proven)
  ++  
  checkTests "Split deliver stock"
    Tpcc.witness Tpcc.axioms Tpcc.deliver Tpcc.tpccSpecA
    (proven,proven)
  ++  
  checkTests "Split deliver orders"
    Tpcc.witness Tpcc.axioms Tpcc.deliver Tpcc.tpccSpecB
    (proven,proven)
  ++  
  checkTests "Split deliver customer"
    Tpcc.witness Tpcc.axioms Tpcc.deliver Tpcc.tpccSpecC
    (proven,proven)
  ++
  checkTests "Split payment stock" 
    Tpcc.witness Tpcc.axioms Tpcc.payment Tpcc.tpccSpecA
    (proven,proven)
  ++
  checkTests "Split payment orders" 
    Tpcc.witness Tpcc.axioms Tpcc.payment Tpcc.tpccSpecB
    (proven,proven)
  ++
  checkTests "Split payment customer" 
    Tpcc.witness Tpcc.axioms Tpcc.payment Tpcc.tpccSpecC
    (proven,proven)

coursewareTests = testGroup "Courseware" $
  checkTests "registerStudent noDeleteStudent"
    CW.witness CW.axioms CW.registerStudent CW.noDeleteStudent
    (proven,proven)
  ++
  checkTests "enroll enrollDomain"
    CW.witness CW.axioms CW.enroll CW.enrollDomain
    (proven,proven)
  ++
  checkTests "enroll capacityValue"
    CW.witness CW.axioms CW.enroll CW.capacityValue
    (proven,proven)
  ++
  checkTests "unEnroll capacityValue"
    CW.witness CW.axioms CW.unEnroll CW.capacityValue
    (proven,proven)

checkTest :: IO (SBVThmResult,SBVThmResult) -> CheckResult -> IO ()
checkTest c r = c >>= (\r' -> iResult r' @?= r)

checkTest' :: IO (SBVThmResult,SBVThmResult) -> (ResultSpec, ResultSpec) -> IO ()
checkTest' c (r1,r2) = do
  CheckResult r1' r2' <- iResult <$> c
  (r1 r1', r2 r2') @?= (True,True)

checkTests :: (Grant g, Avs w, Avs r) => String -> (g, GUpd g) -> Axioms -> TransactComp g w r -> Spec g -> (ResultSpec, ResultSpec) -> [TestTree]
checkTests name w ax f p (sp,up) =
  [testCase (name ++ " (Spec)") $
     do r <- checkSpec w ax f p
        sp r @?= True
  ,testCase (name ++ " (Update)") $
     do r <- checkUpdate w ax f p
        up r @?= True
  ]
