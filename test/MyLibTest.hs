module Main (main) where

import Transact
import Transact.Int

import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ intTests
  ]

intTests = testGroup "Int"
  [testCase "Good takeStock" $
     checkTest (check witness takeStock nonNegative) checkSuccess
  ,testCase "Bad takeStock" $
     checkTest (check witness badTakeStock nonNegative) checkFail
  ]

checkTest :: IO (SBVThmResult,SBVThmResult) -> CheckResult -> IO ()
checkTest c r = c >>= (\r' -> iResult r' @?= r)
