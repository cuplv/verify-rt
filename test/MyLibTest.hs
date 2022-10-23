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
     (iResult <$> check witness takeStock nonN) @?= Right ()
  ,testCase "Bad takeStock" $
     (iResult <$> check witness badTakeStock nonN) @?= Left ()
  ]
