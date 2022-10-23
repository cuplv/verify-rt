module Main (main) where

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
     check takeStock nonN @?= Right ()
   testCase "Bad takeStock" $
     check badTakeStock nonN @?= Left 
  ]
