module Main (
    main
) where

import Test.Framework
import Test.Framework.Providers.HUnit

import Compile.RegAllocTests

main :: IO()
main = defaultMain tests

tests :: [Test]
tests = 
  [
    testGroup "RegAlloc"
    [
      testGroup "Migrated from HUnit"  
        (
          hUnitTestToTests testAddNewInter1 ++
          hUnitTestToTests testAddNewInter2 ++
          hUnitTestToTests testGenInter1
        )
    ]
  ]