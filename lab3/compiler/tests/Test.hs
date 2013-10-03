module Main (
    main
) where

import Test.Framework
import Test.Framework.Providers.HUnit

import Compile.RegAllocTests
import Compile.CgcTests

main :: IO()
main = defaultMain tests

tests :: [Test]
tests = 
  [
    testGroup "RegAlloc"
    (
      hUnitTestToTests testAddNewInter1 ++
      hUnitTestToTests testAddNewInter2 ++
      hUnitTestToTests testGenInter1 ++
      hUnitTestToTests testAllocate1
    ),
    testGroup "Cgc"
    (
      hUnitTestToTests testBuildGraph ++
      hUnitTestToTests testColoring
    )
  ]
