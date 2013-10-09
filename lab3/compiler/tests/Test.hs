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
    testGroup "Cgc"
    (
      hUnitTestToTests testBuildGraph ++
      hUnitTestToTests testColoring ++
      hUnitTestToTests testColoring1
    )
  ]
