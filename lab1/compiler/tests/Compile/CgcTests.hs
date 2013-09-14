module Compile.CgcTests where

import Compile.Types
import Compile.Cgc
import Test.HUnit
import Data.Set as Set
import Data.Map as Map

testBuildGraph :: Test
testBuildGraph =
  "testBuildGraph" ~: (Map.fromList [(ALoc (AReg 0), []),
                                     (ALoc (ATemp 0), [ALoc (ATemp 1)]),
                                     (ALoc (ATemp 1), [ALoc (ATemp 0), ALoc (ATemp 2)]),
                                     (ALoc (ATemp 2), [ALoc (ATemp 1)])]) @=?
  buildGraph [ALoc (ATemp 0), ALoc (ATemp 1), ALoc (AReg 0), ALoc (ATemp 2)]
  [(ALoc (ATemp 0), ALoc (ATemp 1)), (ALoc (ATemp 2), ALoc (ATemp 1)),
   (ALoc (ATemp 1), ALoc (ATemp 2))]
                                      
graph1 = buildGraph [ALoc (ATemp 0), ALoc (ATemp 1), ALoc (AReg 0), ALoc (ATemp 2)]
         [(ALoc (ATemp 0), ALoc (ATemp 1)), (ALoc (ATemp 2), ALoc (ATemp 1)),
          (ALoc (ATemp 1), ALoc (ATemp 2))]

testColoring :: Test
testColoring =
  "testColoring" ~: (Map.fromList [(ALoc (AReg 0), EAX),
                                   (ALoc (AReg 3), EDX),
                                   (ALoc (ATemp 0), EAX),
                                   (ALoc (ATemp 1), EBX),
                                   (ALoc (ATemp 2), EAX)]) @=?
  coloring graph1
