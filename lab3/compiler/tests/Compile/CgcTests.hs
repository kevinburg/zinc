module Compile.CgcTests where

import Compile.Types
import Compile.Cgc
import Test.HUnit
import Data.Set as Set
import Data.Map as Map

testBuildGraph :: Test
testBuildGraph =
  "testBuildGraph" ~: (Map.fromList [((AReg EAX), []),
                                     ((ATemp 0), [  (ATemp 1)]),
                                     ((ATemp 1), [  (ATemp 0),   (ATemp 2)]),
                                     ((ATemp 2), [  (ATemp 1)])]) @=?
  buildGraph [(ATemp 0), (ATemp 1), (AReg EAX), (ATemp 2)]
  [((ATemp 0), (ATemp 1)), ((ATemp 2), (ATemp 1)),
   ((ATemp 1), (ATemp 2))]
                                      
graph1 = buildGraph [(ATemp 0), (ATemp 1),
                     (AReg EAX), (ATemp 2)]
         [((ATemp 0), (ATemp 1)), ((ATemp 2), (ATemp 1)),
          ((ATemp 1), (ATemp 2))]


base = [(ARes, Reg EAX), (AReg EAX, Reg EAX), (AReg ECX, Reg ECX), (AReg EDX, Reg EDX)] ++
       [(AArg i, Reg r) | (i,r) <- [(0,EAX),(1,EDI),(2,ESI),(3,EDX),(4,ECX),(5,R8D),(6,R9D)]]

testColoring :: Test
testColoring =
  "testColoring" ~: (Map.fromList $ base ++
                     [((ATemp 0), Reg EAX),
                      ((ATemp 1), Reg EDI),
                      ((ATemp 2), Reg EAX)]) @=?
  coloring graph1


graph2 = buildGraph [AArg 0, AArg 1, AArg 2, ATemp 0, ATemp 1, ATemp 2,
                     ATemp 3, ATemp 4, ARes]
         [(AArg 1, ATemp 0), (AArg 2, ATemp 0), (ATemp 0, ATemp 2),
          (ATemp 0, ATemp 1), (ATemp 1, AArg 2), (ATemp 1, ATemp 2), (ATemp 2, ATemp 3)]

testColoring1 =
  "testColoring1" ~: (Map.fromList $ base ++
                      [(ATemp 0, Reg EAX),
                       (ATemp 1, Reg EDX),
                       (ATemp 2, Reg EDI),
                       (ATemp 3, Reg EAX),
                       (ATemp 4, Reg EAX)]) @=?
  coloring graph2
