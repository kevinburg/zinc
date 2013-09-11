module Compile.RegAllocTests where

import Compile.Types
import Compile.RegAlloc
import Test.HUnit
import Data.Set as Set

testAddNewInter1 :: Test
testAddNewInter1 = 
  "addNewInter AImm" ~: Set.empty @=? 
  addNewInter (AImm 0) (Set.fromList [ALoc $ ATemp 0])
  
testAddNewInter2 =
  "addNewInter ALoc" ~: ((Set.fromList [(ALoc $ ATemp 0, ALoc $ ATemp 1),
                                        (ALoc $ ATemp 0, ALoc $ ATemp 2)]) :: Set.Set (AVal, AVal)) @=?
  addNewInter (ALoc $ ATemp 0) (Set.fromList [ALoc $ ATemp 1, ALoc $ ATemp 2])
