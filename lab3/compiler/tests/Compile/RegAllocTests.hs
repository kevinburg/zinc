module Compile.RegAllocTests where

import Compile.Types
import Compile.RegAlloc
import Test.HUnit
import Data.Set as Set
import Data.Map as Map

testAddNewInter1 :: Test
testAddNewInter1 = 
  "addNewInter AImm" ~: Set.empty @=? 
  addNewInter (AImm 0) (Set.fromList [ALoc $ ATemp 0])
  
testAddNewInter2 =
  "addNewInter ALoc" ~: ((Set.fromList [(ALoc $ ATemp 0, ALoc $ ATemp 1),
                                        (ALoc $ ATemp 0, ALoc $ ATemp 2)]) :: Set.Set (AVal, AVal)) @=?
  addNewInter (ALoc $ ATemp 0) (Set.fromList [ALoc $ ATemp 1, ALoc $ ATemp 2])

program1 =
  [AAsm {aAssign = [ATemp 0], aOp = Nop, aArgs = [AImm 0]},
   AAsm {aAssign = [ATemp 1], aOp = Nop, aArgs = [AImm 1]},
   AAsm {aAssign = [AReg 0], aOp = Nop, aArgs = [ALoc $ ATemp 0]},
   ACtrl Ret (ALoc $ AReg 0)]

testGenInter1 =
  "genInter" ~: (Set.fromList [(ALoc $ ATemp 1, ALoc $ ATemp 0)], 
                 Set.fromList [ALoc $ ATemp 0, ALoc $ ATemp 1, ALoc $ AReg 0]) @=?
  genInter program1

testAllocate1 =
  "allocate1" ~: (Map.fromList [(ALoc (AReg 0), Reg EAX),
                                (ALoc (AReg 3), Reg EDX),
                                (ALoc (ATemp 0), Reg EAX),
                                (ALoc (ATemp 1), Reg EBX)]) @=?
  allocateRegisters program1
