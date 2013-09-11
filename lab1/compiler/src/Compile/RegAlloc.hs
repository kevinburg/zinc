module Compile.RegAlloc where

import Compile.Types
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Compile.Cgc as Cgc

import Debug.Trace

-- Evaluates to a map of the form ALoc -> Register
allocateRegisters aasm =
  let
    (res, vars) = genInter aasm
    regMap = genRegMap res vars
    prgm = foldr (\x -> \y -> show x ++ "\n" ++ y) "" aasm
  in trace ("\n" ++ prgm ++ "\n\n" ++ show res ++ "\n\n" ++ show regMap) regMap

addNewInter :: AVal -> Set.Set AVal -> Set.Set (AVal, AVal)
addNewInter (ALoc loc) s =
  Set.map (\x -> (ALoc loc, x)) s
addNewInter (AImm _) s =
  Set.empty

isTemp (ALoc _) = True
isTemp _ = False

genInter stmts = 
  let
    (inter, vars) = genInter' (reverse stmts) Set.empty Set.empty Set.empty
  in
    (Set.filter (\(x,y) -> x /= y) inter, vars)
  
genInter' [] _ inter vars = (inter, vars)
genInter' (stmt : aasm) l inter vars =
  case stmt of
    ACtrl Ret loc ->
      let
        l' = Set.insert loc l
        newInter = Set.map (\x -> (loc, x)) l
        inter' = Set.union inter newInter
      in genInter' aasm l' inter' (Set.insert loc vars)
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} ->
      let
        l' = Set.delete (ALoc dest) l
        newInter = Set.map (\x -> (ALoc dest, x)) l
        inter' = Set.union inter newInter
        live = Set.union (Set.fromList (filter isTemp srcs)) l'
      in genInter' aasm live inter' (Set.insert (ALoc dest) vars)

genRegMap graph vars = 
  let
    g = Cgc.buildGraph (Set.toList vars) (Set.toList graph)
    m = Cgc.coloring g
  in Map.map (\r -> Reg r) m