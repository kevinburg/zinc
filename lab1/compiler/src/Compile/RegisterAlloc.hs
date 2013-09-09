module Compile.RegisterAlloc where

import Compile.Types
import qualified Data.Set as Set

addNewInter (ALoc loc) s =
  Set.map (\x -> (ALoc loc, x)) s
addNewInter (AImm _) s =
  Set.empty

isTemp (ALoc _) = True
isTemp _ = False

genInter [] _ inter = inter
genInter (stmt : aasm) l inter =
  case stmt of
    ACtrl Ret loc ->
      let
        newInter = addNewInter loc l
        l' = Set.insert loc l
        inter' = Set.union inter newInter
      in genInter aasm l' inter'
    -- only have single dest instructions
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} ->
      let
        l' = Set.delete (ALoc dest) l
        newInters = addNewInter (ALoc dest) l'
        inter' = Set.union inter newInters
        live = Set.union (Set.fromList (filter isTemp srcs))  l'
      in genInter aasm live inter'    
