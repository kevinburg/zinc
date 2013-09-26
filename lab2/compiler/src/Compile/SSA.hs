module Compile.SSA where

import Compile.Types
import qualified Data.Set as Set
import qualified Data.Map as Map

import Debug.Trace

isTemp (ALoc _) = True
isTemp _ = False

ssa aasm = let
  p = parameterize aasm
  in p
  
{- The abstract assembly is group by label. Each label contains the set of variables that
   are live at the time of entering the label and the code that follows. The set of live
   variables will be used to put paramters on the labels and gotos.
-}
type Blocks = Map.Map String (Set.Set AVal, [AAsm])

parameterize :: [AAsm] -> Blocks
parameterize aasm = let
  p = parameterize' (reverse aasm) Set.empty [] Map.empty
  p' = paramGoto p
  in p'

-- Perform first pass on code gropuping it into basic blocks.
parameterize' :: [AAsm] -> Set.Set AVal -> [AAsm] -> Blocks -> Blocks
parameterize' [] live aasm b = Map.insert "main" (live, aasm) b
parameterize' (s : xs) live aasm b = 
  case s of
    ACtrl (Lbl l) -> let
      b' = Map.insert l (live, aasm) b
      in parameterize' xs live [] b'
    ACtrl (Goto _) ->
      parameterize' xs live (s : aasm) b
    ACtrl (Ifz v l) -> let
      live' = Set.insert v live
      in parameterize' xs live' (s : aasm) b
    ACtrl (Ret v) -> let
      live' = Set.insert v live
      in parameterize' xs live' (s : aasm) b
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} -> let
      srcs' = filter isTemp srcs
      live' = Set.union (Set.fromList srcs') (Set.delete (ALoc dest) live)
      in parameterize' xs live' (s : aasm) b
         
-- Put the paramters back on the gotos in the second pass.
paramGoto blocks = Map.map (\(live, aasm) -> (live, map f aasm)) blocks
  where f (ACtrl (Goto l)) = 
          let
            (vs, _) = blocks Map.! l
          in ACtrl $ GotoP l vs
        f (ACtrl (Ifz v l)) = 
          let
            (vs, _) = blocks Map.! l
          in ACtrl $ IfzP v l vs
        f s = s