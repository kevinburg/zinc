module Compile.SSA where

import Compile.Types
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

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
type Blocks = [(String, (Set.Set AVal, [AAsm]))]

parameterize :: [AAsm] -> Blocks
parameterize aasm = let
  p = parameterize' (reverse aasm) Set.empty [] []
  p1 = paramGoto p
  p2 = varGeneration p1
  in p2

-- Perform first pass on code gropuping it into basic blocks.
parameterize' :: [AAsm] -> Set.Set AVal -> [AAsm] -> Blocks -> Blocks
parameterize' [] live aasm b = ("main", (live, aasm)) : b
parameterize' (s : xs) live aasm b = 
  case s of
    ACtrl (Lbl l) -> let
      b' = (l, (live, aasm)) : b
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
paramGoto :: Blocks -> Blocks
paramGoto blocks = Map.map (\(live, aasm) -> (live, map f aasm)) blocks
  where f (ACtrl (Goto l)) = 
          let
            Just (vs, _) = List.lookup l blocks
          in ACtrl $ GotoP l vs
        f (ACtrl (Ifz v l)) = 
          let
            Just (vs, _) = List.lookup l blocks
          in ACtrl $ IfzP v l vs
        f s = s

varGeneration blocks = let
  blocks' = List.map (\(l, (live, aasm)) -> (l, ((live, False), aasm))) blocks
  res = gen blocks' Map.empty
  in List.map (\(l, ((live, _), aasm)) -> (l, (live, aasm))) res

gen [] _ = []
gen (x : xs) m = let
  (res, m') = gen1 x m
  in res : (gen xs m')

gen1 :: (String, ((Set.Set AVal, Bool), [AAsm])) -> Map.Map String Int ->
        ((String, ((Set.Set AVal, Bool), [AAsm])), Map.Map String Int)
gen1 (l, ((live, b), [])) m = ((l, ((live, b), [])), m)
gen1 (l, ((live, False), aasm)) m = let
  m' = Set.fold (\(ALoc (AVar x)) -> \acc -> Map.adjust (+ 1) x acc) m live
  live' = (Set.map (\(ALoc (AVar i)) -> (ALoc (AVarG i (m' Map.! i)))) live, True)
  in gen1 (l, (live', aasm)) m'
gen1 (l, ((live, True), s : aasm)) m = let
  (res, m') = gen2 s m
  ((_, (_, aasm')), m'') = gen1 (l, ((live, True), aasm)) m'
  in ((l, ((live, True), res : aasm')), m'')

gen2 (AAsm {aAssign = [AVar i], aOp = o, aArgs = srcs}) m = let
  srcs' = updateGen srcs m
  m' = case Map.lookup i m of
    Nothing -> Map.insert i 0 m
    (Just g) -> Map.insert i (g+1) m
  dest' = [AVarG i (m' Map.! i)]
  in (AAsm {aAssign = dest', aOp = o, aArgs = srcs'}, m')
gen2 (ACtrl (GotoP i s)) m = let
  res = ACtrl (GotoP i (Set.map (\(ALoc (AVar x)) -> (ALoc (AVarG x (m Map.! x)))) s))
  in (res, m)
gen2 (ACtrl (IfzP v l s)) m = let
  [v'] = updateGen [v] m
  s' = Set.map (\(ALoc (AVar x)) -> ALoc (AVarG x (m Map.! x))) s
  res = ACtrl (IfzP v' l s')
  in (res, m)
gen2 x m = (x,m)

updateGen [] m = []
updateGen ((ALoc (AVar i)) : xs) m = let
  gen = m Map.! i
  in (ALoc (AVarG i gen)) : (updateGen xs m)
updateGen (x : xs) m = x : updateGen xs m

--build blockX calls blockY with params Set.Set AVal
-- builds Map of Block String of Label -> Block String of Code -> Params from Code
--

type Lblmap = Map.Map String (Map.Map String (Set.Set AVal)) 
  
mapBlocks :: Blocks -> Lblmap -> Lblmap
mapBlocks blocks lblmap = let lbls = map (\x -> b lblmap x) blocks
                          in lbls
  where b lblmap lbl vals aasm = let lmap = map (\x -> f lblmap lbl vals x) aasm
                                  in lmap
          where f lblmap lbl vals (ACtrl(IfzP aval goto s)) = Map.insert lbl (Map.insert goto s (lblmap Map.! lbl)) lblmap
                f lblmap lbl vals (ACtrl(GotoP goto s)) = Map.insert lbl (Map.insert goto s (lblmap Map.! lbl)) lblmap
                f lblmap lbl vals (ACtrl(Ifz _ _)) = lblmap --error ("Bad representation of AAsm Ifz not IfzP")
                f lblmap lbl vals (ACtrl(Goto _ _)) = lblmap --error ("Bad representation of AAsm Goto not GotoP")
                f lblmap bl vals _ = lblmap

                         
-- Minimize the blocks 
minimize :: Blocks -> Blocks
minimize [] = []
minimize blocks = let bmap = Map.empty
                      bmap' = mapBlocks blocks $ map (\x -> Map.insert (fst x) Map.empty bmap) blocks
                      min = minimize' blocks bmap'
                  in
                   min
                      
  --rules for minimizing SSA generated code
minimize' :: Blocks -> Lblmap -> Blocks
minimize' [] _ = []
minimize' blocks bmap = let blcks = Map.map (\x -> if Set.size(x) == 1 then replace x else x) bmap
                        in
                         blcks
  where replace lbl vals aasm = (lbl, (vals, aasm))

--go thru map and see if size of where its called from = 1 then update aasm to change vals and change bmap
