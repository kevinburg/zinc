module Compile.SSA where

import Compile.Types
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

import Debug.Trace

isTemp (ALoc _) = True
isTemp _ = False

ssa :: [AAsm] -> Blocks
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
  prgm = foldr (\x -> \y -> (show x) ++ "\n" ++ y) "" aasm
  p = parameterize' (reverse aasm) Set.empty [] []
  p1 = trace (prgm ++ "\n\n") $ paramGoto p
  p2 = varGeneration p1
  in p2

-- Perform first pass on code gropuping it into basic blocks.
parameterize' :: [AAsm] -> Set.Set AVal -> [AAsm] -> Blocks -> Blocks
parameterize' [] live aasm b = ("top", (live, aasm)) : b
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
paramGoto blocks = List.map (\(l,(live, aasm)) -> (l,(live, map f aasm))) blocks
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
  live' = Set.filter isVar live
  m' = Set.fold (\(ALoc (AVar x)) -> \acc -> Map.adjust (+ 1) x acc) m live'
  live'' = (Set.map (updateGen m') live', True)
  in gen1 (l, (live'', aasm)) m'
gen1 (l, ((live, True), s : aasm)) m = let
  (res, m') = gen2 s m
  ((_, (_, aasm')), m'') = gen1 (l, ((live, True), aasm)) m'
  in ((l, ((live, True), res : aasm')), m'')
gen2 (AAsm {aAssign = [AVar i], aOp = o, aArgs = srcs}) m = let
  srcs' = map (updateGen m) srcs
  m' = case Map.lookup i m of
    Nothing -> Map.insert i 0 m
    (Just g) -> Map.insert i (g+1) m
  dest' = [AVarG i (m' Map.! i)]
  in (AAsm {aAssign = dest', aOp = o, aArgs = srcs'}, m')
gen2 (AAsm {aAssign = [dest], aOp = o, aArgs = srcs}) m = let
  srcs' = map (updateGen m) srcs
  in (AAsm {aAssign = [dest], aOp = o, aArgs = srcs'}, m)
gen2 (ACtrl (GotoP i s)) m = let
  s' = Set.filter isVar s
  res = ACtrl (GotoP i (Set.map (updateGen m) s'))
  in (res, m)
gen2 (ACtrl (IfzP v l s)) m = let
  [v'] = map (updateGen m) [v]
  s' = Set.map (updateGen m) s
  res = ACtrl (IfzP v' l s')
  in (res, m)
gen2 x m = (x,m)

isVar (ALoc (AVar _)) = True
isVar _ = False

updateGen m (ALoc (AVar i)) = let
  gen = case Map.lookup i m of
    Nothing -> 0
    Just g -> g
  in ALoc (AVarG i gen)
updateGen _ x = x

--build blockX calls blockY with params Set.Set AVal
-- builds Map of Block String of Label -> Block String of Code -> Params from Code
--

type Lblmap = Map.Map String [(String, Set.Set AVal)]
  
mapBlocks :: Blocks -> Lblmap
mapBlocks blocks = Map.fromList $ zipmap $ grpby $ concat (map (\(lbl,(vals,aasm)) -> (map (\x -> f(lbl,x)) aasm)) blocks)
  where grpby l = List.groupBy (\(x,y)-> \(a,b)-> x==a) $ List.filter (\(x,y)-> x=="") l
        zipmap l = zip (map (\x -> fst (head x)) l) (map (\x -> map (snd) x) l)
        f (lbl, (ACtrl(IfzP aval goto s))) = (lbl, (goto, s)) --possibly flip goto and lbl here
        f (lbl, (ACtrl(GotoP goto s))) = (lbl, (goto, s))
        f (lbl, x) = ("",("",Set.empty)) 
 
{- 
mapBlocks blocks lblmap = let bmap = map (\(lbl,(vals,aasm)) -> Map.insert lbl vals empty) blocks
                              lbls = map (\x -> )blocks
                                -- map (\(lbl, (vals, aasm))-> b lblmap lbl vals aasm) blocks
                          in lbls
  where b lblmap lbl vals aasm = let lmap = map (\x -> f lblmap lbl vals x) aasm
                                  in lmap
          where f lblmap lbl vals (ACtrl(IfzP aval goto s)) = Map.insert lbl (Map.insert goto s (lblmap Map.! lbl)) lblmap
                f lblmap lbl vals (ACtrl(GotoP goto s)) = Map.insert lbl (Map.insert goto s (lblmap Map.! lbl)) lblmap
                f lblmap lbl vals (ACtrl(Ifz _ _)) = lblmap --error ("Bad representation of AAsm Ifz not IfzP")
                f lblmap lbl vals (ACtrl(Goto _)) = lblmap --error ("Bad representation of AAsm Goto not GotoP")
                f lblmap bl vals _ = lblmap
-}
                         
-- Minimize the blocks 
minimize :: Blocks -> Blocks
minimize [] = []
minimize blocks = let bmap = mapBlocks blocks
                             -- $ Map.fromList $ map (\(lbl,(vals,aasm)) -> Map.insert lbl Set.empty bmap) blocks
                      min = minimize' blocks bmap
                  in
                   min
                      
  --rules for minimizing SSA generated code
minimize' :: Blocks -> Lblmap -> Blocks
minimize' [] _ = []
minimize' blocks lblmap = let bmap = Map.fromList blocks
                              blcks = map (\(lbl,(vals,aasm)) -> let l = (lblmap Map.! lbl)
                                                                 in if length l == 1
                                                                    then replace lbl aasm (snd $ head l)
                                                                    else (lbl,(bmap Map.! lbl))) blocks
                        in
                         blcks
        -- replaces the vals in the lbl aasm with the vals from the goto val set
  where replace lbl aasm gvals = let gvalmap = Map.fromList(map (\(ALoc(AVarG i gen)) -> (i,gen)) $ Set.toList(gvals))
                                 in (lbl, (Set.empty, (map (\x-> f gvalmap x) aasm)))
                                        -- ^REPLACE^ --
          where f gvalmap AAsm{aAssign=locs, aOp=o, aArgs=args} =
                  AAsm{aAssign=(map (\x -> r gvalmap x) locs), aOp=o, aArgs=(map (\x -> r' gvalmap x) args)}
                  where r gvalmap (AVarG i gen) = if Map.member i gvalmap
                                                  then AVarG i (gvalmap Map.! i)
                                                  else AVarG i gen
                        r gvalmap loc = loc
                        r' gvalmap (ALoc g) = ALoc (r gvalmap g)
                        r' gvalmap (AImm i) = AImm i
                  -- =ALoc(AVarG i2 (gvalmap Map.! i2))} 
                f gvalmap (ACtrl(Ret(ALoc(AVarG i1 gen1)))) =
                  if Map.member i1 gvalmap
                  then ACtrl(Ret(ALoc(AVarG i1 (gvalmap Map.! i1))))
                  else ACtrl(Ret(ALoc(AVarG i1 gen1)))
                f gvalmap (ACtrl(GotoP s valset)) =
                  if s == lbl
                  then ACtrl(GotoP s Set.empty)
                  else ACtrl(GotoP s valset)
                f gvalmap (ACtrl(IfzP(ALoc(AVarG i gen)) s valset)) =
                  if Map.member i gvalmap
                  then ACtrl(IfzP(ALoc(AVarG i (gvalmap Map.! i))) s valset)
                  else ACtrl(IfzP(ALoc(AVarG i gen)) s valset)
                f g a = a

--go thru map and see if size of where its called from = 1 then update aasm to change vals and change bmap
                 


-- Turn the SSA code back into non SSA code that gets rid of parameterized labels and gotos
-- Basically, assign label vals with goto vals before goto
deSSA :: Blocks -> [AAsm]
deSSA blocks = let bmap = Map.fromList blocks
               in concat $ map (\(lbl,(vals,aasm)) -> [ACtrl(Lbl lbl)] ++ (concat $ map (\x -> f bmap x) aasm)) blocks
  where f bmap (ACtrl(GotoP goto valset)) =
          let (gvals,_) = bmap Map.! goto
              gvals' = Set.toAscList gvals
              valset' = Set.toAscList valset
              valpairs = zip valset' gvals'
              valpairs' = map (\(ALoc(AVarG s1 i1),ALoc(AVarG s2 i2))->(ALoc(AVar(s1++(show i1))),ALoc(AVar(s2++(show i2))))) valpairs 
              assigns = map (\(x,ALoc y) -> AAsm{aAssign=[y],aOp=Nop,aArgs=[x]}) valpairs'
          in
           assigns ++ [ACtrl $ Goto goto]
        f bmap (ACtrl(IfzP val goto valset)) =
          let (gvals,_) = bmap Map.! goto
              gvals' = Set.toAscList gvals
              valset' = Set.toAscList valset
              valpairs = zip valset' gvals'
              valpairs' = map (\(ALoc(AVarG s1 i1),ALoc(AVarG s2 i2))->(ALoc(AVar(s1++(show i1))),ALoc(AVar(s2++(show i2))))) valpairs
              assigns = map (\(x,ALoc y) -> AAsm{aAssign=[y],aOp=Nop,aArgs=[x]}) valpairs'
              stmt = case val of
                ALoc(AVarG s i) ->
                  ACtrl(Ifz(ALoc(AVar (s ++ (show i)))) goto)
                t -> ACtrl(Ifz t goto)
          in
           assigns ++ [stmt]
        f bmap (ACtrl(Ret(ALoc(AVarG s i)))) = [ACtrl(Ret(ALoc(AVar (s ++ (show i)))))]
        f bmap AAsm{aAssign=locs, aOp = o, aArgs = vals} =
          let locs' = map (\x -> case x of
                              AVarG s i -> AVar (s ++ (show i))
                              a -> a
                          ) locs
              vals' = map (\(x) -> case x of
                              ALoc(AVarG s i) -> ALoc(AVar(s ++ (show i)))
                              y -> y
                          )vals
          in
           [AAsm {aAssign=locs', aOp = o, aArgs = vals'}]
        f bmap aasm = [aasm]
          
          
          --go thru aasm in blocks and assign lbl vals with goto vals and change vals to AVar "x#"
          
