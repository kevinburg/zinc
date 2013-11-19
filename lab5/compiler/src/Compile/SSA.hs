module Compile.SSA where

import Compile.Types
import qualified Compile.RegAlloc as RA
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

import Debug.Trace

isTemp (ALoc _) = True
isTemp _ = False

{- TODO: We should at the very least figure out constant propogation.
Save it for lab5?

We also never did minimization. This is kind of a big deal because it
affects our performance in register allocation.
-}

ssa :: [AAsm] -> String -> Int -> Blocks
ssa aasm fun opt = let
  l = parameterize aasm fun
  in if opt == 0 then
       minimize l
     else let
       (_, opt) = foldl (\(m, acc) -> \(fun, (s, aasm)) -> let
                            (code, m') = optimize aasm m
                            in (m', acc ++ [(fun, (s, code))]))
                  (Map.empty, []) (minimize l)
       opt1 = map (\(fun, (s, aasm)) -> (fun, (s, cse aasm))) opt
       in opt1
          
optimize p m =
  let
    (constProp, m1) = 
      foldl (\(aasm, m) -> \inst ->
              case inst of
                (AAsm {aAssign = [loc], aOp = Nop, aArgs = [AImm i]}) ->
                  case loc of
                    (ATemp _) -> let
                      m' = Map.insert (ALoc loc) (AImm i) m
                      in (aasm, m')
                    (AVarG _ _) -> let
                      m' = Map.insert (ALoc loc) (AImm i) m
                      in (aasm, m')
                    _ -> (aasm ++ [inst], m)
                (AAsm {aAssign = [loc], aOp = o, aArgs = srcs}) -> let
                  srcs' = map (copy m) srcs
                  in case constantFold o srcs' of
                    Nothing -> (aasm ++ [AAsm {aAssign = [loc], aOp = o, aArgs = srcs'}], m)
                    Just (val, op) ->
                      case loc of
                        (ATemp _) -> let
                          m' = Map.insert (ALoc loc) val m
                          in (aasm, m')
                        (AVarG _ _) -> let
                          m' = Map.insert (ALoc loc) val m
                          in (aasm, m')
                        _ -> let
                          inst = [AAsm [loc] op [val]]
                          in (aasm ++ inst, m)
                (ACtrl (GotoP lbl l)) -> let
                  l' = map (\(var, _) -> (var, Just $ copy m (ALoc var))) l
                  in (aasm ++ [ACtrl $ GotoP lbl l'], m)
                (ACtrl (IfzP v lbl b l)) -> let
                  l' = map (\(var, _) -> (var, Just $ copy m (ALoc var))) l
                  in (aasm ++ [ACtrl $ IfzP (copy m v) lbl b l'], m)
                (ACtrl (CompP v1 v2 op lbl l)) -> let
                  l' = map (\(var, _) -> (var, Just $ copy m (ALoc var))) l
                  in (aasm ++ [ACtrl $ CompP (copy m v1) (copy m v2) op lbl l'], m)
                x -> (aasm ++ [x], m)
            ) ([], m) p
    (copyProp, m2) = constProp `seq`
      foldl (\(aasm, m) -> \inst ->
              case inst of
                (AAsm {aAssign = [loc], aOp = op, aArgs = [s]}) | op == Nop || op == MemMov Small ->
                  case (loc, s) of
                    (ARes, _) -> let
                      s' = copyPt m s
                      inst' = [AAsm [loc] op [s']]
                      in (aasm ++ inst', m)
                    (AArg _, _) -> let
                      s' = copyPt m s
                      inst' = [AAsm [loc] op [s']]
                      in (aasm ++ inst', m)
                    (Register _, _) -> let
                      s' = copyPt m s
                      inst' = [AAsm [loc] op [s']]
                      in (aasm ++ inst', m)
                    (Pt l, _) -> let
                      s' = copyPt m s
                      ALoc l' = copyPt m (ALoc l)
                      inst' = [AAsm [Pt l'] op [s']]
                      in (aasm ++ inst', m)
                    (_, ALoc (Pt x)) -> let
                      ALoc x' = copyPt m (ALoc x)
                      inst' = [AAsm [loc] op [ALoc (Pt x')]]
                      in (aasm ++ inst', m)
                    (_, (AImm _)) -> let
                      ALoc loc' = copyPt m (ALoc loc)
                      inst' = [AAsm [loc'] op [s]]
                      in (aasm ++ inst', m)
                    (_, (ALoc (AArg _))) -> let
                      ALoc loc' = copyPt m (ALoc loc)
                      inst' = [AAsm [loc'] op [s]]
                      in (aasm ++ inst', m)
                    (_, (ALoc ARes)) -> let
                      ALoc loc' = copyPt m (ALoc loc)
                      inst' = [AAsm [loc'] op [s]]
                      in (aasm ++ inst', m)
                    (_, (ALoc (Register _))) -> let
                      ALoc loc' = copyPt m (ALoc loc)
                      inst' = [AAsm [loc'] op [s]]
                      in (aasm ++ inst', m)
                    _ -> let
                      s' = copyPt m s
                      m' = copyInsert (ALoc loc) s' m
                      in (aasm, m')
                (AAsm {aAssign = [loc], aOp = o, aArgs = srcs}) -> let
                  ALoc loc' = copyPt m (ALoc loc)
                  srcs' = map (copyPt m) srcs
                  inst = [AAsm [loc'] o srcs']
                  in (aasm ++ inst, m)
                (ACtrl (GotoP lbl l)) -> let
                  l' = map (\(var, _) -> (var, Just $ copyPt m (ALoc var))) l
                  in (aasm ++ [ACtrl $ GotoP lbl l'], m)
                (ACtrl (IfzP v lbl b l)) -> let
                  l' = map (\(var, _) -> (var, Just $ copyPt m (ALoc var))) l
                  in (aasm ++ [ACtrl $ IfzP (copy m v) lbl b l'], m)
                (ACtrl (CompP v1 v2 op lbl l)) -> let
                  l' = map (\(var, _) -> (var, Just $ copyPt m (ALoc var))) l
                  in (aasm ++ [ACtrl $ CompP (copy m v1) (copy m v2) op lbl l'], m)
                x -> (aasm ++ [x], m)
            ) ([], m1) constProp
    string = copyProp `seq` ((show constProp) ++ "\n" ++ (show copyProp) ++ "\n\n")
  in (copyProp, m2)
  --in (constProp, m2)
     where copy m x =
             case Map.lookup x m of
               (Just c) -> c
               _ -> x
           copyPt m (ALoc (Pt x)) =
             case Map.lookup (ALoc x) m of
               (Just (ALoc c)) -> ALoc $ Pt c
               _ -> ALoc $ Pt x
           copyPt m x = copy m x
           copyInsert k v m =
             case Map.lookup v m of
               Just v' -> copyInsert k v' m
               Nothing -> Map.insert k v m
           constantFold Div _ = Nothing
           constantFold Mod _ = Nothing
           constantFold Nop [AImm i] = Just (AImm i, Nop)
           constantFold Add [AImm i, AImm j] = Just (AImm (mod (i+j) $ 2^32), Nop)
           constantFold Add [s, AImm 0] = Just (s, Nop)
           constantFold Add [AImm 0, s] = Just (s, Nop)
           constantFold Mul [AImm i, AImm j] = Just (AImm (mod (i*j) $ 2^32), Nop)
           constantFold Mul [s, AImm 0] = Just (AImm 0, Nop)
           constantFold Mul [s, AImm 1] = Just (s, Nop)
           constantFold Geq [AImm i, AImm j] = Just (AImm (if i >= j then 1 else 0), Nop)
           constantFold Gt [AImm i, AImm j] = Just (AImm (if i > j then 1 else 0), Nop)
           constantFold Leq [AImm i, AImm j] = Just (AImm (if i <= j then 1 else 0), Nop)
           constantFold Lt [AImm i, AImm j] = Just (AImm (if i < j then 1 else 0), Nop)
           constantFold _ _ = Nothing

cse code = let
  res = foldl (\(aasm, m) -> \inst ->
                case inst of
                  (AAsm [loc] Mul [s1, s2]) ->
                    case Map.lookup (Mul, (s1, s2)) m of
                      Just var -> let
                        inst' = [AAsm [loc] Nop [var]]
                        in (aasm ++ inst', m)
                      Nothing -> let
                        m' = Map.insert (Mul, (s1, s2)) (ALoc loc) m
                        in (aasm ++ [inst], m')
                  y -> (aasm ++ [y], m)) ([], Map.empty) code
  (code', _) = res
  in code'
                     

{- The abstract assembly is group by label. Each label contains the set of variables that
   are live at the time of entering the label and the code that follows. The set of live
   variables will be used to put paramters on the labels and gotos.
-}
type Blocks = [(String, (Set.Set ALoc, [AAsm]))]

parameterize :: [AAsm] -> String -> Blocks
parameterize aasm fun = let
  live = RA.liveVars aasm
  p = parameterize' (reverse aasm) live 0 [] [] fun
  p1 = paramGoto p
  p2 = varGeneration p1
  in p2

-- Perform first pass on code gropuping it into basic blocks.
parameterize' :: [AAsm] -> Map.Map Int (Set.Set ALoc) -> Int -> [AAsm] -> Blocks ->
                 String -> Blocks
parameterize' [] live i aasm b fun = ("top_"++fun, (Set.empty, aasm)) : b
parameterize' (s : xs) live i aasm b fun = 
  case s of
    ACtrl (Lbl l) -> let
      liveVars = live Map.! i
      b' = (l, (liveVars, aasm)) : b
      in parameterize' xs live (i+1) [] b' fun
    _ -> parameterize' xs live (i+1) (s : aasm) b fun

-- Put the paramters back on the gotos in the second pass.
paramGoto :: Blocks -> Blocks
paramGoto blocks = List.map (\(l,(live, aasm)) -> (l,(live, map f aasm))) blocks
  where f (ACtrl (Goto l)) = 
          let
            vs = case List.lookup l blocks of
              Just (vs, _) -> vs
              Nothing -> Set.empty
          in ACtrl $ GotoP l $ map (\x -> (x, Nothing)) (Set.toList vs)
        f (ACtrl (Ifz v l b)) = 
          let
            vs = case List.lookup l blocks of
              Just (vs, _) -> vs
              Nothing -> Set.empty
          in ACtrl $ IfzP v l b $ map (\x -> (x, Nothing)) (Set.toList vs)
        f (ACtrl (Comp v1 v2 op l)) = 
          let
            vs = case List.lookup l blocks of
              Just (vs, _) -> vs
              Nothing -> Set.empty
          in ACtrl $ CompP v1 v2 op l $ map (\x -> (x, Nothing)) (Set.toList vs)
        f s = s

varGeneration blocks = let
  blocks' = List.map (\(l, (live, aasm)) -> (l, ((live, False), aasm))) blocks
  res = gen blocks' Map.empty
  in List.map (\(l, ((live, _), aasm)) -> (l, (live, aasm))) res

gen [] _ = []
gen (x : xs) m = let
  (res, m') = gen1 x m
  in res : (gen xs m')

gen1 :: (String, ((Set.Set ALoc, Bool), [AAsm])) -> Map.Map String Int ->
        ((String, ((Set.Set ALoc, Bool), [AAsm])), Map.Map String Int)
gen1 (l, ((live, b), [])) m = ((l, ((live, b), [])), m)
gen1 (l, ((live, False), aasm)) m = let
  live' = Set.filter isVar live
  m' = Set.fold (\(AVar x) -> \acc -> Map.adjust (+ 1) x acc) m live'
  live'' = (Set.map (updateGen m') live', True)
  in gen1 (l, (live'', aasm)) m'
gen1 (l, ((live, True), s : aasm)) m = let
  (res, m') = gen2 s m
  ((_, (_, aasm')), m'') = gen1 (l, ((live, True), aasm)) m'
  in ((l, ((live, True), res : aasm')), m'')
gen2 (AAsm {aAssign = [AVar i], aOp = o, aArgs = srcs}) m = let
  srcs' = map (updateGen' m) srcs
  m' = case Map.lookup i m of
    Nothing -> Map.insert i 0 m
    (Just g) -> Map.insert i (g+1) m
  dest' = [AVarG i (m' Map.! i)]
  in (AAsm {aAssign = dest', aOp = o, aArgs = srcs'}, m')
gen2 (AAsm {aAssign = [Pt (AVar i)], aOp = o, aArgs = srcs}) m = let
  srcs' = map (updateGen' m) srcs
  dest' = [Pt $ AVarG i (m Map.! i)] -- this should be ok because if
                                -- we are using (Pt var x) then var x
                                -- must have already been defined.
  in (AAsm {aAssign = dest', aOp = o, aArgs = srcs'}, m)
gen2 (AAsm {aAssign = [dest], aOp = o, aArgs = srcs}) m = let
  srcs' = map (updateGen' m) srcs
  in (AAsm {aAssign = [dest], aOp = o, aArgs = srcs'}, m)
gen2 (ACtrl (GotoP i s)) m = let
  s' = filter (\(x, _) -> isVar x) s
  res = ACtrl (GotoP i (map (\(x,y) -> (updateGen m x, y)) s'))
  in (res, m)
gen2 (ACtrl (IfzP (ALoc v) l b s)) m = let
  [v'] = map (updateGen m) [v]
  s' = map (\(x,y) -> (updateGen m x, y)) s
  res = ACtrl (IfzP (ALoc v') l b s')
  in (res, m)
gen2 (ACtrl (CompP (ALoc v1) (ALoc v2) op l s)) m = let
  [v1', v2'] = map (updateGen m) [v1, v2]
  s' = map (\(x,y) -> (updateGen m x, y)) s
  res = ACtrl (CompP (ALoc v1') (ALoc v2') op l s')
  in (res, m)
gen2 (ACtrl (CompP (ALoc v1) v2 op l s)) m = let
  [v1'] = map (updateGen m) [v1]
  s' = map (\(x,y) -> (updateGen m x, y)) s
  res = ACtrl (CompP (ALoc v1') v2 op l s')
  in (res, m)
gen2 (ACtrl (CompP v1 (ALoc v2) op l s)) m = let
  [v2'] = map (updateGen m) [v2]
  s' = map (\(x,y) -> (updateGen m x, y)) s
  res = ACtrl (CompP v1 (ALoc v2') op l s')
  in (res, m)
gen2 x m = (x,m)

isVar (AVar _) = True
isVar _ = False

updateGen m (AVar i) = let
  gen = case Map.lookup i m of
    Nothing -> 0
    Just g -> g
  in AVarG i gen
updateGen m (Pt (AVar i)) = let
  gen = case Map.lookup i m of
    Nothing -> 0
    Just g -> g
  in (Pt $ AVarG i gen)
updateGen _ x = x

updateGen' m (ALoc (AVar i)) = let
  gen = case Map.lookup i m of
    Nothing -> 0
    Just g -> g
  in ALoc (AVarG i gen)
updateGen' m (ALoc (Pt (AVar i))) = let
  gen = case Map.lookup i m of
    Nothing -> 0
    Just g -> g
  in ALoc $ Pt $ AVarG i gen
updateGen' _ x = x

--build blockX calls blockY with params Set.Set AVal
-- builds Map of Block String of Label -> Block String of Code -> Params from Code
--

type GMap = Map.Map String [(Set.Set ALoc, String)]
type LMap = Map.Map String (Set.Set ALoc)

gotosMap :: Blocks -> GMap -> GMap
gotosMap b m =
  let
    m' = map (\(x,(y,z)) -> gotosMap' z x m) b
    m'' = foldl (\x -> \y -> Map.unionWith(\v1 -> \v2 -> v1 ++ v2) x y) Map.empty m'
  in
   --trace "GotoMap:\n" $ 
   --trace (foldl (++) "" (map(\x -> (show x)++"\n") $ zip (Map.keys m'') (Map.elems m''))) $
   --trace "------------\n" $
   m''

gotosMap' :: [AAsm] -> String -> GMap -> GMap
gotosMap' aasm l m =
  if (length aasm) == 0 then m
  else case head aasm of
    (ACtrl(GotoP s set)) ->
      let
        m' = Map.alter(\x -> case x of
                          Just x' -> Just ((Set.fromList $ map fst set,l) : x')
                          Nothing -> Just [(Set.fromList $ map fst set,l)]) s m
      in
       gotosMap' (tail aasm) l m'
    (ACtrl(IfzP _ s _ set)) ->
      let
        m' = Map.alter(\x -> case x of
                          Just x' -> Just ((Set.fromList $ map fst set,l) : x')
                          Nothing -> Just [(Set.fromList $ map fst set,l)]) s m
      in
       gotosMap' (tail aasm) l m'
    (ACtrl(CompP _ _ _ s set)) ->
      let
        m' = Map.alter(\x -> case x of
                          Just x' -> Just ((Set.fromList $ map fst set,l) : x')
                          Nothing -> Just [(Set.fromList $ map fst set,l)]) s m
      in
       gotosMap' (tail aasm) l m'
    _ -> gotosMap' (tail aasm) l m

labelsMap :: Blocks -> LMap
labelsMap b = let b' = map(\(x,(y,z)) -> (x,y)) b
              in Map.fromList b'

--minimize - Minimize the SSA
minimize blocks =
  let gotoMap = gotosMap blocks Map.empty
      lblmap = labelsMap blocks
      lbls = (Map.keys gotoMap) List.\\ ["mem"]
      varMap = Map.unions $ map(\x -> let g = gotoMap Map.! x
                                          g' = map(\(x,y) -> x) g
                                          l = lblmap Map.! x 
                                      in if length(g') == 1 then createVarMap l (head g')
                                         else Map.empty) lbls 
      blocks' = cmpLbls lbls gotoMap lblmap blocks varMap
      b = map(\(x,(y,z)) -> case Map.lookup x lblmap of
                 Just y' -> (x,(y',z))
                 Nothing -> (x,(y,z))) blocks'
  in
   --trace (show lbls) $ 
   --trace (foldl (++) "" (map (\(x,(y,z)) -> "1: "++(show x)++" - "++(show y)++"\n"
   --                                              ++(foldl (++) "" (map (\a->"1: "++(show a)++"\n") z))
   --                                              ++"\n") b)) $
   blocks'

--cmpLbls - compares gotos to block labels and tries to reduce the number of variables
-- that are passed from goto to label
-- This is the <3 of the minimization 
cmpLbls :: [String] -> GMap -> LMap -> Blocks -> Map.Map ALoc ALoc -> Blocks 
cmpLbls lbls g l b vm =
  if length lbls == 0
  then b
  else
    let lbl = head lbls
        gotos = g Map.! lbl -- [(goto vars, label of block goto is in)]
        gvars = map(\(x,y) -> x) gotos
        lvars = l Map.! lbl
        (bool, g', l', b') = cmpSets gotos lvars b vm
    in
     if bool
     then let
       Just (_,aasm) = List.lookup lbl b'
       varmap = createVarMap lvars g'
       (aasm',lbls') = --trace ((show lbl)++"\n"++(show vm)++"\n--------\n") $
         updateVars aasm vm lbls 
       l'' = Map.adjust (\v -> l') lbl l
       ylbl = l'' Map.! lbl
       b'' = map(\(x,(y,z)) -> if x == lbl then (x,(ylbl,aasm')) else (x,(y,z))) b'
       g'' = Map.adjust (\v -> map(\(x,s)-> (x Set.\\ g', s)) v) lbl g
       in
        cmpLbls (tail lbls') g'' l'' b'' vm
     else
       cmpLbls (tail lbls) g l b vm
      
cmpSets :: [(Set.Set ALoc, String)] -> Set.Set ALoc -> Blocks -> Map.Map ALoc ALoc
           -> (Bool, Set.Set ALoc, Set.Set ALoc, Blocks)
cmpSets g l b vm =
  let (gvars, glbls) = unzip g
  in
   if length(g) == 1 then
     let l' = (Set.map(\x->case Map.lookup x vm of
                         Just x' -> x'
                         Nothing -> x) l) --Set.\\ (head gvars)
         l'' = Set.filter (\x-> Set.member x (head gvars)) l'
     in
      (True, head gvars, l'', b) -- removing params, set of params to remove, new lbl params, new blocks
   else
     (False, head gvars, l, b) 

createVarMap s1 s2 =
  let l1 = filter (\x -> case x of {AVarG _ _ -> True; _ -> False}) $ Set.toAscList s1
      l2 = filter (\x -> case x of {AVarG _ _ -> True; _ -> False}) $ Set.toAscList s2
  in
   if length(l1) /= length (l2)
   then trace (":( what do i do now?\n" ++ (show l1)++"\n"++(show l2)) $ (Map.empty) Map.! 0
   else
     let l = map(\(AVarG st1 _, AVarG st2 _) -> if (st1 == st2) then True else False) $ zip l1 l2
     in
      if any(\x -> not x) l
      then  trace ("Things not == :(\n" ++ (show l1)++"\n"++(show l2)) $ (Map.empty) Map.! 0
      else Map.fromList $ zip l1 l2

updateVars aasm varmap l =
  if length(aasm) == 0 then (aasm,l)
  else
    let
      aasm' = map (\x -> updateVars' x varmap l) aasm
      aasm'' = map(\(x,y)->x)aasm'
      l' = last (map(\(x,y)->y)aasm')
    in
     --trace (foldl (++) "" (map (\x -> "0: "++(show x)++"\n") aasm)) $ 
     --trace (foldl (++) "" (map (\x -> "1: "++(show x)++"\n") aasm')) $
     --trace "--------------" $
     (aasm'',l')

updateVars'(AAsm {aAssign = alocs, aOp = o, aArgs = args}) vm l = 
  let
    alocs' = map(\x -> case Map.lookup x vm of
                    Just v' -> --trace ("AAsm - alocs: "++(show x)++" -> "++(show v')) $
                      v'
                    Nothing -> x) alocs
    args' = map(\x -> case x of
                   AImm i -> AImm i
                   ALoc v -> case Map.lookup v vm of
                     Just v' -> --trace ("AAsm - avars: "++(show v)++" -> "++(show v')) $
                       ALoc v'
                     Nothing -> ALoc v) args
  in
   (AAsm {aAssign=alocs', aOp=o, aArgs=args'}, l)
updateVars'(ACtrl(Ret(ALoc v))) vm l = --trace ("\tRet:"++(show vm)) $
  case Map.lookup v vm of
    Just v' -> (ACtrl(Ret(ALoc v')),l)
    Nothing -> (ACtrl(Ret(ALoc v)),l)
updateVars'(ACtrl(IfzP(ALoc v) s b set)) vm l =
  let
    set' = map (\(a,av) -> case Map.lookup a vm of
                   Just a' -> (a', Just (ALoc a'))
                   Nothing -> (a,av)) set
  in
   case Map.lookup v vm of
     Just v' -> (ACtrl (IfzP(ALoc v') s b set'),l++[s])
     Nothing -> (ACtrl (IfzP(ALoc v) s b set'),l++[s])
updateVars'(ACtrl(CompP e1 e2 op s set)) vm l =
  let
    set' = map (\(a,av) -> case Map.lookup a vm of
                   Just a' -> (a', Just (ALoc a'))
                   Nothing -> (a,av)) set
  in
   case (e1, e2) of
     (ALoc v1, ALoc v2) ->
       case (Map.lookup v1 vm, Map.lookup v2 vm) of
         (Just v1', Just v2') -> (ACtrl (CompP (ALoc v1') (ALoc v2') op s set'),l++[s])
         (Just v1', Nothing) -> (ACtrl (CompP (ALoc v1') (ALoc v2) op s set'),l++[s])
         (Nothing, Just v2') -> (ACtrl (CompP (ALoc v1) (ALoc v2') op s set'),l++[s])
         (Nothing, Nothing) -> (ACtrl (CompP (ALoc v1) (ALoc v2) op s set'),l++[s])
     (ALoc v1, _) ->
       case Map.lookup v1 vm of
         (Just v1') -> (ACtrl (CompP (ALoc v1') e2 op s set'),l++[s])
         Nothing -> (ACtrl (CompP (ALoc v1) e2 op s set'),l++[s])
     (_, ALoc v2) ->
       case Map.lookup v2 vm of
         (Just v2') -> (ACtrl (CompP e1 (ALoc v2') op s set'),l++[s])
         Nothing -> (ACtrl (CompP e1 (ALoc v2) op s set'),l++[s])
     _ -> (ACtrl (CompP e1 e2 op s set'),l++[s])
updateVars'(APush v) vm l = --trace "APush" $
  case Map.lookup v vm of
    Just v' -> (APush v',l)
    Nothing -> (APush v,l)
updateVars'(APop v) vm l = --trace "APop" $
  case Map.lookup v vm of
    Just v' -> (APop v',l)
    Nothing -> (APush v,l)
updateVars'(ACtrl(GotoP s set)) vm l =
  let
    set' = map (\(v,av) -> case Map.lookup v vm of
                   Just v' -> (v', Just (ALoc v'))
                   Nothing -> (v,av)) set
  in
   (ACtrl(GotoP s set'), l ++ [s])
updateVars' v _ l= (v,l)

{-
type Lblmap = Map.Map String [(String, Set.Set ALoc)]
  
mapBlocks :: Blocks -> Lblmap
mapBlocks blocks = Map.fromList $ zipmap $ grpby $ concat (map (\(lbl,(vals,aasm)) -> (map (\x -> f(lbl,x)) aasm)) blocks)
  where grpby l = List.groupBy (\(x,y)-> \(a,b)-> x==a) $ List.filter (\(x,y)-> x=="") l
        zipmap l = zip (map (\x -> fst (head x)) l) (map (\x -> map (snd) x) l)
        f (lbl, (ACtrl(IfzP aval goto _ s))) = (lbl, (goto, s)) --possibly flip goto and lbl here
        f (lbl, (ACtrl(GotoP goto s))) = (lbl, (goto, s))
        f (lbl, x) = ("",("",Set.empty)) 
-}
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
        {-
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
                 -}


unGen (AVarG s i) = AVar (s ++ (show i))
unGen (Pt (AVarG s i)) = Pt $ AVar (s ++ (show i))
unGen x = x

-- Turn the SSA code back into non SSA code that gets rid of parameterized labels and gotos
-- Basically, assign label vals with goto vals before goto
deSSA :: Blocks -> [AAsm]
deSSA blocks = let bmap = Map.fromList blocks
               in concat $ map (\(lbl,(vals,aasm)) -> [ACtrl(Lbl lbl)] ++ (concat $ map (\x -> f bmap x) aasm)) blocks
  where f bmap (ACtrl(GotoP goto valList)) = let
          (gvals, _) = if goto == "mem" then (Set.empty,[]) else bmap Map.! goto
          assigns = concat $ Set.toList $ Set.map
                    (\x -> let
                        var = case x of
                          (AVarG s _) -> s
                        in case List.find (\(key, _) -> case key of
                                              (AVarG s' _) -> var == s'
                                              _ -> False) valList of
                             (Just (y, p)) -> case p of
                               Just (ALoc v) -> [AAsm [unGen x] Nop [ALoc $ unGen v]]
                               Just const -> [AAsm [unGen x] Nop [const]]
                               Nothing -> [AAsm [unGen x] Nop [ALoc $ unGen y]]
                             Nothing -> []) gvals
          in assigns ++ [ACtrl $ Goto goto]
        f bmap (ACtrl(IfzP val goto b valList)) = let
          (gvals, _) = if goto == "mem" then (Set.empty,[]) else bmap Map.! goto
          assigns = concat $ Set.toList $ Set.map
                    (\x -> let
                        var = case x of
                          (AVarG s _) -> s
                        in case List.find (\(key, _) -> case key of
                                              (AVarG s' _) -> var == s'
                                              _ -> False) valList of
                             (Just (y, p)) -> case p of
                               Just (ALoc v) -> [AAsm [unGen x] Nop [ALoc $ unGen v]]
                               Just const -> [AAsm [unGen x] Nop [const]]
                               Nothing -> [AAsm [unGen x] Nop [ALoc $ unGen y]]
                             Nothing -> []) gvals
          stmt = case val of
            ALoc(AVarG s i) -> ACtrl(Ifz(ALoc(AVar (s ++ (show i)))) goto b)
            t -> ACtrl(Ifz t goto b)
          in assigns ++ [stmt]
        f bmap (ACtrl(CompP val1 val2 op goto valList)) = let
          (gvals, _) = if goto == "mem" then (Set.empty,[]) else bmap Map.! goto
          assigns = concat $ Set.toList $ Set.map
                    (\x -> let
                        var = case x of
                          (AVarG s _) -> s
                        in case List.find (\(key, _) -> case key of
                                              (AVarG s' _) -> var == s'
                                              _ -> False) valList of
                             (Just (y, p)) -> case p of
                               Just (ALoc v) -> [AAsm [unGen x] Nop [ALoc $ unGen v]]
                               Just const -> [AAsm [unGen x] Nop [const]]
                               Nothing -> [AAsm [unGen x] Nop [ALoc $ unGen y]]
                             Nothing -> []) gvals
          stmt = case (val1, val2) of
            (ALoc(AVarG s1 i1), ALoc (AVarG s2 i2)) ->
              ACtrl $ Comp (ALoc (AVar (s1 ++ (show i1)))) (ALoc (AVar (s2 ++ (show i2)))) op goto
            (ALoc(AVarG s1 i1), _) ->
              ACtrl $ Comp (ALoc (AVar (s1 ++ (show i1)))) val2 op goto
            (_, ALoc (AVarG s2 i2)) ->
              ACtrl $ Comp  val1 (ALoc (AVar (s2 ++ (show i2)))) op goto
            _ ->
              ACtrl $ Comp val1 val2 op goto
          in assigns ++ [stmt]
        f bmap (ACtrl(Ret(ALoc(AVarG s i)))) = [ACtrl(Ret(ALoc(AVar (s ++ (show i)))))]
        f bmap AAsm{aAssign=locs, aOp = o, aArgs = vals} =
          let locs' = map (\x -> case x of
                              AVarG s i -> AVar (s ++ (show i))
                              Pt (AVarG s i) -> Pt $ AVar (s ++ (show i))
                              a -> a
                          ) locs
              vals' = map (\(x) -> case x of
                              ALoc(AVarG s i) -> ALoc(AVar(s ++ (show i)))
                              ALoc(Pt (AVarG s i)) -> ALoc(Pt $ AVar(s ++ (show i)))
                              y -> y
                          )vals
          in
           [AAsm {aAssign=locs', aOp = o, aArgs = vals'}]
        f bmap (APush loc) = let
          loc' = case loc of
            AVarG s i -> AVar (s ++ (show i))
            a -> a
          in [APush loc']
        f bmap (APop loc) = let
          loc' = case loc of
            AVarG s i -> AVar (s ++ (show i))
            a -> a
          in [APop loc']
        f bmap aasm = [aasm]
          
          
          --go thru aasm in blocks and assign lbl vals with goto vals and change vals to AVar "x#"
          
