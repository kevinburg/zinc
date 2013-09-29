module Compile.RegAlloc where

import Compile.Types
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Compile.Cgc as Cgc

import Debug.Trace

-- Evaluates to a map of the form ALoc -> Register
allocateRegisters aasm =
  let
    live = liveVars aasm
    -- (res, vars) = genInter aasm
    -- regMap = genRegMap res vars
  in trace (show live) Map.empty

{- Evaluates to a mapping of line number to live variables at that line. The last line in the program
   is line 0 because that makes sense. 
-}
liveVars :: [AAsm] -> Map.Map Int (Set.Set AVal)
liveVars aasm = 
    loop Map.empty 
    where loop m = 
            case liveVars' (reverse aasm) 0 (labelLines aasm) Set.empty m True of
              (m', True) -> m'
              (m', False) -> loop m'

{- Computes a mapping of labels to the line numbers that they point to. As above, line numbers
   are in reverse order.
-}
labelLines aasm = labelLines' (reverse aasm) 0 Map.empty

labelLines' [] _ m = m
labelLines' ((ACtrl (Lbl l)) : aasm) i m = let
  m' = Map.insert l i m
  in labelLines' aasm (i+1) m'
labelLines' (_ : aasm) i m = labelLines' aasm (i+1) m

{- Returns the map that is a result of setting m[k] = s. The boolean in the return is set
   to true if the operation changed the map and false otherwise.
-}
update m k s = 
  case Map.lookup k m of
    Nothing -> (Map.insert k s m, True)
    Just s' -> if s == s' then (m, False)
               else (Map.insert k s m, True)

liveVars' :: [AAsm] -> Int -> Map.Map String Int -> Set.Set AVal ->
             Map.Map Int (Set.Set AVal) -> Bool -> (Map.Map Int (Set.Set AVal), Bool)
liveVars' [] _ _ _ m saturate = (m, saturate)
liveVars' (stmt : aasm) i labels live m saturate =
  case stmt of
    ACtrl (Ret loc) ->
      let
        live' = case Map.lookup (i-1) m of
          Nothing -> Set.insert loc live
          Just s -> Set.union s (Set.insert loc live)
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    ACtrl (Lbl _) ->
      let
        m' = Map.insert i live m
      in liveVars' aasm (i+1) labels live m' saturate
    ACtrl (Goto l) ->
      let
        line = labels Map.! l
        live' = case Map.lookup line m of
          Nothing -> Set.empty
          Just s -> Set.union s live
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    ACtrl (Ifz v l) ->
      let
        line = labels Map.! l
        live' = case (Map.lookup line m, Map.lookup (i-1) m) of
          (Nothing, Nothing) -> Set.insert v live
          (Just s, Nothing) -> Set.union s (Set.insert v live)
          (Nothing, Just s) -> Set.union s (Set.insert v live)
          (Just s1, Just s2) -> Set.unions [s1, s2, (Set.insert v live)]
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} ->
      let
        srcs' = filter isTemp srcs
        live' = case Map.lookup (i-1) m of
          Nothing -> Set.union live (Set.fromList srcs')
          Just s -> Set.unions [s, live, Set.fromList srcs']
        live'' = Set.delete (ALoc dest) live'
        (m', changed) = update m i live''
      in liveVars' aasm (i+1) labels live'' m' (saturate && not(changed))

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
    ACtrl (Ret loc) ->
      let
        l' = Set.insert loc l
        newInter = Set.map (\x -> (loc, x)) l
        inter' = Set.union inter newInter
      in genInter' aasm l' inter' (Set.insert loc vars)
    AAsm {aAssign = [dest], aOp = Div, aArgs = srcs} ->
      let
        l' = Set.insert (ALoc dest) l
        newInter = Set.map (\x -> (ALoc dest, x)) l
        inter' = Set.union inter newInter
        live = Set.union (Set.fromList (filter isTemp srcs)) l'
        inter'' = Set.union inter' 
                  (Set.fromList [(a,b) | a <- Set.toList live, b <- [ALoc (AReg 0), ALoc (AReg 3)]])
      in genInter' aasm live inter'' (Set.insert (ALoc dest) vars)
    AAsm {aAssign = [dest], aOp = Mod, aArgs = srcs} ->
      let
        l' = Set.insert (ALoc dest) l
        newInter = Set.map (\x -> (ALoc dest, x)) l
        inter' = Set.union inter newInter
        live = Set.union (Set.fromList (filter isTemp srcs)) l'
        inter'' = Set.union inter' 
                  (Set.fromList [(a,b) | a <- Set.toList live, b <- [ALoc (AReg 0), ALoc (AReg 3)]])
      in genInter' aasm live inter'' (Set.insert (ALoc dest) vars)
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
  in m
