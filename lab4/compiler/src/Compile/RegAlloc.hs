module Compile.RegAlloc where

import Compile.Types
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Compile.Cgc as Cgc

import Debug.Trace

allocateRegisters :: [AAsm] -> (Map.Map ALoc Arg, Int)
allocateRegisters aasm =
  let
    live = liveVars aasm
    (res, vars) = genInter aasm live
    graph = Cgc.buildGraph (Set.toList vars) (Set.toList res)
    (m,i) = Cgc.coloring graph
  in (m,i)

{- Evaluates to a mapping of line number to live variables at that line. The last line in the program
   is line 0 because that makes sense. 
-}
liveVars :: [AAsm] -> Map.Map Int (Set.Set ALoc)
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

liveVars' :: [AAsm] -> Int -> Map.Map String Int -> Set.Set ALoc ->
             Map.Map Int (Set.Set ALoc) -> Bool -> (Map.Map Int (Set.Set ALoc), Bool)
liveVars' [] _ _ _ m saturate = (m, saturate)
liveVars' (stmt : aasm) i labels live m saturate =
  case stmt of
    APush loc ->
      let
        live' = Set.insert loc live
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    APop loc ->
      let
        live' = Set.delete loc live
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    ACtrl (Ret (ALoc loc)) ->
      let
        live' = Set.insert loc live
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    ACtrl (Lbl _) ->
      let
        m' = Map.insert i live m
      in liveVars' aasm (i+1) labels live m' saturate
    ACtrl (Call _ ts) ->
      let
        live' = Set.union live (Set.fromList $ map (\t -> ATemp t) ts)
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    ACtrl (Goto l) ->
      let
        line = labels Map.! l
        live' = case Map.lookup line m of
          Nothing -> Set.empty
          Just s -> s
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    ACtrl (Ifz (ALoc v) l) ->
      let
        line = labels Map.! l
        live' = case Map.lookup line m of
          Nothing -> Set.insert v live
          Just s -> Set.union (Set.insert v s) live
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} ->
      let
        srcs' = isTemp srcs
        newLive = ptlive dest srcs'
        live' = Set.union (Set.delete dest live) (Set.fromList newLive)
        (m', changed) = update m i live'
      in liveVars' aasm (i+1) labels live' m' (saturate && not(changed))

ptlive (Pt x) srcs = x : (ptlive' srcs)
ptlive _ srcs = ptlive' srcs

ptlive' ((Pt x) : xs) = x : (ptlive' xs)
ptlive' (x : xs) = x : (ptlive' xs)
ptlive' [] = []

isTemp [] = []
isTemp ((ALoc x) : xs) = x : (isTemp xs)
isTemp (_ : xs) = isTemp xs

genInter stmts live = 
  let
    (inter, vars) = genInter' (reverse stmts) 0 live Set.empty Set.empty
  in
    (Set.filter (\(x,y) -> x /= y) inter, vars)
  
genInter' [] _ _ inter vars = (inter, vars)
genInter' (stmt : aasm) i live inter vars =
  case stmt of
    APush loc -> let
      vars' = Set.insert loc vars
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (loc, x)) vs
      inter' = Set.union inter newInter
      in genInter' aasm (i+1) live inter' vars'
    APop loc -> let
      vars' = Set.insert loc vars
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (loc, x)) vs
      inter' = Set.union inter newInter
      in genInter' aasm (i+1) live inter' vars'
    ACtrl (Call f ts) -> let
      ler = [AReg EAX, AReg EDI, AReg ESI, AReg EDX, AReg ECX,
             AReg R8D, AReg R9D, AReg R10D, AReg R11D]
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.fromList [(a,b) | a <- ler, b <- (Set.toList vs)]
      inter' = Set.union inter newInter
      in genInter' aasm (i+1) live inter' vars
    ACtrl (Ret (ALoc loc)) -> let
      vars' = Set.insert loc vars
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (loc, x)) vs
      inter' = Set.union inter newInter
      in genInter' aasm (i+1) live inter' vars'
    ACtrl (Ifz (ALoc v) _) -> let
      vars' = Set.insert v vars
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (v, x)) vs
      inter' = Set.union inter newInter
      in genInter' aasm (i+1) live inter' vars'
    ACtrl _ -> genInter' aasm (i+1) live inter vars
    AAsm {aAssign = [dest], aOp = o, aArgs = srcs} | o == SShl || o == SShr -> let
      srcs' = isTemp srcs
      vars' = Set.insert dest (Set.union vars (Set.fromList $ isTemp srcs))
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (dest, x)) (Set.difference vs (Set.fromList srcs'))
      inter' = Set.union inter newInter
      inter'' = Set.union inter' (Set.fromList [(a, AReg ECX) | a <- (Set.toList vs) ++ [dest]])
      in genInter' aasm (i+1) live inter'' vars'
    AAsm {aAssign = [dest], aOp = o, aArgs = srcs} | o == Div || o == Mod -> let
      srcs' = isTemp srcs
      vars' = Set.insert dest (Set.union vars (Set.fromList $ isTemp srcs))
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (dest, x)) (Set.difference vs (Set.fromList srcs'))
      inter' = Set.union inter newInter
      inter'' = Set.union inter' (Set.fromList [(a, b) | a <- Set.toList vs,
                                                b <- [AReg EAX, AReg EDX]])
      in genInter' aasm (i+1) live inter'' vars'
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} -> let
      srcs' = isTemp srcs
      vars' = Set.insert dest (Set.union vars (Set.fromList $ isTemp srcs))
      vs = case Map.lookup i live of
        Nothing -> Set.empty
        Just s -> s
      newInter = Set.map (\x -> (dest, x)) (Set.difference vs (Set.fromList srcs'))
      inter' = Set.union inter newInter
      in genInter' aasm (i+1) live inter' vars'
