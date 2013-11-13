module Compile.Cgc where

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Heap as PQ

import Compile.Types

import Debug.Trace

type Vertex = ALoc
type Edge = (Vertex, Vertex)
type Graph = Map.Map Vertex [Vertex]

buildGraph :: [Vertex] -> [Edge] -> Graph
buildGraph v e = 
  let
    m = foldr (\v -> \acc -> Map.insert v [] acc) Map.empty v
  in foldr (\(x,y) -> \acc -> Map.adjust (List.union [y]) x 
                              (Map.adjust (List.union [x]) y acc)) m e

-- nghbr : Given a graph and a vertex, return a list of the neighboring vertices
nghbr :: Graph -> Vertex -> [Vertex]
nghbr g v = g Map.! v
            --in if Mb.isJust l then Mb.fromJust l else []

isnghbr :: Graph -> Vertex -> Vertex -> Bool
isnghbr g v1 v2 = v2 `elem` (nghbr g v1)

-- Simplicial Elimination Ordering
seo :: Graph -> [Vertex]
seo g = let verts = Map.keys g
            weights = PQ.fromAscList (map (\x -> (0,x)) verts) 
        in
          List.reverse (seo' g weights [])

seo' :: Graph -> PQ.MaxHeap (Int, Vertex) -> [Vertex] -> [Vertex]
seo' g weights l =
  case PQ.view weights of
    Nothing -> l
    Just ((_, v), weights') ->
      let
        (left, right) = PQ.partition (\(_, v') -> isnghbr g v v') weights'
        left' = PQ.fromList (map (\(prio, val) -> (prio + 1, val)) (PQ.toList left))
        w = PQ.union left' right
     in seo' g w (v : l)

-- Greedy coloring algorithm, takes a graph, outputs a list of tuples
-- Vertex paired with Int, which represents color
coloring :: Graph -> (Map.Map Vertex Arg, Int)
coloring g = let size = Map.size g
                 bound = 10000
                 m = Map.map (\x-> -1) g
                 preColoring = [(ARes, 0)] ++
                               [(AReg EAX, 0), (AReg EDI, 1), (AReg ESI, 2),
                                (AReg EDX, 3), (AReg ECX, 4), (AReg R8D, 5),
                                (AReg R9D, 6), (AReg R10D, 7), (AReg R11D, 8)] ++
                               [(AArg i, i+1) | i <- [0..5]]
                 m' = case size > bound of
                   False -> foldr (\(x,y) -> \acc -> Map.insert x y acc) m preColoring
                   True -> foldr (\(x,y) -> \acc -> Map.insert x y acc) (Map.empty) preColoring
                 s = List.filter (\r -> case r of
                                     (AReg _) -> False
                                     ARes -> False
                                     (AArg _) -> True
                                     _ -> True) (seo g)
                 res = case size > bound of
                   False -> color g m' s
                   True -> let
                     (m'',_) = Map.foldWithKey (\key -> \_ -> \(m,i) ->
                                                 case key of
                                                   AArg i | i > 5 ->
                                                     (Map.insert key (-(i-5)) m, i+1)
                                                   _ ->
                                                     (Map.insert key i m, i+1)) (Map.empty,11) g
                     in Map.union m' m''
                 regsUsed = List.maximum (Map.elems res)
                 order = registerOrder ()
             in (Map.map (\v -> 
                            case v < 0 of
                              True -> Reg (SpillArg (-v))
                              False ->
                                case (v < (length(order)-1)) of
                                  True ->
                                    let Just reg = lookup v order
                                    in Reg reg
                                  False ->
                                    let offset = (v - length(order) + 1)
                                    in Stk (offset*8)
                          ) res, max 0 (regsUsed - 8))

color :: Graph -> Map.Map Vertex Int -> [Vertex] -> Map.Map Vertex Int
color g m [] = m
color g m s =  let
  v = List.head s in
  case v of
    AArg i | i > 5 -> let
      n' = (-(i-5))
      m' = Map.insert v n' m
      in color g m' (tail s)
    AArg i -> let
      n' = i+1
      m' = Map.insert v n' m
      in color g m' (tail s)
    _ -> let
      n = nghbr g v
      n' = List.map (\x -> m Map.! x) n
      m' = Map.insert v (mex n') m
      in color g m' (tail s)
    
--Finds the Minimally Excluded Element of a list
mex :: [ Int ] -> Int
mex [] = 0
mex l = let 
  l' = [0..((List.maximum l)+2)]
  l'' = l' List.\\ l
  m = if length l'' == 0 then 0 else List.minimum(l'')
  in m

-- Orders the registers in the order we want to use them (ESP, EBP for stack)
registerOrder () =
  zip [0..] $ [EAX,EDI,ESI,EDX,ECX,R8D,R9D,R10D,R11D,EBX,R12D,R13D]
  -- preference toward caller save registers
