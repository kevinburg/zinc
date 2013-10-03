module Compile.Cgc where

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Heap as PQ

import Compile.Types

import Debug.Trace

type Vertex = AVal
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
coloring :: Graph -> Map.Map Vertex Arg
coloring g = let m = Map.map (\x-> -1) g
                 m' = Map.insert (ALoc $ AReg 0) 0
                      (Map.insert (ALoc $ AReg 2) 2
                       (Map.insert (ALoc $ AReg 3) 3 m))
                 s = List.filter (\r -> case r of
                                     ALoc (AReg _) -> False
                                     _ -> True) (seo g)
                 res = color g m' s
                 order = registerOrder ()
             in  (Map.map (\v -> 
                            case (v < (Map.size(order)-1)) of
                              True ->
                                let Just reg = Map.lookup v order
                                in Reg reg
                              False ->
                                let offset = (v - Map.size(order) + 2)
                                in Stk (-(offset*4))
                          ) res)

color :: Graph -> Map.Map Vertex Int -> [Vertex] -> Map.Map Vertex Int
color g m [] = m
color g m s = let n = nghbr g (List.head s)
                  n' = List.map (\x ->  m Map.! x) n
                  m' = Map.insert (List.head s) (mex n') m
              in
               color g m' (tail s)
    
--Finds the Minimally Excluded Element of a list
mex :: [ Int ] -> Int
mex [] = 0
mex l = let m = List.minimum([0..((List.maximum l)+2)] List.\\ l)
        in
         m
         {-
         if m < (Map.size(registerOrder())-1)
         then m
         else Map.size(registerOrder())-1
          -}
-- Orders the registers in the order we want to use them (ESP, EBP for stack)
registerOrder () =
  Map.fromList (zip [0..] [EAX,EBX,ECX,EDX,ESI,EDI,R8D,R9D,R10D,R11D,R12D,R13D,R14D])
