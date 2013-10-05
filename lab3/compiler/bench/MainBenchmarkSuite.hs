module Main (main) where

import System.FilePath
import System.Process
import System.Exit
  
import Control.Monad.Error

import Criterion.Main
import Criterion.Config

import Compile
import Args
import System.Environment
import System.IO
import System.IO.Unsafe

import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.ParserCombinators.Parsec.Pos
  
import Compile.Types
import Compile.Parse
import Compile.CheckAST
import Compile.CodeGen
import Compile.Elaborate
import Compile.SSA
import Compile.RegAlloc
import qualified Compile.Cgc as Cgc
  
import LiftIOE
import Debug.Trace


getDefaults "c0c" = defaultJob
getDefaults "l3c" = defaultJob {jobOutFormat = Asm}
getDefaults _ = defaultJob

createTests :: String -> (String,Program,S,[Stmt], [AAsm], Blocks, [AAsm], Map.Map AVal Arg,
                          Map.Map Int (Set.Set AVal), Set.Set Cgc.Edge, Set.Set Cgc.Vertex, Cgc.Graph)
createTests str =
  let ast1 = do ast <- runErrorT $ parseAST "../../lab2/tests1/zirconium-return-large-live.l2"
                case ast of
                  Left err -> return (Program (Block [] $ newPos "*.l2" 0 0))
                  Right p -> return p
      ast1' = unsafePerformIO ast1
      elab = let e = elaborate ast1' in case e of {Right s -> s; Left s -> ANup}
      stmts = case ast1' of Program (Block s _) -> s
      (aasm, _, _) = genStmt ([], 0, 0) stmts
      s = ssa aasm
      unssa = deSSA s
      live = liveVars unssa
      (res, vars) = genInter unssa live
      graph = Cgc.buildGraph (Set.toList vars) (Set.toList res)
      regMap = Cgc.coloring graph
  in
   (str, ast1', elab, stmts, aasm, s, unssa, regMap, live, res, vars, graph)
                       

main :: IO ()
main = defaultMainWith benchConfig (return ()) benchmarks
  
benchmarks :: [Benchmark]
benchmarks =
  let tests = ["../tests/test.l3"]
      tests' = map (\x -> createTests x) tests
      --(str1, ast1, elab1) = createTest "../../lab2/tests1/zirconium-return-large-live.l2"
      --(str2, ast2, elab2) = createTest "../../lab2/tests1/osmium-many-blocks.l2"
      --(str3, ast3, elab3) = createTest "../../lab2/tests1/radium-return03.l2"
      --(str4, ast4, elab4) = createTest "../../lab2/tests3/titanium-return04.l2"
  in
   map (\(str, ast, elab, stmts, aasm, s, unssa, regMap, live, res, vars, graph) -> 
         bgroup str
         [
           bench "parse" $ whnf parseAST str,
           bench "elaborate" $ nf elaborate ast,
           bench "checkAST" $ nf checkAST elab,
           bench "genStmt" $ nf (genStmt ([], 0, 0)) stmts,
           bench "ssa" $ nf ssa aasm,
           bench "unssa" $ nf deSSA s,
           bench "liveVars" $ nf liveVars unssa,
           bench "genInter" $ nf (genInter unssa) live,
           bench "Cgc.buildGraph" $ whnf (Cgc.buildGraph (Set.toList vars)) (Set.toList res),
           --bench "Cgc.coloring" $ whnf Cgc.coloring graph,
           bench "translate" $ nf (concatMap (translate regMap)) unssa
         ]
       ) tests'
   
benchConfig :: Config
benchConfig = defaultConfig {
  cfgPerformGC = ljust True,
  cfgSamples = ljust 50,
  cfgVerbosity = ljust Verbose
  }



{-ast1 = do ast <- runErrorT $ parseAST "../../lab2/tests1/zirconium-return-large-live.l2"
                case ast of
                  Left err -> return (Program (Block [] $ newPos "*.l2" 0 0))
                  Right p -> return p
      ast2 = do ast <- runErrorT $ parseAST "../../lab2/tests1/osmium-many-blocks.l2"
                case ast of
                  Left err -> return (Program (Block [] $ newPos "*.l2" 0 0))
                  Right p -> return p
      ast1' = unsafePerformIO ast1
      ast2' = unsafePerformIO ast2
      elab1 = let e = elaborate ast1' in case e of {Right s -> s; Left s -> ANup}
      elab2 = let e = elaborate ast2' in case e of {Right s -> s; Left s -> ANup}
      -}
