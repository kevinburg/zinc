{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Main compiler module; takes a job and compiles it
-}
module Compile
(compile
,Job(..)
,defaultJob
,OF(..)
) where

import System.FilePath
import System.Process
import System.Exit

import Control.Monad.Error

import Compile.Types
import Compile.Parse
import Compile.CheckAST
import Compile.CodeGen
import Compile.Elaborate
import Compile.SSA

import LiftIOE
import Debug.Trace
import qualified Data.Map as Map

writer file obj = liftIOE $ writeFile file $ show obj

sourceWriter file obj = let
  funs = Map.foldWithKey (\fun -> \asm -> \acc ->
                          let
                            body = foldr (\x -> \y -> (show x) ++ "\n" ++ y) "" asm
                          in "\t.globl _c0_" ++ fun ++ "\n_c0_" ++ fun ++ ":\n" ++
                             body ++ "\n" ++ acc) "" obj
  in liftIOE $ writeFile file $  funs

compile :: Job -> IO ()
compile job = do
  res <- runErrorT $ do
    ast <- parseAST $ jobSource job
    (elab, ast') <- liftEIO $ elaborate ast
    smap <- liftEIO $ checkAST elab
    if jobOutFormat job == C0
      then writer (jobOut job) ast
      else let asm = codeGen (ast', smap) in
             if jobOutFormat job == Asm
                then sourceWriter (jobOut job) asm
                else do writer asmFile ast
                        let o = if jobOutFormat job == Obj then "-c" else ""
                        gcc o asmFile (jobOut job)
  case res of
    Left msg -> error msg
    Right () -> return ()
  where asmFile = replaceExtension (jobOut job) "s"

gcc :: String -> FilePath -> FilePath -> ErrorT String IO ()
gcc args input output = exitErrorCode $ readProcessWithExitCode
  "gcc"
  [args, input, "-o", output]
  ""
  where exitErrorCode :: IO (ExitCode, String, String) -> ErrorT String IO ()
        exitErrorCode m = do
          (exitCode, _, msg) <- lift m
          case exitCode of
            ExitSuccess   -> return ()
            ExitFailure n -> throwError $ "Error " ++ (show n) ++ "\n" ++ msg
