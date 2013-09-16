{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops

data AST = Block [Stmt] SourcePos
data Stmt = Decl String BindVal SourcePos
          | Asgn String AsgnOp Expr SourcePos 
          | Return Expr SourcePos
data Expr = ExpInt IntT Integer SourcePos
          | Ident String SourcePos
          | ExpBinOp Op Expr Expr SourcePos
          | ExpUnOp Op Expr SourcePos
type AsgnOp = Maybe Op
type BindVal = Maybe Expr
data IntT = Dec | Hex


-- Note to the student: You will probably want to write a new pretty printer
-- using the module Text.PrettyPrint.HughesPJ from the pretty package
-- This is a quick and dirty pretty printer.
-- Once that is written, you may find it helpful for debugging to switch
-- back to the deriving Show instances.

instance Show AST where
  show (Block stmts _) =
    "Block\n" ++
    "  [Stmt]\n" ++
    (unlines (map (\x -> "    " ++ show x) stmts))


instance Show Stmt where
  show (Return e _) = "Return " ++ "(" ++ (show e) ++ ") _"
  show (Asgn  i op e _) = "Asgn " ++ i ++ " " ++ (mShow op) ++ "=" ++ " "
                         ++ "(" ++ (show e) ++ ") _"
  show (Decl i e _) = "Decl " ++ i ++ " = (" ++ (mShow e) ++ ") _"

instance Show Expr where
  show (ExpInt _ n _) = "ExpInt " ++ show n ++ " _"
  show (ExpBinOp op e1 e2 _) = "ExpBinOp " ++ (show op) ++ " (" ++ (show e1)
                               ++ ") (" ++ (show e2) ++ ") _"
  show (Ident s _) = "Ident " ++ s ++ " _"
  show (ExpUnOp op e _) = "ExpUnOp " ++ (show op) ++ " (" ++ (show e) ++ ") _"
  
mShow Nothing = ""
mShow (Just x) = show x
