{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops

data Program = Program Block
data Block = Block [Stmt] SourcePos
data Type = Int
          | Bool deriving Show
data Simp = Decl Type String (Maybe Expr) SourcePos
          | Asgn String (Maybe Op) Expr SourcePos
          | PostOp String Op SourcePos
          | Expr Expr SourcePos
data Stmt = Simp Simp SourcePos
          | Ctrl Ctrl SourcePos
          | BlockStmt Block SourcePos
data Ctrl = If Expr Stmt (Maybe Stmt) SourcePos
          | While Expr Stmt SourcePos
          | For (Maybe Simp) Expr (Maybe Simp) Stmt SourcePos
          | Return Expr SourcePos
data Expr = ExpInt IntT Integer SourcePos            
          | TrueT SourcePos
          | FalseT SourcePos
          | Ident String SourcePos
          | ExpUnOp Op Expr SourcePos
          | ExpBinOp Op Expr Expr SourcePos
          | ExpTernOp Expr Expr Expr SourcePos
data IntT = Hex | Dec deriving Show

-- Note to the student: You will probably want to write a new pretty printer
-- using the module Text.PrettyPrint.HughesPJ from the pretty package
-- This is a quick and dirty pretty printer.
-- Once that is written, you may find it helpful for debugging to switch
-- back to the deriving Show instances.

instance Show Program where
  show (Program b) = "Program\n" ++ (show b)
  
instance Show Block where
  show (Block stmts _) = foldr (\x -> \y ->  "\n\t" ++ (show x) ++ y) "" stmts
  
instance Show Simp where
  show (Decl t s e _) = "(Decl " ++ (show t) ++ " " ++ s ++ " " ++ (show e) ++ ")"
  show (Asgn s op e _) = "(Asgn " ++ s ++ " " ++ (show op) ++ " " ++ (show e) ++ ")"
  show (PostOp s op _) = "(PostOp " ++ s ++ " " ++ (show op) ++ ")"
  show (Expr e _) = "(Expr " ++ (show e) ++ ")"

instance Show Stmt where
  show (Simp s _) = "(Simp " ++ (show s) ++ ")"
  show (Ctrl c _) = "(Ctrl " ++ (show c) ++ ")"
  show (BlockStmt b _) = "\n\n\t(BlockStmt " ++ (show b) ++ ")\n\n\t"
  
instance Show Expr where
  show (ExpInt _ i _) = "(ExpInt " ++ (show i) ++ ")"
  show (TrueT _) = "true"
  show (FalseT _) = "false"
  show (Ident s _) = "(Ident " ++ s ++ ")"
  
instance Show Ctrl where
  show (Return e _) = "(Return " ++ (show e) ++ ")"
  show (If e s1 s2 _) = "(If " ++ (show e) ++ " " ++ (show s1) ++ " " ++ (show s2) ++ ")"
  show (While e s _) = "(While " ++ (show e) ++ " " ++ (show s) ++ ")"