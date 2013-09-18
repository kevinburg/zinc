{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops

data Program = Program Block deriving Show
data Block = Block [Stmt] SourcePos deriving Show
data Type = Int
          | Bool deriving Show
data Simp = Decl Type String (Maybe Expr) SourcePos
          | Asgn String (Maybe Op) Expr SourcePos
          | PostOp String Op SourcePos
          | Expr Expr SourcePos deriving Show
data Stmt = Simp Simp SourcePos
          | Ctrl Ctrl SourcePos
          | BlockStmt Block SourcePos deriving Show
data Ctrl = If Expr Stmt (Maybe Stmt) SourcePos
          | While Expr Stmt SourcePos
          | For (Maybe Simp) Expr (Maybe Simp) Stmt SourcePos
          | Return Expr SourcePos deriving Show
data Expr = ExpInt IntT Integer SourcePos            
          | TrueT SourcePos
          | FalseT SourcePos
          | Ident String SourcePos
          | ExpUnOp Op Expr SourcePos
          | ExpBinOp Op Expr Expr SourcePos
          | ExpTernOp Expr Expr Expr SourcePos deriving Show
data IntT = Hex | Dec deriving Show

-- Note to the student: You will probably want to write a new pretty printer
-- using the module Text.PrettyPrint.HughesPJ from the pretty package
-- This is a quick and dirty pretty printer.
-- Once that is written, you may find it helpful for debugging to switch
-- back to the deriving Show instances.
