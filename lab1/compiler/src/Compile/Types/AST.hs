{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops

data AST = Block [Decl] [Stmt] SourcePos
data Decl = Decl {declName :: String, declPos :: SourcePos}
          | DeclAsgn {declName :: String, declPos :: SourcePos, bindVal :: Expr}
data Stmt = Asgn String AsgnOp Expr SourcePos 
          | Return Expr SourcePos
data Expr = ExpInt Integer SourcePos
          | Ident String SourcePos
          | ExpBinOp Op Expr Expr SourcePos
          | ExpUnOp Op Expr SourcePos
type AsgnOp = Maybe Op


-- Note to the student: You will probably want to write a new pretty printer
-- using the module Text.PrettyPrint.HughesPJ from the pretty package
-- This is a quick and dirty pretty printer.
-- Once that is written, you may find it helpful for debugging to switch
-- back to the deriving Show instances.

instance Show AST where
  show (Block decls stmts _) =
    "Block\n" ++
    "  [Decl]\n" ++    
    (unlines (map (\x -> "    " ++ show x) decls)) ++
    "  [Stmt]\n" ++
    (unlines (map (\x -> "    " ++ show x) stmts))

instance Show Decl where
  show (Decl i _) = "Decl " ++ i ++ " _"
  show (DeclAsgn i _ e) = "DeclAsgn " ++ i ++ " (" ++ (show e) ++ ") _"

instance Show Stmt where
  show (Return e _) = "Return " ++ "(" ++ (show e) ++ ") _"
  show (Asgn i op e _) = "Asgn " ++ i ++ " " ++ (mShow op) ++ "=" ++ " "
                         ++ "(" ++ (show e) ++ ") _"

instance Show Expr where
  show (ExpInt n _) = "ExpInt " ++ show n ++ " _"
  show (ExpBinOp op e1 e2 _) = "ExpBinOp " ++ (show op) ++ "(" ++ (show e1)
                               ++ ") (" ++ (show e2) ++ ") _"
  show (Ident i _) = "Ident " ++ i ++ " _"
  show (ExpUnOp op e _) = "ExpUnOp " ++ (show op) ++ "(" ++ (show e) ++ ") _"
  
mShow Nothing = ""
mShow (Just x) = show x
