{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.PST where

import Control.DeepSeq

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops

data Program = Program [GDecl]
data GDecl = TypeDef Type String SourcePos
           | FDecl Type String [Param] SourcePos
           | FDefn Type String [Param] Block SourcePos
           | SDecl String SourcePos
           | SDefn String (Maybe String) [Param] SourcePos deriving Show
data Param = Param Type String deriving (Show, Eq)
data Block = Block [Stmt] SourcePos 
data Simp = Decl Type String (Maybe Expr) SourcePos
          | Asgn LValue (Maybe Op) Expr SourcePos
          | PostOp Op LValue SourcePos
          | Expr Expr SourcePos
data LValue = LIdent String
            | LArrow LValue String
            | LDot LValue String
            | LDeref LValue
            | LArray LValue Expr -- deriving Show
data Stmt = Simp Simp SourcePos
          | Ctrl Ctrl SourcePos
          | BlockStmt Block SourcePos
data Ctrl = If Expr Stmt (Maybe Stmt) SourcePos
          | While Expr Stmt SourcePos
          | For (Maybe Simp) Expr (Maybe Simp) Stmt SourcePos
          | Return (Maybe Expr) SourcePos
          | Assert Expr SourcePos
data Expr = TempLoc Int 
          | ExpInt IntT Integer SourcePos            
          | TrueT SourcePos
          | FalseT SourcePos
          | Ident String SourcePos
          | Null SourcePos
          | ExpUnOp Op Expr SourcePos
          | ExpBinOp Op Expr Expr SourcePos
          | ExpTernOp Expr Expr Expr SourcePos
          | App String [Expr] SourcePos
          | Alloc Type SourcePos
          | AllocArray Type Expr SourcePos
          | Subscr Expr Expr SourcePos deriving (Eq,Ord)
data IntT = Hex | Dec deriving (Show,Eq,Ord)

instance Show Program where
  show (Program b) = "Program\n" ++ (show b)
  
instance Show Block where
  show (Block stmts _) = foldr (\x -> \y ->  "\n\t" ++ (show x) ++ y) "" stmts
  
instance Show Simp where
  show (Decl t s e _) = "(Decl " ++ (show t) ++ " " ++ s ++ " " ++ (show e) ++ ")"
  show (Asgn l op e _) = "(Asgn " ++ (show l) ++ " " ++ (show op) ++ " " ++ (show e) ++ ")"
  show (PostOp op l _) = "(PostOp " ++ (show op) ++ " " ++ (show l) ++ ")"
  show (Expr e _) = "(Expr " ++ (show e) ++ ")"

instance Show Stmt where
  show (Simp s _) = "(Simp " ++ (show s) ++ ")"
  show (Ctrl c _) = "(Ctrl " ++ (show c) ++ ")"
  show (BlockStmt b _) = "\n\n\t(BlockStmt " ++ (show b) ++ ")\n\n\t"

instance Show LValue where
  show (LIdent s) = "(LIdent " ++ (show s) ++ ")"
  show (LArrow l s) = "(LArrow " ++ (show l) ++ " " ++ (show s) ++ ")"
  show (LDot l s) = "(LDot " ++ (show l) ++ " " ++ (show s) ++ ")"
  show (LDeref l) = "(LDeref " ++ (show l) ++ ")"
  show (LArray l e) = "(LArray " ++ (show l) ++ " " ++ (show e) ++ ")"

instance Show Expr where
  show (ExpInt _ i _) = "(ExpInt " ++ (show i) ++ ")"
  show (TrueT _) = "true"
  show (FalseT _) = "false"
  show (Ident s _) = "(Ident " ++ s ++ ")"
  show (Null _) = "(NULL)"
  show (ExpUnOp op e _) = "(ExpUnOp " ++ (show op) ++ " " ++ (show e) ++ ")"
  show (ExpBinOp op e1 e2 _) = "(ExpBinOp " ++ (show op) ++ " " ++ (show e1) ++ " " ++ (show e2) ++ ")"
  show (ExpTernOp e1 e2 e3 _) = "(ExpTernOp " ++ (show e1) ++ " " ++ (show e2) ++ " " ++ (show e3) ++ ")"
  show (App f a _) = "(App " ++ f ++ " " ++ (show a) ++ ")"
  show (Alloc t _) = "(Alloc " ++ (show t) ++ ")"
  show (AllocArray t e _) = "(AllocArray " ++ (show t) ++ " " ++ (show e) ++ ")"
  show (Subscr e1 e2 _) = "(Subscr " ++ (show e1) ++ " " ++ (show e2) ++ ")"
  
instance Show Ctrl where
  show (Return e _) = "(Return " ++ (show e) ++ ")"
  show (If e s1 s2 _) = "(If " ++ (show e) ++ " " ++ (show s1) ++ " " ++ (show s2) ++ ")"
  show (While e s _) = "(While " ++ (show e) ++ " " ++ (show s) ++ ")"
  show (For s1 e s2 s3 _) = "(For " ++ (show s1) ++ " " ++ (show e) ++ " " ++ (show s2) ++ " " ++ (show s3) ++ ")"
  show (Assert e _) = "(Assert " ++ (show e) ++ ")"

instance NFData Expr where
  rnf (ExpInt intt i sp) = intt `seq` i `seq` sp `seq` ()
  rnf (TrueT sp) = sp `seq` ()
  rnf (FalseT sp) = sp `seq` ()
  rnf (Ident s sp) = s `seq` sp `seq` ()
  rnf (ExpUnOp o e sp) = o `seq` e `seq` sp `seq` ()
  rnf (ExpBinOp o e1 e2 sp) = o `seq` e1 `seq` e2 `seq` sp `seq` ()
  rnf (ExpTernOp e1 e2 e3 sp) = e1 `seq` e2 `seq` e3 `seq` sp `seq` ()
