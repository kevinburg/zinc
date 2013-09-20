{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops
import Compile.Type.PST

data S = Assign String Expr
       | If Expr Stmt Stmt
       | While Expr Stmt
       | Return Expr
       | Nop
       | Seq Stmt Stmt
       | Declare String Type Stmt deriving Show
                                             
