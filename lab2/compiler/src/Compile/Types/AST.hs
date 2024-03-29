{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops
import Compile.Types.PST

-- TODO: add in sourcePos for errors
data S = AAssign String Expr
       | AIf Expr S S
       | AWhile Expr S
       | AReturn Expr
       | ANup
       | ASeq S S
       | ABlock S S
       | AExpr Expr S
       | ADeclare String Type S deriving Show
                                             
