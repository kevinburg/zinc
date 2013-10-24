{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Control.DeepSeq

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.Ops
import Compile.Types.PST

data S = AAssign LValue Expr
       | AIf Expr S S
       | AWhile Expr S
       | AReturn (Maybe Expr)
       | ANup
       | ASeq S S
       | ABlock S S
       | AExpr Expr S
       | AAssert Expr
       | ADeclare String Type S deriving Show

instance NFData S where
  rnf (AAssign str e) = str `seq` e `seq` ()
  rnf (AIf e s1 s2) = e `seq` s1 `seq` s2 `seq` ()
  rnf (AWhile e s) = e `seq` s `seq` ()
  rnf (AReturn e) = e `seq` ()
  rnf (ANup) = ANup `seq` ()
  rnf (ASeq s1 s2) = s1 `seq` s2 `seq` ()
  rnf (ABlock s1 s2) = s1 `seq` s2 `seq` ()
  rnf (AExpr e s) = e `seq` s `seq` ()
  rnf (ADeclare str t s) = str `seq` t `seq` s `seq` ()
  
