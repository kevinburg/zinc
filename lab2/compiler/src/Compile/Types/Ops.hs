{- L2 Compiler
   Authors: Kevin Burg <kburg@andrew.cmu.edu>
            John Cole <kburg@andrew.cmu.edu>

   Abstract Assembly operations
-}
module Compile.Types.Ops where

data Op = Mul
        | Add
        | Sub
        | Div
        | Neg
        | Mod
        | BAnd
        | BXor
        | BOr
        | LAnd
        | LOr
        | Shl
        | Shr
        | Nop
        | Eq
        | Neq
        | BNot
        | LNot
        | Incr
        | Decr
        | Lt
        | Leq
        | Gt
        | Geq
          
instance Show Op where
  show Mul = "*"
  show Add = "+"
  show Sub = "-"
  show Div = "/"
  show Neg = "-"
  show Mod = "%"
  show LAnd = "&&"
  show LOr = "||"
  show BAnd = "&"
  show BXor = "^"
  show BOr = "|"
  show Shl = "<<"
  show Shr = ">>"
  show Eq = "=="
  show Neq = "!="
  show BNot = "~"
  show LNot = "!"
  show Incr = "++"
  show Decr = "--"
  show Lt = "<"
  show Leq = "<="
  show Gt = ">"
  show Geq = ">="
  show Nop = "[nop]"
