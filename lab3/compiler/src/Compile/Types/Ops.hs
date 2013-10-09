{- L2 Compiler
   Authors: Kevin Burg <kburg@andrew.cmu.edu>
            John Cole <kburg@andrew.cmu.edu>

   Abstract Assembly operations
-}
module Compile.Types.Ops where

data Type = Int 
          | Bool 
          | Void 
          | Type String 
          | Map [Type] Type deriving (Eq, Show)

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
        | SShl
        | SShr
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
        | Fail deriving Eq

opType Mul = ([Int, Int], Int)
opType Add = ([Int, Int], Int)
opType Sub = ([Int, Int], Int)
opType Div = ([Int, Int], Int)
opType Neg = ([Int], Int)
opType Mod = ([Int, Int], Int)
opType BAnd = ([Int, Int], Int)
opType BXor = ([Int, Int], Int)
opType BOr = ([Int, Int], Int)
opType LAnd = ([Bool, Bool], Bool)
opType LOr = ([Bool, Bool], Bool)
opType Shl = ([Int, Int], Int)
opType Shr = ([Int, Int], Int)
opType SShl = ([Int, Int], Int)
opType SShr = ([Int, Int], Int)
opType BNot = ([Int], Int)
opType LNot = ([Bool], Bool)
opType Incr = ([Int], Int)
opType Decr = ([Int], Int)
opType Lt = ([Int, Int], Bool)
opType Leq = ([Int, Int], Bool)
opType Gt = ([Int, Int], Bool)
opType Geq = ([Int, Int], Bool)
             
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
  show SShl = "<<"
  show SShr = ">>"
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
