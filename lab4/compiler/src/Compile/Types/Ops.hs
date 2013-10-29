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
          | Struct String
          | Pointer Type
          | Array Type
          | Map [Type] Type deriving (Eq, Show)

data Op = Mul
        | Add
        | AddrAdd
        | Sub
        | Div
        | Neg
        | Deref
        | Arrow
        | Dot
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
        | Fail
        | MemMov MovSize deriving (Ord, Eq)

data MovSize = Small | Large deriving (Show, Ord, Eq)

opInt Int = True
opInt _ = False

opBool Bool = True
opBool _ = False

opPointer (Pointer _) = True
opPointer _ = False

opType Mul = ([opInt, opInt], \_ -> Int)
opType Add = ([opInt, opInt], \_ -> Int)
opType Sub = ([opInt, opInt], \_ -> Int)
opType Div = ([opInt, opInt], \_ -> Int)
opType Neg = ([opInt], \_ -> Int)
opType Mod = ([opInt, opInt], \_ -> Int)
opType BAnd = ([opInt, opInt], \_ -> Int)
opType BXor = ([opInt, opInt], \_ -> Int)
opType BOr = ([opInt, opInt], \_ -> Int)
opType LAnd = ([opBool, opBool], \_ -> Bool)
opType LOr = ([opBool, opBool], \_ -> Bool)
opType Shl = ([opInt, opInt], \_ -> Int)
opType Shr = ([opInt, opInt], \_ -> Int)
opType SShl = ([opInt, opInt], \_ -> Int)
opType SShr = ([opInt, opInt], \_ -> Int)
opType BNot = ([opInt], \_ -> Int)
opType LNot = ([opBool], \_ -> Bool)
opType Incr = ([opInt], \_ -> Int)
opType Decr = ([opInt], \_ -> Int)
opType Lt = ([opInt, opInt], \_ -> Bool)
opType Leq = ([opInt, opInt], \_ -> Bool)
opType Gt = ([opInt, opInt], \_ -> Bool)
opType Geq = ([opInt, opInt], \_ -> Bool)
opType Deref = ([opPointer], \(Pointer t) -> t)
             
instance Show Op where
  show Mul = "*"
  show Add = "+"
  show Sub = "-"
  show Div = "/"
  show Neg = "-"
  show Deref = "Deref"
  show Arrow = "->"
  show Dot = "."
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
  show AddrAdd = "AddrAdd"
  show (MemMov s) = "MemMov " ++ (show s)
