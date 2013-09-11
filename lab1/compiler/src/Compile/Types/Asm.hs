module Compile.Types.Asm where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.AbstractAssembly

data Asm = AsmRet
         | Movl Arg Arg 
         | Addl Arg Arg 
         | Subl Arg Arg

data Arg = Reg Register
         | Val Int

data Register = EAX
              | EBX
              | ECX
              | EDX
              | ESI
              | EDI
              | ESP
              | EBP
              | R9
              | R10
              | R11
              | R12
              | R13
              | R14
              | R15

instance Show Asm where
  show (AsmRet) = "\tret"
  show (Movl e1 e2) = "\tmovl " ++ show e1 ++ ", " ++ show e2
  show (Addl e1 e2) = "\taddl " ++ show e1 ++ ", " ++ show e2
  
instance Show Arg where
  show (Reg reg) = "%" ++ show reg
  show (Val i) = "$" ++ show i
  
instance Show Register where
  show EAX = "eax"
  show EBX = "ebx"
  show ECX = "ecx"
  show EDX = "edx"
  show ESI = "esi"
  show EDI = "edi"