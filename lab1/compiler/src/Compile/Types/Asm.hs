module Compile.Types.Asm where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.AbstractAssembly

data Asm = AsmRet
         | Movl Arg Arg 
         | Addl Arg Arg 
         | Subl Arg Arg
         | Imull Arg Arg
         | Negl Arg
         | Idivl Arg

data Arg = Reg Register
         | Val Int deriving Eq

data Register = EAX
              | EBX
              | ECX
              | EDX
              | ESI
              | EDI
              | ESP
              | EBP
              | R8D
              | R9D
              | R10D
              | R11D
              | R12D
              | R13D
              | R14D
              | R15D deriving Eq

instance Show Asm where
  show (AsmRet) = "\tret"
  show (Movl e1 e2) = "\tmovl " ++ show e1 ++ ", " ++ show e2
  show (Addl e1 e2) = "\taddl " ++ show e1 ++ ", " ++ show e2
  show (Subl e1 e2) = "\tsubl " ++ show e1 ++ ", " ++ show e2
  show (Imull e1 e2) = "\timull " ++ show e1 ++ ", " ++ show e2
  show (Negl e) = "\tnegl " ++ show e
  show (Idivl e) = "\tidivl " ++ show e
  
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
  show R8D = "r8d"
  show R9D = "r9d"
  show R10D = "r10d"
  show R11D = "r11d"
  show R12D = "r12d"
  show R13D = "r13d"
  show R14D = "r14d"
  show R15D = "r15d"
