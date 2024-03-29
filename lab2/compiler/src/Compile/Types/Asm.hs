module Compile.Types.Asm where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import qualified Numeric as Num

import Compile.Types.AbstractAssembly

data Asm = AsmRet
         | Movl Arg Arg 
         | Addl Arg Arg 
         | Andl Arg Arg 
         | Orl Arg Arg 
         | Xorl Arg Arg 
         | Subl Arg Arg
         | Imull Arg Arg
         | Negl Arg
         | Notl Arg
         | Idivl Arg
         | Push Arg
         | Subb Arg Arg
         | Mov Arg Arg | Pop Arg
         | Movslq Arg Arg
         | Sall Arg Arg
         | Sarl Arg Arg
         | Cdq
         | Jmp String
         | Testl Arg Arg
         | Cmpl Arg Arg
         | Je String
         | AsmLbl String
         | Movzbl Arg Arg
         | Setl Arg
         | Setle Arg
         | Sete Arg
         | Setne Arg

data Arg = Reg Register
         | Stk Int -- Stack offset int
         | Val Int deriving Eq

data Register = EAX
              | EBX
              | ECX
              | EDX
              | ESI
              | EDI
              | RSP
              | RBP
              | R8D
              | R9D
              | R10D
              | R11D
              | R12D
              | R13D
              | R14D
              | R15D 
              | R15B
              | CL
              | RDX deriving Eq

instance Show Asm where
  show (AsmRet) = "\tret"
  show (Movl e1 e2) = "\tmovl " ++ show e1 ++ ", " ++ show e2
  show (Sarl e1 e2) = "\tsarl " ++ show e1 ++ ", " ++ show e2
  show (Sall e1 e2) = "\tsall " ++ show e1 ++ ", " ++ show e2
  show (Movslq e1 e2) = "\tmovslq " ++ show e1 ++ ", " ++ show e2
  show (Mov e1 e2) = "\tmov " ++ show e1 ++ ", " ++ show e2
  show (Addl e1 e2) = "\taddl " ++ show e1 ++ ", " ++ show e2
  show (Andl e1 e2) = "\tandl " ++ show e1 ++ ", " ++ show e2
  show (Orl e1 e2) = "\torl " ++ show e1 ++ ", " ++ show e2
  show (Xorl e1 e2) = "\txorl " ++ show e1 ++ ", " ++ show e2
  show (Subl e1 e2) = "\tsubl " ++ show e1 ++ ", " ++ show e2
  show (Subb e1 e2) = "\tsub " ++ show e1 ++ ", " ++ show e2
  show (Imull e1 e2) = "\timull " ++ show e1 ++ ", " ++ show e2
  show (Negl e) = "\tnegl " ++ show e
  show (Notl e) = "\tnotl " ++ show e
  show (Idivl e) = "\tidivl " ++ show e
  show (Push e) = "\tpush " ++ show e
  show (Pop e) = "\tpop " ++ show e
  show Cdq = "\tcdq"
  show (Jmp s) = "\tjmp ." ++ s
  show (Testl e1 e2) = "\ttest " ++ show e1 ++ ", " ++ show e2
  show (Je s) = "\tje ." ++ s
  show (Cmpl e1 e2) = "\tcmpl " ++ show e1 ++ ", " ++ show e2
  show (AsmLbl s) = "." ++ s ++ ":"
  show (Setl e) = "\tsetl " ++ (show e)
  show (Sete e) = "\tsete " ++ (show e)
  show (Setne e) = "\tsetne " ++ (show e)
  show (Setle e) = "\tsetle " ++ (show e)
  show (Movzbl e1 e2) = "\tmovzbl " ++ (show e1) ++ ", " ++ (show e2)
  
instance Show Arg where
  show (Reg reg) = "%" ++ show reg
  show (Val i) = "$" ++ show i
  show (Stk i) = let neg = if i < 0 then "-0x" else "0x"
                     offset = neg ++ Num.showHex (abs(i)) "(%rbp)"
                 in
                  offset
  
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
  show RSP = "rsp"
  show RBP = "rbp"
  show RDX = "rdx"
  show R15B = "r15b"
  show CL = "cl"
