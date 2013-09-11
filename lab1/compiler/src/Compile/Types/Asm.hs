module Compile.Types.Asm where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.AbstractAssembly

data Asm = AsmRet
         | Movl Arg Arg 
         | Addl Arg Arg 
         | Subl Arg Arg deriving Show

data Arg = Reg Register
         | Val Int deriving Show

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
