module Compile.Types.Asm where

import Text.ParserCombinators.Parsec.Pos (SourcePos)

import Compile.Types.AbstractAssembly

data Asm = AsmRet
         | Movl Arg Arg 
         | Addl Arg Arg 
         | Subl Arg Arg deriving Show
data Arg = Reg ALoc
         | Val Int deriving Show