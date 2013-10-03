{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines a flat abstract assembly.
-}
module Compile.Types.AbstractAssembly where

import Compile.Types.Ops
import qualified Data.Set as Set

data AAsm = AAsm {aAssign :: [ALoc]
                 ,aOp     :: Op
                 ,aArgs   :: [AVal]
                 }
          | ACtrl COp
          | AComment String deriving Show

data COp = Ret AVal
         | Ifz AVal String -- If (!AVal) goto lbl
         | Goto String
         | Lbl String
         | GotoP String (Set.Set AVal)
         | IfzP AVal String (Set.Set AVal)
         deriving Show 

data AVal = ALoc ALoc
          | AImm Int deriving (Show, Eq, Ord)

data ALoc = AReg Int
          | ATemp Int
          | AVar String
          | AVarG String Int
          | Register ALoc deriving (Show, Eq, Ord)
