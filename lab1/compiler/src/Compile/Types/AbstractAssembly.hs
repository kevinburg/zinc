{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines a flat abstract assembly.
-}
module Compile.Types.AbstractAssembly where

import Compile.Types.Ops

data AAsm = AAsm {aAssign :: [ALoc]
                 ,aOp     :: Op
                 ,aArgs   :: [AVal]
                 }
          | ACtrl COp AVal
          | AComment String deriving Show

data AVal = ALoc ALoc
          | AImm Int deriving (Show, Eq, Ord)

data ALoc = AReg Int
          | ATemp Int
          | Register ALoc deriving (Show, Eq, Ord)
