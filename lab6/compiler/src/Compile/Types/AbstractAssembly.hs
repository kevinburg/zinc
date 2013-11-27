{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Defines a flat abstract assembly.
-}
module Compile.Types.AbstractAssembly where

import Compile.Types.Ops
import Compile.Types.Asm
import Compile.Types.PST
import qualified Data.Set as Set

import Control.DeepSeq

data AAsm = AAsm {aAssign :: [ALoc]
                 ,aOp     :: Op
                 ,aArgs   :: [AVal]
                 }
          | ACtrl COp
          | APush ALoc
          | APop ALoc
          | AComment String deriving (Ord, Eq, Show)

data COp = Ret AVal
         | Ifz AVal String Bool
         | Comp AVal AVal Op String
         | Goto String
         | Lbl String
         | GotoP String [(ALoc, Maybe AVal)]
         | IfzP AVal String Bool [(ALoc, Maybe AVal)]
         | CompP AVal AVal Op String [(ALoc, Maybe AVal)]
         | Call String [Int]
         deriving (Show, Ord, Eq)

data AVal = ALoc ALoc
          | AImm Int deriving (Show, Eq, Ord)

data ALoc = ARes
          | AArg Int
          | AReg Register
          | ATemp Int
          | AVar String
          | AVarG String Int
          | Pt ALoc
          | Register ALoc deriving (Show, Eq, Ord)

instance NFData AAsm where
  rnf (AAsm {aAssign = aloc, aOp = op, aArgs = aval}) = aloc `seq` op `seq` aval `seq` ()
  rnf (ACtrl cop) = cop `seq` ()
  rnf (AComment str) = str `seq` ()

instance NFData COp where
  rnf (Ret aval) = aval `seq` ()
  rnf (Ifz aval str _) = aval `seq` str `seq` ()
  rnf (Goto str) = str `seq` ()
  rnf (Lbl str) = str `seq` ()
  rnf (GotoP str vals) = str `seq` vals `seq` ()
  rnf (IfzP aval str _ vals) = aval `seq` str `seq` vals `seq` ()

instance NFData AVal where
  rnf (ALoc aloc) = aloc `seq` ()
  rnf (AImm i) = i `seq` ()


instance NFData ALoc where
  rnf (AReg i) = i `seq` ()
  rnf (ATemp i) = i `seq` ()
  rnf (AVar str) = str `seq` ()
  rnf (AVarG str i) = str `seq` i `seq` ()
  rnf (Register aloc) = aloc `seq` ()
