module Compile.Elaborate where

import Compile.Types
import Debug.Trace


elaborate :: Program -> S
elaborate (Program (Block stmts _)) =
  case elaborate' stmts of
    Left s -> throw s
    Right s -> s

data Error = Error String

elaborate' :: [Stmt] -> Either Error S
elaborate' [] = Nop
elaborate' ((Simp (Decl T I Nothing)) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Declare I T s
elaborate' ((Simp (Decl T I (Just E))) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s ->
      case contained I E of
        True -> Left "Recursive declaration of " ++ (show I)
        False -> Declare I T (Seq (Assign X E) s)
elaborate' 
