module Compile.Elaborate where

import Compile.Types
import Debug.Trace
import Control.Exception
import Data.Typeable


elaborate :: Program -> S
elaborate (Program (Block stmts _)) =
  case elaborate' stmts of
    Left (Error s) -> ANup
    Right s -> s

data Error = Error String

elaborate' :: [Stmt] -> Either Error S
elaborate' [] = Right ANup
elaborate' ((Simp (Decl t i Nothing _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right (ADeclare i t s)
elaborate' ((Simp (Decl t i (Just e) _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s ->
      case False of --contained i e of -- contained NYI
        True -> Left (Error ("Recursive declaration of " ++ (show i)))
        False -> Right $ ADeclare i t (ASeq (AAssign i e) s)
elaborate' ((Simp (Asgn I Nothing E)) : xs)  =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ AAssign I E
elaborate' ((Simp (Asgn I (Just e) E)) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign I E) s
elaborate' ((Simp (PostOp O E _)) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign "" E) s
elaborate' ((Simp (Expr E _)) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right S -> Right $ ASeq (AAssign "" E) s

contained :: String -> Expr -> Bool
contained I (Ident X _) = I == X
contained I (ExpUnOp _ E _) = contained I E
contained I (ExpBinOp _ E1 E2 _) = contained I E1 || contained I E2
contained I (ExpTernOp _ E1 E2 E3 _) = contained I E1 || contained I E2 || contained I E3
