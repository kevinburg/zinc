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
      case False of --contained i e of
        True -> Left (Error ("Recursive declaration of " ++ (show i)))
        False -> Right $ ADeclare i t (ASeq (AAssign i e) s)
