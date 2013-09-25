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
      case contained i e of -- contained NYI
        True -> Left (Error ("Recursive declaration of " ++ (show i)))
        False -> Right $ ADeclare i t (ASeq (AAssign i e) s)
elaborate' ((Simp (Asgn i Nothing e _)_) : xs)  =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ AAssign i e
elaborate' ((Simp (Asgn i (Just e) e2 _)_) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign i e2) s
elaborate' ((Simp (PostOp o e _)_) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case e of
      Ident _ _-> Right $ ASeq (AAssign "" e) s
      _ -> Left (Error ("Applying " ++ (show o) ++ " to non-identifier " ++ (show e)))
elaborate' ((Simp (Expr e _)_) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign "" e) s
-- CONTROL FLOW --
  -- IF --
elaborate' ((Ctrl (If e st (Nothing) _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' [st] of
      Left s' -> Left s'
      Right s' -> Right $ ASeq (AIf e s' ANup) s
elaborate' ((Ctrl (If e s1 (Just s2) _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case (elaborate' [s1], elaborate'[s2]) of
      (Right s1', Right s2') -> Right $ ASeq (AIf e s1' s2') s
      (Left s', _) -> Left s'
      (_, Left s') -> Left s'
  -- WHILE --
elaborate' ((Ctrl (While e st _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' [st] of
      Left s' -> Left s'
      Right s' -> Right $ ASeq (AWhile e s') s
  -- FOR - for(; expr;){} --
elaborate' ((Ctrl (For (Nothing) e (Nothing) st _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' [st] of
      Left s' -> Left s'
      Right s' -> Right $ ASeq (AWhile e s') s
  -- FOR - for(decl; expr;){} --
elaborate' ((Ctrl (For (Just simp) e (Nothing) st _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' [st] of
      Left s' -> Left s'
      Right s' -> 
        case simp of
          Decl t i Nothing _ -> Right $ ASeq (AWhile e s') s
          Decl t i (Just expr) _ -> Right $ ASeq (AWhile e s') s
          Asgn i Nothing e _ -> Right $ ASeq (AWhile e s') s
          Asgn i (Just expr) e _ -> Right $ ASeq (AWhile e s') s
  -- FOR - for(; expr; Asgn/PostOp/Expr){} --
elaborate' ((Ctrl (For (Nothing) e (Just simp) st _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' [st] of
      Left s' -> Left s'
      Right s' -> case simp of
        PostOp _ _ _ -> Right $ ASeq (AWhile e s') s
        Expr _ _ -> Right $ ASeq (AWhile e s') s
  -- FOR - for(decl; expr; Asgn/PostOp/Expr){} --
elaborate' ((Ctrl (For (Just simp1) e (Just simp2) st _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' [st] of
      Left s' -> Left s'
      Right s' -> {-case on simp1 and simp2 here -} Right $ ASeq (AWhile e s') s
  -- RETURN --
elaborate' ((Ctrl (Return e _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AReturn e) s
-- BLOCK STMTs --
elaborate' ((BlockStmt (Block l _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' l of
      Left s' -> Left s'
      Right s' -> Right $ ASeq s' s


    
contained :: String -> Expr -> Bool
contained i (Ident x _) = i == x
contained i (ExpUnOp _ e _) = contained i e
contained i (ExpBinOp _ e1 e2 _) = contained i e1 || contained i e2
contained i (ExpTernOp e1 e2 e3 _) = contained i e1 || contained i e2 || contained i e3
contained _ _ = False
