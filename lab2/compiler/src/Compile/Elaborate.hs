module Compile.Elaborate where

import Compile.Types
import Debug.Trace
import Control.Exception
import Data.Typeable
import Compile.CheckAST

elaborate :: Program -> Either String S
elaborate (Program (Block stmts _)) =
  case elaborate' stmts of
    Left (Error s) -> Left s
    Right s -> Right s

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
      case contained i e of
        True -> Left (Error ("Recursive declaration of " ++ (show i)))
        False -> Right $ ADeclare i t (ASeq (AAssign i e) s)
elaborate' ((Simp (Asgn i Nothing e _)_) : xs)  =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign i e) s
elaborate' ((Simp (Asgn i (Just op) e2 p) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign i (ExpBinOp op (Ident i p) e2 p)) s
elaborate' ((Simp (PostOp o e _)_) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> 
      case e of
        Ident i p -> 
          case o of 
            Incr -> Right $ ASeq (AAssign i (ExpBinOp Add (Ident i p) (ExpInt Dec 1 p) p)) s
            Decr -> Right $ ASeq (AAssign i (ExpBinOp Sub (Ident i p) (ExpInt Dec 1 p) p)) s
        _ -> Left (Error ("Applying " ++ (show o) ++ " to non-identifier " ++ (show e)))
elaborate' ((Simp (Expr (ExpUnOp Incr (Ident i p) _)_)_): xs) = 
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign i (ExpBinOp Add (Ident i p) (ExpInt Dec 1 p) p)) s
elaborate' ((Simp (Expr (ExpUnOp Decr (Ident i p) _)_)_): xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign i (ExpBinOp Sub (Ident i p) (ExpInt Dec 1 p) p)) s
elaborate' ((Simp (Expr (ExpUnOp Incr _ _) _)_): xs) = Left $ Error "bad incr"
elaborate' ((Simp (Expr (ExpUnOp Decr _ _) _)_): xs) = Left $ Error "bad decr"
elaborate' ((Simp (Expr _ _)_): xs) = elaborate' xs
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
  -- FOR --
elaborate' ((Ctrl (For (Just (Decl t i e _)) exp s2 s3 _) p) : xs) =      
  case s2 of
    Just (Decl _ _ _ _) -> Left (Error "step in for loop is decl")
    _ ->
      case (elaborate' xs, elaborate' (mList s2 p), elaborate' [s3]) of
        (Left err, _, _) -> Left err
        (_, Left err, _) -> Left err
        (_, _, Left err) -> Left err
        (Right s, Right step, Right body) ->
          case e of
            Nothing ->
              Right $ ASeq (ADeclare i t (AWhile exp (ASeq body step))) s
            (Just e') ->
              Right $ ASeq (ADeclare i t (ASeq (AAssign i e') (AWhile exp (ASeq body step)))) s
elaborate' ((Ctrl (For s1 exp s2 s3 _) p) : xs) =
  case s2 of
    Just (Decl _ _ _ _) -> Left (Error "step in for loop is decl")
    _ ->
      case (elaborate' xs, elaborate' (mList s1 p), elaborate' (mList s2 p), elaborate' [s3]) of
        (Left err, _, _, _) -> Left err
        (_, Left err, _, _) -> Left err
        (_, _, Left err, _) -> Left err
        (Right s, Right init, Right step, Right body) ->
          Right $ ASeq (ASeq init (AWhile exp (ASeq body step))) s
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

-- extremely special case function
mList Nothing _ = []
mList (Just x) p = [Simp x p]

    
contained :: String -> Expr -> Bool
contained i (Ident x _) = i == x
contained i (ExpUnOp _ e _) = contained i e
contained i (ExpBinOp _ e1 e2 _) = contained i e1 || contained i e2
contained i (ExpTernOp e1 e2 e3 _) = contained i e1 || contained i e2 || contained i e3
contained _ _ = False
