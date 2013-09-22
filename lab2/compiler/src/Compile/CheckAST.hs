module Compile.CheckAST where

import Compile.Types
import qualified Data.Map as Map
import Debug.Trace

data CheckS = ValidS
            | BadS String
              
data CheckE = ValidE Type
            | BadE String

type Context = Map.Map String Type

-- Checks that the abstract syntax adheres to the static semantics
-- TODO: check variable initialization
checkAST :: S -> Either String ()
checkAST s =
  case checkReturns s of
    False -> Left "One or more control flow paths do not return"
    True ->
      case checkS s Map.empty of
        ValidS -> Right ()
        BadS s -> Left s

-- Verifies that all control flow paths end with a return statement
checkReturns :: S -> Bool
checkReturns ANup = False
checkReturns (AAssign _ _) = False
checkReturns (AWhile _ _) = False
checkReturns (AReturn _) = True
checkReturns (AIf _ s1 s2) = (checkReturns s1) && (checkReturns s2)
checkReturns (ASeq s1 s2) = (checkReturns s1) || (checkReturns s2)
checkReturns (ADeclare _ _ s) = checkReturns s

-- Performs static type checking on a statements  under a typing context
checkS :: S -> Context -> CheckS
checkS ANup ctx = ValidS
checkS (ASeq s1 s2) ctx = 
  case checkS s1 ctx of
    BadS s -> BadS s
    ValidS -> checkS s2 ctx
checkS (ADeclare i t s) ctx =
  case Map.lookup i ctx of
    Just _ -> BadS $ "Redeclaring " ++ i
    Nothing -> checkS s $ Map.insert i t ctx
checkS (AReturn e) ctx = 
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Bool -> BadS "Main returns type bool"
    ValidE Int -> ValidS
checkS (AWhile e s) ctx = 
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Int -> BadS "While condition is not type bool"
    ValidE Bool -> checkS s ctx
checkS (AAssign i e) ctx =
  case Map.lookup i ctx of
    Nothing -> BadS $ "Assigning " ++ i ++ " undeclared"
    Just t1 ->
      case checkE e ctx of
        BadE s -> BadS s
        ValidE t2 -> if t1 == t2 then ValidS
                     else BadS $ i ++ " declared with type " ++ (show t1) ++ 
                          " assigned with type " ++ (show t2)
checkS (AIf e s1 s2) ctx =
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Int -> BadS "If condition is not type bool"
    ValidE Bool ->
      case checkS s1 ctx of
        BadS s -> BadS s
        ValidS -> checkS s2 ctx
  
-- Performs static type checking on an expression under a typing context
checkE :: Expr -> Context -> CheckE
checkE (ExpInt _ _ _) _ = ValidE Int
checkE (TrueT _) _ = ValidE Bool
checkE (FalseT _) _ = ValidE Bool