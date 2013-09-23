module Compile.CheckAST where

import Compile.Types
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace

-- Checks that the abstract syntax adheres to the static semantics
-- TODO: check variable initialization
checkAST :: S -> Either String ()
checkAST s =
  case checkReturns s of
    False -> Left "One or more control flow paths do not return"
    True ->
      case checkS s Map.empty of
        BadS s -> Left s
        ValidS -> 
          case checkInit s Set.empty of
            Left s -> Left s
            Right _ -> Right ()
          

-- Verifies that all control flow paths end with a return statement
checkReturns :: S -> Bool
checkReturns ANup = False
checkReturns (AAssign _ _) = False
checkReturns (AWhile _ _) = False
checkReturns (AReturn _) = True
checkReturns (AIf _ s1 s2) = (checkReturns s1) && (checkReturns s2)
checkReturns (ASeq s1 s2) = (checkReturns s1) || (checkReturns s2)
checkReturns (ADeclare _ _ s) = checkReturns s

data CheckS = ValidS
            | BadS String
              
data CheckE = ValidE Type
            | BadE String

type Context = Map.Map String Type

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

-- Checks that no variables are used before definition
checkInit :: S -> Set.Set String -> Either String (Set.Set String)
checkInit ANup live = Right live
checkInit (AReturn e) live = 
  case Set.isSubsetOf (uses e) live of
    False -> Left "Return statement uses undefined variable(s)"
    True -> Right Set.empty
checkInit (AAssign i e) live = 
  case Set.isSubsetOf (uses e) live of
    False -> Left $ "Undeclared variable on RHS of define for " ++ i
    True -> Right $ Set.delete i live
checkInit (AIf e s1 s2) live = 
  case Set.isSubsetOf (uses e) live of
    False -> Left "If condition uses undefined variable(s)"
    True ->
      case (checkInit s1 live, checkInit s2 live) of
        (Left s, _) -> Left s
        (_, Left s) -> Left s
        (Right live1, Right live2) ->
          Right $ Set.difference live $ Set.intersection live1 live2
checkInit (AWhile e s) live =
  case Set.isSubsetOf (uses e) live of
    False -> Left "While condition uses undefined variable(s)"
    True ->
      case checkInit s live of
        Left s -> Left s
        Right _ -> Right live
checkInit (ASeq s1 s2) live =
  case checkInit s1 live of
    Left s -> Left s
    Right live' -> checkInit s2 live'
checkInit (ADeclare i _ s) live =
  case checkInit s (Set.insert i live) of
    Left s -> Left s
    Right _ -> Right live
    
-- Evaluates to a list of identifiers used in the expression
uses :: Expr -> Set.Set String
uses (Ident i _) = Set.singleton i
uses (ExpUnOp _ e _) = uses e
uses (ExpBinOp _ e1 e2 _) = Set.union (uses e1) (uses e2)
uses (ExpTernOp e1 e2 e3 _) = Set.unions [uses e1, uses e2, uses e3]
uses _ = Set.empty