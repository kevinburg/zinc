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
          case checkInit s (Set.empty, Set.empty) of
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
checkE (Ident i _) ctx = 
  case Map.lookup i ctx of
    Nothing -> BadE $ i ++ " used undeclared."
    Just t -> ValidE t    
checkE (ExpUnOp op e _) ctx =
  let
    ([opT], ret) = opType op
  in case (checkE e ctx) of
    BadE s -> BadE s
    ValidE t -> if opT == t then ValidE ret
                else BadE "unop expr mismatch"
checkE (ExpBinOp op e1 e2 _) ctx =
  if (op == Eq) || (op == Neq) then
    case (checkE e1 ctx, checkE e2 ctx) of
      (BadE s, _) -> BadE s
      (_, BadE s) -> BadE s
      (ValidE t1, ValidE t2) -> if t1 == t2 then ValidE Bool
                                else BadE "eq type mismatch"
  else
    let
      ([opT1, opT2], ret) = opType op
    in case (checkE e1 ctx, checkE e2 ctx) of
      (BadE s, _) -> BadE s
      (_, BadE s) -> BadE s
      (ValidE t1, ValidE t2) ->
        if (t1 == opT1) && (t2 == opT2) then ValidE ret
        else BadE ("binop expr mismatch " ++ (show e1) ++ (show e2) ++ (show op))
checkE (ExpTernOp e1 e2 e3 _) ctx =
  case (checkE e1 ctx, checkE e2 ctx, checkE e3 ctx) of
    (BadE s, _, _) -> BadE s
    (_, BadE s, _) -> BadE s
    (_, _, BadE s) -> BadE s
    (ValidE t1, ValidE t2, ValidE t3) ->
      case t1 of
        Int -> BadE "cond in ternary op not type bool"
        Bool -> if t2 == t3 then ValidE t2
                else BadE "ternary result type mismatch"
                      
-- Checks that no variables are used before definition
checkInit :: S -> (Set.Set String, Set.Set String) -> Either String (Set.Set String, Set.Set String)
checkInit ANup acc = Right acc
checkInit (AReturn e) (live, defn) = 
  case checkLive (uses e) live of
    True -> Left "Return statement uses undefined variable(s)"
    False -> Right (Set.empty, Set.union defn live)
checkInit (AAssign i e) (live, defn) = 
  case checkLive (uses e) live of
    True -> Left $ "Undeclared variable on RHS of define for " ++ i
    False -> Right $ (Set.delete i live, Set.insert i defn)
checkInit (AIf e s1 s2) (live, defn) = 
  case checkLive (uses e) live of
    True -> Left "If condition uses undefined variable(s)"
    False ->
      case (checkInit s1 (live, defn), checkInit s2 (live, defn)) of
        (Left s, _) -> Left s
        (_, Left s) -> Left s
        (Right (live1, defn1), Right (live2, defn2)) ->
          Right (Set.difference live $ Set.intersection defn1 defn2,
                 Set.union defn $ Set.intersection defn1 defn2)
checkInit (AWhile e s) (live, defn) =
  case checkLive (uses e) live of
    True -> Left "While condition uses undefined variable(s)"
    False ->
      case checkInit s (live, defn) of
        Left s -> Left s
        Right _ -> Right (live, defn)
checkInit (ASeq s1 s2) acc =
  case checkInit s1 acc of
    Left s -> Left s
    Right acc' -> checkInit s2 acc'
checkInit (ADeclare i _ s) (live, defn) =
  case checkInit s (Set.insert i live, defn) of
    Left s -> Left s
    Right _ -> Right (live, defn)
    
checkLive s live =
  Set.fold (||) False $ Set.map (\x -> Set.member x live) s
    
-- Evaluates to a list of identifiers used in the expression
uses :: Expr -> Set.Set String
uses (Ident i _) = Set.singleton i
uses (ExpUnOp _ e _) = uses e
uses (ExpBinOp _ e1 e2 _) = Set.union (uses e1) (uses e2)
uses (ExpTernOp e1 e2 e3 _) = Set.unions [uses e1, uses e2, uses e3]
uses _ = Set.empty
