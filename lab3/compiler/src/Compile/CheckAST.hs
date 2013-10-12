module Compile.CheckAST where

import Compile.Types
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace

-- Checks that the abstract syntax adheres to the static semantics
checkAST :: (Map.Map String Type, [(String,
                                  (Type, [Param], S,
                                   Map.Map String Type,
                                   Map.Map String (Type, [Type])))]) -> Either String ()
checkAST (typedef, fdefns) =
  let
    (typedef', ctx) = addHeader typedef
  in
    (case lookup "main" fdefns of
        Nothing -> Left "main undefined"
        (Just (t, p, s, _, _)) ->
          if length(p) > 0 then Left "main should take no arguments" else
            if not(typeEq typedef' (Int, t)) then Left "main is not type int" else
              Right ()) >>= \_ ->
    case foldr
         (\(fun,(t, p, b, tdefs, fdecls)) -> \acc ->
           case acc of
             Left s -> Left s
             Right ctx -> 
               let
                 (output, args, _) = fixTypes typedef' (t,p,ANup)
                 ts = map (\(Param ty i) -> ty) args
                 ctx' = Map.unions [ctx, Map.map (\(t1,t2) -> Map t2 t1) fdecls,
                                    Map.singleton fun (Map ts output)]
                 ctx'' = Map.map (findType typedef') ctx'
               in case checkFunction typedef' ctx'' (t,p,b) of
                 Left s -> Left s
                 Right () -> Right ctx'') (Right ctx) fdefns of
      Left s -> Left s
      Right _ -> Right ()
       

addHeader typedef = let
  funs = [("fadd", Map [Int, Int] Int),
          ("fsub", Map [Int, Int] Int),
          ("fmul", Map [Int, Int] Int),
          ("fdiv", Map [Int, Int] Int),
          ("fless", Map [Int, Int] Bool),
          ("itof", Map [Int] Int),
          ("ftoi", Map [Int] Int),
          ("print_fpt", Map [Int] Void),
          ("print_int", Map [Int] Void),
          ("print_hex", Map [Int] Void)]
  in (Map.insert "fpt" Int typedef, Map.fromList funs)
             
fixTypes m (t, p, s) = 
  let
    t' = findType m t
    p' = map (\(Param t1 s) -> Param (findType m t1) s) p
    s' = fixTypes' m s
  in (t', p', s') where
   
fixTypes' m (ADeclare i t s) = ADeclare i (findType m t) (fixTypes' m s)
fixTypes' m (AIf e s1 s2) = AIf e (fixTypes' m s1) (fixTypes' m s2)
fixTypes' m (AWhile e s) = AWhile e (fixTypes' m s)
fixTypes' m (ASeq s1 s2) = ASeq (fixTypes' m s1) (fixTypes' m s2)
fixTypes' m (ABlock s1 s2) = ABlock (fixTypes' m s1) (fixTypes' m s2)
fixTypes' m (AExpr e s) = AExpr e (fixTypes' m s)
fixTypes' m x = x

findType m (Type s) = findType m (m Map.! s)
findType m (Map t1 t2) = Map (map (findType m) t1) (findType m t2)
findType _ x = x
             
checkFunction m ctx val =
  let
    -- replace all typedef types so we dont have to deal with them
    (t', p', s') = fixTypes m val
  in (let b = case t' of
            Void -> checkNoReturns s'
            _ -> checkReturns s'
      in case b of
        True -> Right ()
        False -> Left "error in returns check") >>= \_ ->
     (let
         ctx' = foldr (\(Param t s) -> \acc -> Map.insert s t acc) ctx p'
      in case checkS s' ctx' t' of
        ValidS -> Right ()
        BadS s -> Left s) >>= \_ ->
     (let
         vars = map (\(Param t i) -> i) p'
         defn = Set.fromList vars
      in if not(Set.size(defn) == length(p')) then Left "duplicate args" else
           case checkInit s' (Set.empty, defn) of
             Left s -> Left s
             Right _ -> Right()) >>= \_ ->
     (if collides s' (Map.keysSet m) then
        Left "var name collides with type name"
      else Right())

--scans all subepressions for var names colliding with type names
collides (AIf _ s1 s2) m = (collides s1 m) || (collides s2 m)
collides (AWhile _ s) m = collides s m
collides (ASeq s1 s2) m = (collides s1 m) || (collides s2 m)
collides (ABlock s1 s2) m = (collides s1 m) || (collides s2 m)
collides (AExpr _ s) m = collides s m
collides (ADeclare i _ s) m = (Set.member i m) || (collides s m)
collides _ _ = False

typeEq m (e1,e2) = let
  in case (e1, e2) of
    (Type s1, Type s2) ->
      case (Map.lookup s1 m, Map.lookup s2 m) of
        (Just t1, Just t2) -> typeEq m (t1,t2)
        _ -> False
    (_, Type s) ->
      case Map.lookup s m of
        Just t2 -> e1 == t2
        _ -> False
    (Type s, _) ->
      case Map.lookup s m of
        Just t1 -> t1 == e2
        _ -> False
    (_, _) -> e1 == e2
    
-- Verifies that all control flow paths end with a return statement
checkReturns :: S -> Bool
checkReturns ANup = False
checkReturns (AAssert _) = False
checkReturns (AAssign _ _) = False
checkReturns (AWhile _ _) = False
checkReturns (AReturn Nothing) = False
checkReturns (AReturn (Just _)) = True
checkReturns (AIf _ s1 s2) = (checkReturns s1) && (checkReturns s2)
checkReturns (ASeq s1 s2) = (checkReturns s1) || (checkReturns s2)
checkReturns (ABlock s1 s2) = (checkReturns s1) || (checkReturns s2)
checkReturns (ADeclare _ _ s) = checkReturns s
checkReturns (AExpr _ s) = checkReturns s
    
-- Verifies that no control flow paths end with a return statement
checkNoReturns :: S -> Bool
checkNoReturns ANup = True
checkNoReturns (AAssert _) = True
checkNoReturns (AAssign _ _) = True
checkNoReturns (AWhile _ s) = checkNoReturns s
checkNoReturns (AReturn Nothing) = True
checkNoReturns (AReturn (Just _)) = False
checkNoReturns (AIf _ s1 s2) = (checkNoReturns s1) && (checkNoReturns s2)
checkNoReturns (ASeq s1 s2) = (checkNoReturns s1) && (checkNoReturns s2)
checkNoReturns (ABlock s1 s2) = (checkNoReturns s1) && (checkNoReturns s2)
checkNoReturns (ADeclare _ _ s) = checkNoReturns s
checkNoReturns (AExpr _ s) = checkNoReturns s

data CheckS = ValidS
            | BadS String
              
data CheckE = ValidE Type
            | BadE String

type Context = Map.Map String Type

-- Performs static type checking on a statements  under a typing context
checkS :: S -> Context -> Type -> CheckS
checkS ANup ctx _ = ValidS
checkS (AAssert e) ctx _ =
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Bool -> ValidS
    ValidE _ -> BadS "Assert expression not type bool"
checkS (ASeq s1 s2) ctx t = 
  case checkS s1 ctx t of
    BadS s -> BadS s
    ValidS -> checkS s2 ctx t
checkS (ABlock s1 s2) ctx t = 
  case checkS s1 ctx t of
    BadS s -> BadS s
    ValidS -> checkS s2 ctx t
checkS (ADeclare i t' s) ctx t =
  case Map.lookup i ctx of
    -- allow shadowing of variables over functions
    Just (Map _ _) -> checkS s (Map.insert i t' ctx) t
    Just _ -> BadS $ "Redeclaring " ++ i
    Nothing -> checkS s (Map.insert i t' ctx) t
checkS (AReturn e) ctx t = 
  case (e,t) of
    (Nothing, Void) -> ValidS
    (Nothing, _) -> BadS "empty return statement in non-void function"
    (Just _, Void) -> BadS "non-empty return statement in void function"
    (Just e', _) ->
      case checkE e' ctx of
        BadE s -> BadS s
        ValidE t' -> if t==t' then ValidS else BadS "return type mismatch"
checkS (AWhile e s) ctx t = 
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Int -> BadS "While condition is not type bool"
    ValidE Bool -> checkS s ctx t
checkS (AAssign i e) ctx _ =
  case Map.lookup i ctx of
    Nothing -> BadS $ "Assigning " ++ i ++ " undeclared"
    Just t1 ->
      case checkE e ctx of
        BadE s -> BadS s
        ValidE t2 -> if t1 == t2 then ValidS
                     else BadS $ i ++ " declared with type " ++ (show t1) ++ 
                          " assigned with type " ++ (show t2)
checkS (AIf e s1 s2) ctx t =
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Int -> BadS "If condition is not type bool"
    ValidE Bool ->
      case checkS s1 ctx t of
        BadS s -> BadS s
        ValidS -> checkS s2 ctx t
checkS (AExpr e s) ctx t =
  case checkE e ctx of
    BadE s -> BadS s
    ValidE _ -> checkS s ctx t
  
-- Performs static type checking on an expression under a typing context
checkE :: Expr -> Context -> CheckE
checkE (ExpInt Dec i _) _ = if i > (2^31) then BadE "const too large"
                            else ValidE Int
checkE (ExpInt Hex i _) _ = if i > (2^32 - 1) then BadE "const too large"
                            else ValidE Int
checkE (TrueT _) _ = ValidE Bool
checkE (FalseT _) _ = ValidE Bool
checkE (Ident i _) ctx = 
  case Map.lookup i ctx of
    Nothing -> BadE $ i ++ " used undeclared."
    Just t -> ValidE t    
checkE (ExpUnOp op e _) _ | op == Incr || op == Decr =
  BadE "incr or decr in expression"
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
checkE (App fun args _) ctx =
  let
    ts = map (\e -> checkE e ctx) args
    -- TODO better error propagation here
    ts' = map (\(ValidE t) -> t) ts
  in case Map.lookup fun ctx of
    (Just (Map input output)) ->
      if ts' == input then ValidE output
      else BadE "function input type mismatch"
    _ -> BadE "undefined function call"
                      
-- Checks that no variables are used before definition
checkInit :: S -> (Set.Set String, Set.Set String) -> Either String (Set.Set String, Set.Set String)
checkInit ANup acc = Right acc
checkInit (AAssert _) acc = Right acc
checkInit (AReturn Nothing) (live, defn) =
  Right (Set.empty, Set.union defn live)
checkInit (AReturn (Just e)) (live, defn) = 
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
checkInit (ABlock s1 s2) (live, defn) =
  case checkInit s1 (live, defn) of
    Left s -> Left s
    Right (_, defn') -> checkInit s2 (Set.difference live defn', defn')
checkInit (ADeclare i _ s) (live, defn) =
  case checkInit s (Set.insert i live, defn) of
    Left s -> Left s
    Right (live', defn') -> Right (Set.difference live defn', defn')
checkInit (AExpr e s) (live, defn) =  
  case checkLive (uses e) live of
    True -> Left "Using live vars"
    False -> checkInit s (live, defn)
  
checkLive s live =
  Set.fold (||) False $ Set.map (\x -> Set.member x live) s
    
-- Evaluates to a set of identifiers used in the expression
uses :: Expr -> Set.Set String
uses (Ident i _) = Set.singleton i
uses (ExpUnOp _ e _) = uses e
uses (ExpBinOp _ e1 e2 _) = Set.union (uses e1) (uses e2)
uses (ExpTernOp e1 e2 e3 _) = Set.unions [uses e1, uses e2, uses e3]
uses (App _ es _) = Set.unions (map uses es)
uses _ = Set.empty
