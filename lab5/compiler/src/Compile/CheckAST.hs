module Compile.CheckAST where

import Compile.Types
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Debug.Trace

{- TODO: Look at that type. It's pretty ridiculous. We have serious
scoping problems that I've decided to resolve up to now by just
throwing more information on top of what we are tracking for each
function definition. At some point this might affect our performance. -}
-- Checks that the abstract syntax adheres to the static semantics
checkAST :: (Map.Map String Type, [(String,
                                  (Type, [Param], S,
                                   Map.Map String Type,
                                   Map.Map String (Type, [Type]),
                                   Map.Map String [Param]))],
             Map.Map String [Param]) -> Either String (Map.Map String [Param])
checkAST (typedef, fdefns, sdefns) =
  let
    (_, ctx) = addHeader typedef
  in
    (case lookup "main" fdefns of
        Nothing -> Left "main undefined"
        (Just (t, p, s, tdefs, _, _)) ->
          if length(p) > 0 then Left "main should take no arguments" else
            if not(typeEq tdefs (Int, (findType tdefs) t)) then Left "main is not type int" else
              Right ()) >>= \_ ->
    case foldr
         (\(fun,(t, p, b, tdefs, fdecls, sdefns')) -> \acc ->
           case findType tdefs t of
             (Struct _) -> Left "function returns large type"
             _ ->
               case acc of
                 Left s -> Left s
                 Right ctx -> let
                   (output, args, _) = fixTypes tdefs (t,p,ANup)
                   ts = map (\(Param ty i) -> ty) args
                   ctx' = Map.unions [ctx, Map.map (\(t1,t2) -> Map t2 t1) fdecls,
                                      Map.singleton fun (Map ts output)]
                   ctx'' = Map.map (findType tdefs) ctx'
                   sdefns'' = Map.map
                              (\x -> map (\(Param t s) ->Param (findType typedef t) s) x)
                              sdefns'
                   in case checkFunction tdefs ctx'' (t,p,b) fdefns sdefns'' of
                     Left s -> Left s
                     Right () -> Right ctx'') (Right ctx) fdefns of
      Left s -> Left s
      Right _ -> Right sdefns
       
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

{- TODO: I feel like we run this fixTypes routine in a bunch of
different places across the codebase under different names.
Maybe unify them? -}
fixTypes' m (ADeclare i t s) = ADeclare i (findType m t) (fixTypes' m s)
fixTypes' m (AIf e s1 s2) = AIf (fixTypesE m e) (fixTypes' m s1) (fixTypes' m s2)
fixTypes' m (AWhile e s) = AWhile (fixTypesE m e) (fixTypes' m s)
fixTypes' m (ASeq s1 s2) = ASeq (fixTypes' m s1) (fixTypes' m s2)
fixTypes' m (ABlock s1 s2) = ABlock (fixTypes' m s1) (fixTypes' m s2)
fixTypes' m (AExpr e s) = AExpr (fixTypesE m e) (fixTypes' m s)
fixTypes' m (AAssign l e) = AAssign l (fixTypesE m e)
fixTypes' m (AReturn (Just e)) = AReturn $ Just (fixTypesE m e)
fixTypes' m x = x

fixTypesE m (Alloc t p) = Alloc (findType m t) p
fixTypesE m (AllocArray t e p) = AllocArray (findType m t) e p
fixTypesE m (ExpBinOp Arrow e i p) = ExpBinOp Arrow (fixTypesE m e) i p
fixTypesE m (App s e p) = let e' = map (fixTypesE m) e
                          in App s e' p
fixTypesE m x = x

findType m (Type s) = let
  res = (m Map.! s)
  in res `seq` findType m res
findType m (Map t1 t2) = Map (map (findType m) t1) (findType m t2)
findType m (Pointer t) = let
  t' = findType m t
  in t' `seq` Pointer t'
findType m (Array t) = let
  t' = findType m t
  in t' `seq` Array (findType m t)
findType _ x = x
             
checkFunction m ctx val defined sdefns =
  let
    -- replace all typedef types so we dont have to deal with them
    (t', p', s') = fixTypes m val
    defined' = Set.union (Set.fromList $ map (\(k,_) -> k) defined) 
               (Set.fromList ["fadd","fsub","fmul","fdiv","fless",
                              "itof","ftoi","print_fpt",
                              "print_int","print_hex", "main"])
  in (let b = case t' of
            Void -> checkNoReturns s'
            _ -> checkReturns s'
      in case b of
        True -> Right ()
        False -> Left "error in returns check") >>= \_ ->
     (let
         ctx' = foldr (\(Param t s) -> \acc -> Map.insert s t acc) ctx p'
         ctx'' = Map.foldWithKey (\s -> \_ -> \acc -> Map.insert s (Struct s) acc)
                 ctx' sdefns
      in case checkS s' (Map.insert "main" (Map [] Int) ctx') m defined' t' sdefns of
        ValidS -> Right ()
        BadS s -> Left s) >>= \_ ->
     (let
         paramT = map (\(Param t i) -> t) p'
         aVoid = foldl (\x -> \y -> case (x,y) of {(Void,_) -> Void; (_,Void) -> Void; (t1,_) -> t1}) Int paramT
         vars = map (\(Param t i) -> i) p'
         defn = Set.fromList vars
      in if aVoid == Void then Left "Parameter with type void"
         else if not(Set.size(defn) == length(p')) then Left "duplicate args" else
           case checkInit s' (Set.empty, defn) of
             Left s -> Left s
             Right _ -> Right())>>= \_ ->
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
        Just t2 -> typeEq m (e1,t2)
        _ -> False
    (Type s, _) ->
      case Map.lookup s m of
        Just t1 -> typeEq m (t1,e2)
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
checkS :: S -> Context -> Context -> Set.Set String -> Type ->
          Map.Map String [Param] ->CheckS
checkS ANup ctx _ _ _ _ = ValidS
checkS (AAssert e) ctx m d _ smap =
  case checkE e ctx d smap of
    BadE s -> BadS s
    ValidE Bool -> ValidS
    ValidE _ -> BadS "Assert expression not type bool"
checkS (ASeq s1 s2) ctx m d t smap = 
  case checkS s1 ctx m d t smap of
    BadS s -> BadS s
    ValidS -> checkS s2 ctx m d t smap
checkS (ABlock s1 s2) ctx m d t smap = 
  case checkS s1 ctx m d t smap of
    BadS s -> BadS s
    ValidS -> checkS s2 ctx m d t smap
checkS (ADeclare i t' s) ctx m d t smap =
  if Map.member i m then BadS "Variable name conflicts with Type"
  else case t' of
    Void -> BadS "Variables can't be of type void"
    Struct _ -> BadS "declaring large type"
    Array (Void) -> BadS "Arrays cannot have type void"
    _ ->
      case Map.lookup i ctx of
        -- allow shadowing of variables over functions
        Just (Map _ _) -> case s of
          (ASeq (AAssign _ e) s2) ->
            case checkE e ctx d smap of
              BadE s -> BadS s
              ValidE t2 -> if t' == t2 then checkS s2 (Map.insert i t' ctx) m d t smap
                              else BadS $ i ++ " declared with type " ++ "no" ++ --(show t') ++ 
                                " assigned with type " ++ "no" --(show t2)
          _ -> checkS s (Map.insert i t' ctx) m d t smap
        Just _ -> BadS $ "Redeclaring " ++ i
        Nothing -> checkS s (Map.insert i t' ctx) m d t smap
checkS (AReturn e) ctx m d t smap = 
  case (e,t) of
    (Nothing, Void) -> ValidS
    (Nothing, _) -> BadS "empty return statement in non-void function"
    (Just _, Void) -> BadS "non-empty return statement in void function"
    (Just e', _) ->
      case checkE e' ctx d smap of
        BadE s -> BadS s
        ValidE t' -> let
          cond = case (t,t') of
            (Pointer _, Pointer Void) -> True
            _ -> t==t'
          in if cond then ValidS else BadS "return type mismatch"
checkS (AWhile e s) ctx m d t smap = 
  case checkE e ctx d smap of
    BadE s -> BadS s
    ValidE Int -> BadS "While condition is not type bool"
    ValidE Bool -> checkS s ctx m d t smap
checkS (AAssign l e) ctx m d _ smap =
  case lvalType l ctx d smap of
    Nothing -> BadS $ "Could not derive type for lval " ++ (show l)
    Just t1 ->
      case checkE e ctx d smap of
        BadE s -> BadS s
        ValidE t2 -> if (t1 == t2 && asnStrct(t2)) || ptrAny(t1,t2) then ValidS
                     else BadS $ (show l) ++ " declared with type " ++ "no" ++ --(show t1) ++ 
                          " assigned with type " ++ "no" --(show t2)
          where ptrAny(t1,t2) = case (t1,t2) of
                  (Pointer _, Pointer Void) -> True
                  _ -> False
                asnStrct t = case t of
                  (Struct _) -> False
                  _ -> True
checkS (AIf e s1 s2) ctx m d t smap =
  case checkE e ctx d smap of
    BadE s -> BadS s
    ValidE Int -> BadS "If condition is not type bool"
    ValidE Bool ->
      case checkS s1 ctx m d t smap of
        BadS s -> BadS s
        ValidS -> checkS s2 ctx m d t smap
checkS (AExpr e s) ctx m d t smap =
  case checkE e ctx d smap of
    BadE s -> BadS s
    ValidE _ -> checkS s ctx m d t smap

lvalType :: LValue -> Context -> Set.Set String -> Map.Map String [Param] -> Maybe Type
lvalType (LIdent i) ctx _ _ = Map.lookup i ctx
lvalType (LDeref l) ctx d smap =
  case lvalType l ctx d smap of
    Nothing -> Nothing
    Just (Pointer t) -> Just t
    _ -> Nothing
lvalType (LArrow l s) ctx d smap =
  case lvalType l ctx d smap of
    Just (Pointer(Struct s1)) -> case Map.lookup s1 smap of
      Just ps -> case List.find (\(Param _ f) -> f == s) ps of
        Just (Param t _) -> Just t
        _ -> Nothing
      _ -> Nothing 
    _ -> Nothing
lvalType (LDot l s) ctx d smap =
  case lvalType l ctx d smap of
    Just (Struct s1) -> case Map.lookup s1 smap of
      Just ps -> case List.find (\(Param _ f) -> f == s) ps of
        Just (Param t _) -> Just t
        _ -> Nothing
      _ -> Nothing
    _ -> Nothing
lvalType (LArray l e) ctx d smap =
  case checkE e ctx d smap of
    ValidE Int ->
      case lvalType l ctx d smap of
        Just (Array t) -> Just t
        Just t -> Just t
        _ -> Nothing
    _ -> Nothing
  
-- Performs static type checking on an expression under a typing context
checkE :: Expr -> Context -> Set.Set String -> Map.Map String [Param] -> CheckE
checkE (ExpInt Dec i _) _ _ _ = if i > (2^31) then BadE "const too large"
                              else ValidE Int
checkE (ExpInt Hex i _) _ _ _ = if i > (2^32 - 1) then BadE "const too large"
                              else ValidE Int
checkE (TrueT _) _ _ _ = ValidE Bool
checkE (FalseT _) _ _ _ = ValidE Bool
checkE (Ident i _) ctx d smap = 
  case Map.lookup i ctx of
    Nothing -> BadE $ i ++ " used undeclared."
    Just t -> ValidE t    
checkE (ExpUnOp op e _) _ _ _ | op == Incr || op == Decr =
  BadE "incr or decr in expression"
checkE (ExpUnOp Deref e _) ctx d smap =
  let
    op = Deref
    ([opT], ret) = opType op
  in case (checkE e ctx d smap) of
    BadE s -> BadE s
    ValidE (Pointer Void) -> BadE "Dereferencing Null"
    ValidE t -> if opT(t) then ValidE $ ret(t)
                else BadE "unop expr mismatch"
checkE (ExpUnOp op e _) ctx d smap =
  let
    ([opT], ret) = opType op
  in case (checkE e ctx d smap) of
    BadE s -> BadE s
    ValidE t -> if opT(t) then ValidE $ ret(t)
                else BadE "unop expr mismatch"
checkE (ExpBinOp Arrow e (Ident s2 _) _) ctx d smap =
  case checkE e ctx d smap of
    BadE s -> BadE s
    ValidE t ->
      case t of
        (Pointer (Struct s)) ->
              case Map.lookup s smap of
                Nothing -> BadE $ "undefined struct " ++ s
                Just fields ->
                  case List.find (\(Param _ fieldName) -> fieldName == s2) fields of
                    Nothing -> BadE $ "field " ++ s2 ++ " undefined in struct " ++ s
                    Just (Param t' _) -> ValidE t'
        _ -> BadE "Invalid exp on LHS of arrow op"
checkE (ExpBinOp Arrow _ _ _) _ _ _ = 
  BadE $ "exp on RHS of arrow op is not identifier."
checkE (ExpBinOp Dot e (Ident s2 _) _) ctx d smap =
  case checkE e ctx d smap of
    BadE s -> BadE s
    ValidE t ->
      case t of
        (Struct i) ->
          case Map.lookup i smap of
            Nothing -> BadE $ "undefined struct " ++ i
            Just fields ->
              case List.find (\(Param _ fieldName) -> fieldName == s2) fields of
                Nothing -> BadE $ "field " ++ s2 ++ " undefined in struct " ++ i
                Just (Param t' _) -> ValidE t'
        _ -> BadE "Invalid exp on LHS of dot op"
checkE (ExpBinOp Dot _ _ _) _ _ _ =
  BadE $ "exp on RHS of dot op is not identifier."
checkE (ExpBinOp op e1 e2 _) ctx d smap =
  if (op == Eq) || (op == Neq) then
    case (checkE e1 ctx d smap, checkE e2 ctx d smap) of
      (BadE s, _) -> BadE s
      (_, BadE s) -> BadE s
      (ValidE t1, ValidE t2) -> case t1 of
        Map l t -> BadE "Cannot compare Function Types"
        Struct _ -> BadE "Cannot compare Structs"
        _ -> case t1 of
          (Pointer Void) -> case t2 of
            (Pointer _) -> ValidE Bool
            _ -> BadE "eq type mismatch2"
          (Pointer _) -> if t1 == t2 || t2 == Pointer Void  then ValidE Bool
                         else BadE "eq type mismatch1"
          _ -> if t1 == t2 then ValidE Bool else BadE "eq type mismatch"
  else
    let
      ([opT1, opT2], ret) = opType op
    in case (checkE e1 ctx d smap, checkE e2 ctx d smap) of
      (BadE s, _) -> BadE s
      (_, BadE s) -> BadE s
      (ValidE t1, ValidE t2) ->
        if opT1(t1) && opT2(t2) then ValidE $ ret(t1)
        else BadE ("binop expr mismatch " ++ (show e1) ++ (show e2) ++ (show op))
checkE (ExpTernOp e1 e2 e3 _) ctx d smap =
  case (checkE e1 ctx d smap, checkE e2 ctx d smap, checkE e3 ctx d smap) of
    (BadE s, _, _) -> BadE s
    (_, BadE s, _) -> BadE s
    (_, _, BadE s) -> BadE s
    (ValidE t1, ValidE t2, ValidE t3) ->
      case (t2, t3) of
        (Struct _,_) -> BadE "Ternary op returns large type"
        (_,Struct _) -> BadE "Ternary op returns large type"
        _ -> case t1 of
          Int -> BadE "cond in ternary op not type bool"
          Bool -> if typeCompare(t2,t3) then ValidE t2
                  else BadE "ternary result type mismatch"
checkE (App fun args _) ctx d smap =
  if Set.notMember fun d then BadE "undefined fun" else
    let
      ts = map (\e -> checkE e ctx d smap) args
      -- TODO better error propagation here
    in case any(\x -> case x of {BadE _ -> True; _ -> False}) ts of
      True -> BadE $ "Error in params to function call " ++ (show fun)
      False -> let ts' = map (\(ValidE t) -> t) ts
               in
                case Map.lookup fun ctx of
                  (Just (Map input output)) ->
                    if length(ts') /= length(input) then BadE "Too many arguments to function call"
                    else if all typeCompare $ zip ts' input then ValidE output
                      else BadE "function input type mismatch"
                  _ -> BadE "undefined function call"
checkE (Null _) ctx d smap =
  ValidE (Pointer Void) -- Placeholder for Type Any
checkE (Alloc t _) ctx d smap =
  case t of
    Void -> BadE "Can't allocate pointer of type void"
    Map _ _ -> BadE "Allocating pointer with function type"
    Struct s -> case Map.lookup s smap of
      Just t' -> ValidE (Pointer (Struct s))
      Nothing -> BadE "Allocating undefined struct"
    _ -> ValidE (Pointer t)
checkE (AllocArray t e _) ctx d smap =
  case checkE e ctx d smap of
    BadE s -> BadE s
    ValidE t1 -> case t1 of
      Int -> case t of
        Map _ _ -> BadE "Allocating array with function type"
        Void -> BadE "Allocating array with void type"
        Struct s -> case Map.lookup s smap of
          Nothing -> BadE "Struct definition not in map (checkE(Alloc...))"
          Just t' -> ValidE (Array (Struct s))
        _ -> ValidE (Array t)
      _ -> BadE "size for alloc_array not int"
checkE (Subscr e1 e2 _) ctx d smap = 
  case (checkE e1 ctx d smap, checkE e2 ctx d smap) of
    (ValidE t1, ValidE t2) -> case t2 of
      Int -> case t1 of
        Array t3 -> ValidE t3
        _ -> BadE "Cannot subscript non-array type"
      _ -> BadE "Subscript of array not of type int"
    (BadE s, _) -> BadE s

typeCompare (Pointer Void, Pointer _) = True
typeCompare (Pointer _, Pointer Void) = True
typeCompare (t1, t2) = t1 == t2

getIdent s (LIdent i) (LIdent _) = Right i
getIdent s (LIdent i) _ =
  case Set.member i s of
    True -> Left $ "unitialized variable " ++ i
    False -> Right i
getIdent s (LDeref l) l' = getIdent s l l'
getIdent s (LArrow l _) l' = getIdent s l l'
getIdent s (LDot l _) l' = getIdent s l l'
getIdent s (LArray l e) l' = getIdent s l l'

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
checkInit (AAssign l e) (live, defn) = 
  case checkLive (uses e) live of
    True -> Left $ "Undeclared variable on RHS of define for " ++ (show l)
    False -> let
      i' = getIdent live l l
      in case i' of
        Left s -> Left s
        Right i -> Right $ (Set.delete i live, Set.insert i defn)
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
uses (ExpBinOp Arrow e _ _) = uses e
uses (ExpBinOp Dot e _ _) = uses e
uses (ExpBinOp _ e1 e2 _) = Set.union (uses e1) (uses e2)
uses (ExpTernOp e1 e2 e3 _) = Set.unions [uses e1, uses e2, uses e3]
uses (App _ es _) = Set.unions (map uses es)
uses (Subscr e1 e2 _) = Set.union (uses e1) (uses e2)
uses (Alloc _ _) = Set.empty
uses (AllocArray _ e _) = uses e
uses _ = Set.empty
