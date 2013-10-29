module Compile.Elaborate where

import Compile.Types
import qualified Data.Map as Map
import qualified Data.Set as Set

import Debug.Trace
import Compile.CheckAST

elaborate :: Program -> Either String
             (Map.Map String Type, [(String,
                                   (Type, [Param], S, Map.Map String Type,
                                    Map.Map String (Type, [Type])))],
              Map.Map String [Param])
elaborate (Program gdecls) =
  case partProgram gdecls (Map.singleton "fpt" Int, Map.empty, [], Map.empty) of
    Left err -> Left err
    Right (typedef, fdecl, fdefn, sdefn) -> let
      res = map (\(key,(t, p, Block b _, t1, t2)) -> (key,(t, p, elaborate' b, t1, t2))) fdefn
      --smap = Map.unions $ map (\(k, p)-> Map.unions $ map (\(Param t s) -> Map.insert (k,s) t Map.empty) p) $ Map.toList sdefn
      sdefn' = Map.map (\x -> map (\(Param t s) ->Param (pType(t,typedef)) s) x) sdefn
        where pType(Type s,typedef) = typedef Map.! s
              pType(Pointer t, typedef) = Pointer(pType(t,typedef))
              pType(Array t,_) = Array(pType(t,typedef))
              pType(t,_) = t
      in case foldr
              (\(key, val) -> \acc ->
                case (acc, val) of
                  (Left s, _) -> Left s
                  (_, (_, _, Left s, _, _)) -> Left s
                  (Right m, (t, p, Right val', a, b)) ->
                    Right $ (key,(t, p, val', a, b)) : m) (Right []) res of
           Left s -> Left s
           Right m -> Right (typedef, m, sdefn')

partProgram [] acc = Right acc
partProgram ((TypeDef t s _) : xs) (typedef, fdecl, fdefn, sdefn) =
  if t == Void then Left "loser" else
  (case Map.lookup s typedef of
      (Just _) -> Left $ "Type names may be defined only once - " ++ s
      _ -> Right ()) >>= \_ ->
  (case (Map.lookup s fdecl, lookup s fdefn) of
      (Nothing, Nothing) -> Right ()
      _ -> Left $ "Typedef " ++ s ++ " collides with function decl") >>= \_ ->
  partProgram xs (Map.insert s t typedef, fdecl, fdefn, sdefn)
partProgram ((FDecl t s p _) : xs) (typedef, fdecl, fdefn, sdefn) =
  (let
      ps = map (\(Param _ name) -> name) p 
   in if any (\x -> Map.member x typedef) ps then Left "bleh" else Right ()) >>= \_ ->
{-  (let
      pt = map (\(Param t _) -> t) p
      pt' = filter (\x -> case x of {Type s -> True; _ -> False}) pt
   in if any (\(Type s) -> not (Map.member s typedef)) pt' then Left "Type unknown" else Right()) >> \_ -> -}
  case check (t, s, p) (typedef, fdecl, fdefn) of
    Left err -> Left err
    Right () -> partProgram xs (typedef, Map.insert s (t, typeFromParams p) fdecl, fdefn, sdefn)
partProgram ((FDefn t s p b _) : xs) (typedef, fdecl, fdefn, sdefn) =
  (let
      ps = map (\(Param _ name) -> name) p
   in if any (\x -> Map.member x typedef) ps then Left "bleh" else Right ()) >>= \_ ->
{-  (let
      pt = map (\(Param t _) -> t) p
      pt' = filter (\x -> case x of {Type s -> True; _ -> False}) pt
   in if any (\(Type s) -> not (Map.member s typedef)) pt' then Left "Type unknown" else Right()) >> \_ -> -}
  (case lookup s fdefn of
      (Just _) -> Left $ "Multiple definitions of function " ++ s
      Nothing -> Right ()) >>= \_ ->
  (case elem s ["fadd","fsub","fmul","fdiv","fless","itof","ftoi",
                "print_fpt","print_int","print_hex"] of
     True -> Left "defining external function"
     False -> Right ()) >>= \_ ->
  case check (t, s, p) (typedef, fdecl, fdefn) of
    Left err -> Left err
    Right () -> partProgram xs (typedef, fdecl, (s, (t,p,b,typedef,fdecl)) : fdefn, sdefn)
partProgram ((SDecl _ _) : xs) acc =
  partProgram xs acc
partProgram ((SDefn s f _) : xs) (typedef, fdecl, fdefn, sdefn) =
  (let
      fieldList = map (\(Param _ i) -> i) f
      fieldSet = Set.fromList fieldList
   in case (length fieldList) == (Set.size fieldSet) of
     True -> Right ()
     False -> Left $ "Struct " ++ s ++ " contains duplicate field names.") >>= \_ ->
  (case Map.lookup s sdefn of
      Nothing -> Right ()
      Just fs -> Left $ "Struct " ++ s ++ " defined more than once.") >>= \_ ->
  (let
      sts = filter (\(Param t i) -> case t of {Struct s -> True; _->False}) f
      sts' = map (\(Param (Struct s) i) -> (Map.lookup s sdefn, s)) sts
   in
    case foldl(\(x,a)-> \(y,b)->case (x,y) of (Nothing, _)->(Nothing,a)
                                              (_,Nothing)->(Nothing,b)
                                              (Just t,_)->(Just t,a)) (Just Int,"asdf") sts' of
      (Nothing,a) -> Left $ "Struct "++a++" used but not defined."
      (Just _, _) -> Right ()) >>= \_ ->
  partProgram xs (typedef, fdecl, fdefn, Map.insert s f sdefn)

check (t, s, p) (typedef, fdecl, fdefn) = 
  (case t of
      Type s' ->
        case Map.lookup s' typedef of
          (Just t') -> Right ()
          Nothing -> Left $ "Type " ++ s' ++ " not found"
      _ -> Right ()) >>= \_ ->
  (case Map.lookup s typedef of
      (Just _) -> Left $ "Function decl/defn " ++ s ++ " collides with typedef"
      Nothing -> Right ()) >>= \_ ->
  (case Map.lookup s fdecl of
      (Just (t', p')) ->
        case (typeEq typedef (t,t')) &&
             length(p) == length(p') &&
             (all (typeEq typedef) $ zip p' $ typeFromParams p) of
          False -> 
            Left $ "Function decl/defn conflicts with previous decl/defn"
          True -> Right ()
      Nothing -> Right ()) >>= \_ ->
  (let
      pt = filter (\x -> case x of {x|x==Bool || x==Int -> False; _ -> True}) $ typeFromParams p
      pt' = map pType pt
        where pType t = case t of
                Type s -> Map.notMember s typedef
                Struct s -> False -- False for implicit struct declaration? maybe? --Map.notMember s typedef
                Pointer t' -> pType t'
                Array t' -> pType t'
                Int -> False
                Bool -> False
                Void -> False
                _ -> True
   in
    case any (\x -> x) pt' of
      True -> Left $ "Parameter type unknown for function " ++ s ++ "."
      _ -> Right ()) >>= \_ ->
  (let
      pt = filter(\x -> case x of {x|x==Bool||x==Int -> False; _ -> True}) $ typeFromParams p
      pt' = map pType pt
        where pType t = case t of
                Struct s -> True
                Type s -> case Map.lookup s typedef of
                  Just t' -> case t' of
                    Struct _ -> True
                    _ -> False
                  _ -> False
                _ -> False
   in
    case any (\x -> x) pt' of
      True -> Left $ "Parameter not of small type."
      _ -> Right ()) >>= \_ -> 
  case lookup s fdefn of
    (Just (t', p', _, _, _)) ->
      case (typeEq typedef (t, t')) &&
           length(p) == length(p') &&
           (all (typeEq typedef) $ zip (typeFromParams p') $ typeFromParams p) of
        False -> Left "Function decl/defn conflicts with previous decl/defn"
        True -> Right ()
    Nothing -> Right ()

typeFromParams l = map (\(Param t _) -> t) l 

elaborate' [] = Right ANup
elaborate' ((Simp (Decl t i Nothing _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right (ADeclare i t s)
elaborate' ((Simp (Decl t i (Just e) p) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s ->
      case contained i e of
        True -> Left ("Recursive declaration of " ++ (show i))
        False -> Right $ ADeclare i t (ASeq (AAssign (LIdent i) e) s)
elaborate' ((Simp (Asgn l Nothing e _)_) : xs)  =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssign l e) s
elaborate' ((Simp (Asgn l (Just op) e2 p) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> let
      e1 = unwrap l p
      in Right $ ASeq (AAssign l (ExpBinOp op e1 e2 p)) s
elaborate' ((Simp (PostOp o l _) p) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> let
      e1 = unwrap l p in
      case o of 
        Incr -> Right $ ASeq (AAssign l (ExpBinOp Add e1 (ExpInt Dec 1 p) p)) s
        Decr -> Right $ ASeq (AAssign l (ExpBinOp Sub e1 (ExpInt Dec 1 p) p)) s
elaborate' ((Simp (Expr (ExpUnOp Fail _ _) _)_): xs) = Left  "bad prefix op"
elaborate' ((Simp (Expr e p)_): xs) = 
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ AExpr e s
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
    Just (Decl _ _ _ _) -> Left "step in for loop is decl"
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
              Right $ ASeq (ADeclare i t (ASeq (AAssign (LIdent i) e')
                                          (AWhile exp (ASeq body step)))) s
elaborate' ((Ctrl (For s1 exp s2 s3 _) p) : xs) =
  case s2 of
    Just (Decl _ _ _ _) -> Left "step in for loop is decl"
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
elaborate' ((Ctrl (Assert e _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> Right $ ASeq (AAssert e) s
-- BLOCK STMTs --
elaborate' ((BlockStmt (Block l _) _) : xs) =
  case elaborate' xs of
    Left s -> Left s
    Right s -> case elaborate' l of
      Left s' -> Left s'
      Right s' -> Right $ ABlock s' s

unwrap (LIdent i) p = Ident i p
unwrap (LArrow l i) p = let
  l' = unwrap l p
  in ExpBinOp Arrow (Ident i p) l' p
unwrap (LDot l i) p = let
  l' = unwrap l p
  in ExpBinOp Dot (Ident i p) l' p
unwrap (LDeref l) p = let
  l' = unwrap l p
  in ExpUnOp Deref l' p
unwrap (LArray l e) p = let
  l' = unwrap l p
  in Subscr l' e p

-- extremely special case function
mList Nothing _ = []
mList (Just x) p = [Simp x p]
    
contained :: String -> Expr -> Bool
contained i (Ident x _) = i == x
contained i (ExpUnOp _ e _) = contained i e
contained i (ExpBinOp Arrow e _ _) = contained i e
contained i (ExpBinOp Dot e _ _) = contained i e
contained i (ExpBinOp _ e1 e2 _) = contained i e1 || contained i e2
contained i (ExpTernOp e1 e2 e3 _) = contained i e1 || contained i e2 || contained i e3
contained _ _ = False
