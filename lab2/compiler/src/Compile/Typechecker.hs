module Compile.Typechecker where

import Compile.Types
import qualified Data.Map as Map
import Debug.Trace

data CheckS = ValidS (Map.Map String ())
            | BadS String
              
data CheckE = ValidE Type
            | BadE String

type Context = (Map.Map String Type, Map.Map String ())

-- Somebody should probably test this module.

checkS :: S -> Context -> CheckS
checkS ANup (_, defn) = ValidS defn
checkS (ASeq s1 s2) (decl, defn) = 
  case checkS s1 (decl, defn) of 
    BadS s -> BadS s
    ValidS defn1 -> checkS s2 (decl, defn1)
checkS (ADeclare i t s) (decl, defn) =
  case Map.lookup i decl of
    Just _ -> BadS $ "Redeclaring " ++ i
    Nothing -> checkS s (Map.insert i t decl, defn)
checkS (AReturn e) (decl, defn) = 
  case checkE e (decl, defn) of
    BadE s -> BadS s
    ValidE Bool -> BadS "Main returns type bool"
    ValidE Int -> ValidS defn
checkS (AWhile e s) ctx = 
  case checkE e ctx of
    BadE s -> BadS s
    ValidE Int -> BadS "While condition is not type bool"
    ValidE Bool -> checkS s ctx
checkS (AAssign i e) (decl, defn) =
  case Map.lookup i decl of
    Nothing -> BadS $ "Assigning " ++ i ++ " undeclared"
    Just t1 ->
      case checkE e (decl, defn) of
        BadE s -> BadS s
        ValidE t2 -> if t1 == t2 then ValidS (Map.insert i () defn)
                    else BadS $ i ++ " declared with type " ++ (show t1) ++ 
                         " assigned with type " ++ (show t2)
checkS (AIf e s1 s2) (decl, defn) =
  case checkE e (decl, defn) of
    BadE s -> BadS s
    ValidE Int -> BadS "If condition is not type bool"
    ValidE Bool ->
      case checkS s1 (decl, defn) of
        BadS s -> BadS s
        ValidS defn1 -> checkS s2 (decl, defn1)
  
checkE :: Expr -> Context -> CheckE
checkE (ExpInt _ _ _) _ = ValidE Int
checkE (TrueT _) _ = ValidE Bool
checkE (FalseT _) _ = ValidE Bool