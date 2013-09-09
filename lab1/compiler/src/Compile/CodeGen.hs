{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Currently just a pseudolanguage with 3-operand instructions and arbitrarily many temps.
-}
module Compile.CodeGen where

import Compile.Types
import qualified Data.Map as Map
import qualified Data.Set as Set

import Debug.Trace

type Alloc = (Map.Map String Int, Int)

declName (Decl name _ _) = name

getDecls y = filter pred y
             where
               pred = (\x -> case x of
                          (Decl _ _ _) -> True
                          _ -> False
                      )

addNewInter (ALoc loc) s =
  Set.map (\x -> (ALoc loc, x)) s
addNewInter (AImm _) s = 
  Set.empty

isTemp (ALoc _) = True
isTemp _ = False

{- Generates a list of temp variables/registers that interfere.
   Will only work for L1 programs.
-}
genInter [] _ inter = inter
genInter (stmt : aasm) l inter =
  case stmt of
    ACtrl Ret loc -> 
      let
        newInter = addNewInter loc l
        l' = Set.insert loc l
        inter' = Set.union inter newInter
      in genInter aasm l' inter'
    -- only have single dest instructions
    AAsm {aAssign = [dest], aOp = _, aArgs = srcs} ->
      let
        l' = Set.delete (ALoc dest) l
        newInters = addNewInter (ALoc dest) l'
        inter' = Set.union inter newInters
        live = Set.union (Set.fromList (filter isTemp srcs))  l'
      in genInter aasm live inter'

codeGen :: AST -> [AAsm]
codeGen (Block stmts pos) = let
  decls = getDecls stmts
  temps = Map.fromList $ zip (map declName decls) [0..]
  aasm = concatMap (genStmt (temps, (length decls))) stmts
  -- compute interference graph
  inter = Set.filter (\(x,y) -> x /= y) $ 
          genInter (reverse aasm) Set.empty Set.empty
  -- move register allocation to its own module??
  in trace (show inter) aasm

-- aasm generating functions
genStmt :: Alloc -> Stmt -> [AAsm]
genStmt alloc (Return e _) = (genExp alloc e (AReg 0)) ++ 
                              [ACtrl Ret (ALoc (AReg 0))]
genStmt (a,n) (Asgn v o e s) = let
  l = ATemp $ a Map.! v
  e' = case o of
         Nothing -> e
         Just op -> ExpBinOp op (Ident v s) e s
  in genExp (a,n) e' l
genStmt (a,n) (Decl i Nothing p) = []
genStmt (a,n) (Decl i (Just e) p) = let
  l = ATemp $ a Map.! i
  in genExp (a,n) e l

genExp :: Alloc -> Expr -> ALoc -> [AAsm]
genExp _ (ExpInt n _) l = [AAsm [l] Nop [AImm $ fromIntegral n]]
genExp (a,_) (Ident s _) l = [AAsm [l] Nop [ALoc $ ATemp $ a Map.! s]]
genExp (a,n) (ExpBinOp op e1 e2 _) l = let
  i1 = genExp (a, n + 1) e1 (ATemp n)
  i2 = genExp (a, n + 2) e2 (ATemp $ n + 1)
  c  = [AAsm [l] op [ALoc $ ATemp n, ALoc $ ATemp $ n + 1]]
  in i1 ++ i2 ++ c
genExp (a,n) (ExpUnOp op e _) l = let
  i1 = genExp (a, n + 1) e (ATemp n)
  c  = [AAsm [l] op [ALoc $ ATemp n]]
  in i1 ++ c
