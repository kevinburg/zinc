{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Currently just a pseudolanguage with 3-operand instructions and arbitrarily many temps.
-}
module Compile.CodeGen where

import Compile.Types
import Compile.RegAlloc
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

codeGen :: AST -> [Asm]
codeGen (Block stmts pos) = let
  s = foldr (\x -> \y -> (show x) ++ "\n" ++ y) "\n" stmts
  --temps = Map.fromList $ zip (map declName decls) [0..]
  (aasm, _, _) = foldl (\acc -> \stmt -> genStmt acc stmt) 
                 ([], Map.empty, 0) stmts
  -- compute register mapping
  prgm = foldr (\x -> \y -> (show x) ++ "\n" ++ y) "" aasm
  regMap = allocateRegisters aasm
  aasm' = concatMap (translate regMap) aasm
  in aasm'

-- aasm generating functions
genStmt (stmts, temps, n) (Return e _) = let
  (stmt, n') = genExp (temps, n) e (AReg 0)
  in (stmts ++ stmt ++ [ACtrl Ret (ALoc (AReg 0))], temps, n')
genStmt (stmts, temps, n) (Asgn v o e s) = let
  l = ATemp n
  temps' = Map.insert v n temps
  e' = case o of
    Nothing -> e
    Just op -> 
      ExpBinOp op (Ident v s) e s
  (stmt, n') = genExp (temps, n+1) e' l
  in (stmts ++ stmt, temps', n')
genStmt state (Decl _ Nothing _) = state
genStmt (stmts, temps, n) (Decl v (Just e) _) = let
  l = ATemp n
  temps' = Map.insert v n temps
  (stmt, n') = genExp (temps, n+1) e l
  in (stmts ++ stmt, temps', n')

genExp :: Alloc -> Expr -> ALoc -> ([AAsm], Int)
genExp (_,n) (ExpInt i _) l = ([AAsm [l] Nop [AImm $ fromIntegral i]], n)
genExp (a,n) (Ident s _) l = ([AAsm [l] Nop [ALoc $ ATemp $ a Map.! s]], n)
genExp (a,n) (ExpBinOp op e1 e2 _) l = let
  (i1, n') = genExp (a, n + 1) e1 (ATemp n)
  (i2, n'') = genExp (a, n' + 1) e2 (ATemp $ n')
  c  = [AAsm [l] op [ALoc $ ATemp n, ALoc $ ATemp $ n']]
  in (i1 ++ i2 ++ c, n'')
genExp (a,n) (ExpUnOp op e _) l = let
  (i1, n') = genExp (a, n + 1) e (ATemp n)
  c  = [AAsm [l] op [ALoc $ ATemp n]]
  in (i1 ++ c, n')

-- begin 'temp -> register' translation
translate regMap (AAsm {aAssign = [dest], aOp = Nop, aArgs = [src]}) =
  [Movl (regFind regMap src) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Add, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
  in
   if s == dest' then
     [Movl s dest',
      Addl (regFind regMap src2) dest']
   else
     [Movl (regFind regMap src2) dest',
      Addl s dest']
translate regMap (AAsm {aAssign = [dest], aOp = Sub, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s2 = regFind regMap src2
  in
   if s2 == dest' then
     [Negl s2,
      Addl (regFind regMap src1) s2] 
   else
     [Movl (regFind regMap src1) dest',
      Subl s2 dest']
translate regMap (AAsm {aAssign = [dest], aOp = Mul, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
  in
   if s == dest' then
     [Movl s dest',
      Imull (regFind regMap src2) dest']
   else
     [Movl (regFind regMap src2) dest',
      Imull s dest']
translate regMap (AAsm {aAssign = [dest], aOp = Div, aArgs = [src1, src2]}) =
  [Movl (regFind regMap src1) (Reg EAX),
   Movl (Val 0) (Reg EDX),
   Idivl (regFind regMap src2),
   Movl (Reg EAX) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Mod, aArgs = [src1, src2]}) =
  [Movl (regFind regMap src1) (Reg EAX),
   Movl (Val 0) (Reg EDX),
   Idivl (regFind regMap src2),
   Movl (Reg EDX) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Neg, aArgs = [src]}) =
  let
    dest' = regFind regMap (ALoc dest)
  in
    [Movl (regFind regMap src) dest',
     Negl dest']
translate regMap (ACtrl Ret (ALoc loc)) =
  [AsmRet]

regFind :: Map.Map AVal Arg -> AVal -> Arg
regFind regMap (AImm i) = Val i
regFind regMap aloc = 
  case Map.lookup aloc regMap of
    Just (reg) -> reg
    Nothing -> Reg EAX
