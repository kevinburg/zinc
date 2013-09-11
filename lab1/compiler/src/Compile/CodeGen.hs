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
  decls = getDecls stmts
  temps = Map.fromList $ zip (map declName decls) [0..]
  aasm = concatMap (genStmt (temps, (length decls))) stmts
  -- compute register mapping
  regMap = allocateRegisters aasm
  aasm' = concatMap (translate regMap) aasm
  in aasm'

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

-- begin 'temp -> register' translation
translate regMap (AAsm {aAssign = [dest], aOp = Nop, aArgs = [src]}) =
  [Movl (regFind regMap src) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Add, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
  in
    [Movl (regFind regMap src1) dest',
     Addl (regFind regMap src2) dest']
translate regMap (AAsm {aAssign = [dest], aOp = Sub, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
  in
    [Movl (regFind regMap src1) dest',
     Subl (regFind regMap src2) dest']
translate regMap (AAsm {aAssign = [dest], aOp = Neg, aArgs = [src]}) =
  let
    dest' = regFind regMap (ALoc dest)
  in
    [Movl (Val 0) dest',
     Subl (regFind regMap src) dest']
translate regMap (ACtrl Ret (ALoc loc)) =
  [AsmRet]

regFind :: Map.Map AVal Arg -> AVal -> Arg
regFind regMap (AImm i) = Val i
regFind regMap aloc = 
  case Map.lookup aloc regMap of
    Just (reg) -> reg
    Nothing -> Reg EAX
