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

codeGen :: Program -> [Asm]
codeGen (Program (Block stmts _)) =
  let
    aasm = genStmt ([], 0, 0) stmts
  in trace (show aasm) []

-- updates the abstract assembly at a label
update aasm Nothing = Just aasm
update aasm (Just acc) = Just $ acc ++ aasm

updatePre aasm Nothing = Just aasm
updatePre aasm (Just acc) = Just $ aasm ++ acc
     
genStmt acc [] = acc
genStmt acc ((Simp (Decl _ _ Nothing _) _) : xs) = genStmt acc xs
genStmt (acc, n, l) ((Simp (Decl _ i (Just e) _) _) : xs) =
  let
    (aasm, n', l') = genExp (n, l) e (AVar i)
  in genStmt (acc ++ aasm, n', l') xs
genStmt (acc, n, l) ((Simp (Asgn i o e s) _) : xs) = 
  let
    e' = case o of
      Nothing -> e
      Just op -> ExpBinOp op (Ident i s) e s
    (aasm, n', l') = genExp (n, l) e' (AVar i)
  in genStmt (acc ++ aasm, n', l') xs
genStmt (acc, n, l) ((Simp (PostOp o (Ident i _) s) _) : xs) =
  let
    op = case o of
      Incr -> Add
      Decr -> Sub
    e' = ExpBinOp op (Ident i s) (ExpInt Dec 1 s) s
    (aasm, n', l') = genExp (n, l) e' (AVar i)
  in genStmt (acc ++ aasm, n', l') xs
genStmt (acc, n, l) ((Simp (Expr e _) _) : xs) = 
  let
    (aasm, n', l') = genExp (n + 1, l) e (ATemp n)
  in genStmt (acc ++ aasm, n', l') xs
genStmt acc ((BlockStmt (Block stmts _) _) : xs) = genStmt acc stmts
genStmt (acc, n, l) ((Ctrl (Return e _) _) : xs) =
  let
    (aasm, n', l') = genExp (n, l) e (AReg 0)
  in (acc ++ aasm ++ [ACtrl $ Ret (ALoc $ AReg 0)], n', l')
genStmt (acc, n, l) ((Ctrl (If e s Nothing _) _) : xs) =        
  let
    (aasme, n', l') = genExp (n + 1, l) e (ATemp n)
    (aasms, n'', l'') = genStmt ([], n', l') [s] 
    aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l''+1),
            ACtrl $ Goto (show $ l''+2),
            ACtrl $ Lbl (show $ l''+1)]
    aasm' = aasme ++ aasm ++ aasms ++
            [ACtrl $ Goto (show $ l''+2), ACtrl $ Lbl (show $ l''+2)]
  in genStmt (acc ++ aasm', n'', l''+2) xs
genStmt (acc, n, l) ((Ctrl (If e s1 (Just s2) _) _) : xs) =
   let
    (aasme, n1, l1) = genExp (n+1, l) e (ATemp n)
    (aasms1, n2, l2) = genStmt ([], n1, l1) [s1] 
    (aasms2, n3, l3) = genStmt ([], n2, l2) [s2] 
    aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l3+2),
            ACtrl $ Goto (show $ l3+1),
            ACtrl $ Lbl (show $ l3+1)]
    aasm' = aasme ++ aasm ++ aasms1 ++
            [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+2)] ++
            aasms2 ++ [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+3)]
  in genStmt (acc ++ aasm', n3, l3+3) xs
genStmt (acc, n, l) ((Ctrl (While e s _) _) : xs) =
  let
    (aasme, n1, l1) = genExp (n+1, l) e (ATemp n)
    (aasms, n2, l2) = genStmt ([], n1, l1) [s]
    aasm = [ACtrl $ Lbl (show $ l2+1),
            ACtrl $ Ifz (ALoc (ATemp n)) (show $ l2+3),
            ACtrl $ Goto (show $ l2+2),
            ACtrl $ Lbl (show $ l2+2)]
    aasm' = aasme ++ aasm ++ aasms ++
            [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+3)]
  in genStmt (acc ++ aasm', n2, l2+3) xs
    
genExp :: (Int, Int) -> Expr -> ALoc -> ([AAsm], Int, Int)
genExp (n,l) (ExpInt _ i _) loc = ([AAsm [loc] Nop [AImm $ fromIntegral i]], n, l)
genExp (n,l) (TrueT _) loc = ([AAsm [loc] Nop [AImm 1]], n, l)
genExp (n,l) (FalseT _) loc = ([AAsm [loc] Nop [AImm 0]], n, l)
genExp (n,l) (Ident s _) loc = ([AAsm [loc] Nop [ALoc $ AVar s]], n, l)
genExp (n,l) (ExpBinOp op e1 e2 _) loc = let
  (i1, n', l') = genExp (n + 1, l) e1 (ATemp n)
  (i2, n'', l'') = genExp (n' + 1, l') e2 (ATemp n')
  aasm  = [AAsm [loc] op [ALoc $ ATemp n, ALoc $ ATemp $ n']]
  in (i1 ++ i2 ++ aasm, n'', l'')
genExp (n,l) (ExpUnOp op e _) loc = let
  (i1, n', l') = genExp (n + 1, l) e (ATemp n)
  aasm = [AAsm [loc] op [ALoc $ ATemp n]]
  in (i1 ++ aasm, n', l')
     
{-
genExp (n, l) (ExpTernOp e1 e2 e3 _) loc = let
  (i1, n', l') = genExp (acc, n+1, l) e1 (ATemp n)
  aasm1 =  [Actrl $ ALoc (ATemp n) $ Ifz ("else" ++ (show l))]
  i1' = Map.alter (update aasm1) l' i1
  (i2, n'', l'') = genExp (i1', n'+1, l') e1 (ATemp n')
  aasm2 = [AAsm [l] Nop [ALoc $ ATemp n'],
           Goto (show $ l'''+1)]
  i2' = Map.alter (update aasm2) l'' i2
  (i3, n''', l''') = genExp (i2, n''+1, l'') e1 (ATemp n'')
  aasm3 = [AAsm [l] Nop [ALoc $ ATemp n'']]
  i3' = Map.alter (update aasm3) l''' i3
  in (i3', n''', l'''+1 )
-}

     
{-
-- begin 'temp -> register' translation
translate regMap (AAsm {aAssign = [dest], aOp = Nop, aArgs = [src]}) =
  let
    s = regFind regMap src
  in
   case s of
     (Stk _) ->
       [Movl s (Reg R15D),
        Movl (Reg R15D) (regFind regMap (ALoc dest))]
     _ ->
       [Movl (regFind regMap src) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Add, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (s, s2) of
     (Stk _, _) ->
       [Movl s (Reg R15D),
        Addl (regFind regMap src2) (Reg R15D),
        Movl (Reg R15D) dest']
     (_, Stk _) ->
        [Movl s2 (Reg R15D),
        Addl s (Reg R15D),
        Movl (Reg R15D) dest']
     _ ->
       if s == dest' then
         [Movl s dest',
          Addl (regFind regMap src2) dest']
       else
         [Movl (regFind regMap src2) dest',
          Addl s dest']
translate regMap (AAsm {aAssign = [dest], aOp = Sub, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (s, s2) of
     _ ->
       if s2 == dest' then
         [Negl s2,
          Movl s (Reg R15D),
          Addl (Reg R15D) s2] 
       else
         [Movl s (Reg R15D),
          Movl (Reg R15D) dest',
          Movl s2 (Reg R15D),
          Subl (Reg R15D) dest']
translate regMap (AAsm {aAssign = [dest], aOp = Mul, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (s, s2) of
     (Stk _, _) ->
       [Movl s (Reg R15D),
        Imull (regFind regMap src2) (Reg R15D),
        Movl (Reg R15D) dest']
     (_, Stk _) ->
        [Movl s2 (Reg R15D),
        Imull s (Reg R15D),
        Movl (Reg R15D) dest']
     _ ->
       if s == dest' then
         [Movl s dest',
          Imull (regFind regMap src2) dest']
       else
         [Movl (regFind regMap src2) dest',
          Imull s dest']
translate regMap (AAsm {aAssign = [dest], aOp = Div, aArgs = [src1, src2]}) =
  [Movl (regFind regMap src1) (Reg EAX),
   Cdq,
   Idivl (regFind regMap src2),
   Movl (Reg EAX) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Mod, aArgs = [src1, src2]}) =
  [Movl (regFind regMap src1) (Reg EAX),
   Cdq,
   Idivl (regFind regMap src2),
   Movl (Reg EDX) (regFind regMap (ALoc dest))]
translate regMap (AAsm {aAssign = [dest], aOp = Neg, aArgs = [src]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src
  in
   case (s, dest') of
     (Stk _, Stk _) ->
       [Movl s (Reg R15D),
        Movl (Reg R15D) dest',
        Negl dest']
     _ ->
       [Movl (regFind regMap src) dest',
        Negl dest']
translate regMap (ACtrl Ret (ALoc loc)) =
  [Pop (Reg RBP), AsmRet]

regFind :: Map.Map AVal Arg -> AVal -> Arg
regFind regMap (AImm i) = Val i
regFind regMap aloc = 
  case Map.lookup aloc regMap of
    Just (reg) -> reg
    Nothing -> Reg EAX
-}
