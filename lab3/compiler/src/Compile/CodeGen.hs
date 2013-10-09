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

import Compile.SSA

codeGen :: Program -> [Asm]
codeGen (Program gdecls) =
  let
    fdefns = concatMap (\x -> case x of
                           (FDefn _ s p (Block b _) _) -> [(s,p,b)]
                           _ -> []) gdecls
    res = map (\f -> genFunction f) fdefns
{-
    s = ssa aasm
    unssa = deSSA s
    regMap = allocateRegisters unssa -- TODO: this function needs to get the de-SSA aasm
    code = concatMap (translate regMap) unssa
-}
  in
   trace (show res) []

genFunction (s,p,b) =
  let
    (aasm, _, _) = genStmt ([], length(p), 0, -1) b
    p' = zip (map (\(Param _ i) -> i) p) [0..]
    prefix = map (\(i, n) ->
                   AAsm {aAssign = [AVar i], aOp = Nop, aArgs = [ALoc $ AArg n]}) p'
  in (s, prefix ++ aasm)

-- updates the abstract assembly at a label
update aasm Nothing = Just aasm
update aasm (Just acc) = Just $ acc ++ aasm

updatePre aasm Nothing = Just aasm
updatePre aasm (Just acc) = Just $ aasm ++ acc
     
genStmt acc [] = acc
genStmt acc ((Simp (Decl _ _ Nothing _) _) : xs) = genStmt acc xs
genStmt (acc, n, l, ep) ((Simp (Decl _ i (Just e) _) _) : xs) =
  let
    (aasm, n', l') = genExp (n, l) e (AVar i)
  in genStmt (acc ++ aasm, n', l', ep) xs
genStmt (acc, n, l, ep) ((Simp (Asgn i o e s) _) : xs) = 
  let
    e' = case o of
      Nothing -> e
      Just op -> ExpBinOp op (Ident i s) e s
    (aasm, n', l') = genExp (n, l) e' (AVar i)
  in genStmt (acc ++ aasm, n', l', ep) xs
genStmt (acc, n, l, ep) ((Simp (PostOp o (Ident i _) s) _) : xs) =
  let
    op = case o of
      Incr -> Add
      Decr -> Sub
    e' = ExpBinOp op (Ident i s) (ExpInt Dec 1 s) s
    (aasm, n', l') = genExp (n, l) e' (AVar i)
  in genStmt (acc ++ aasm, n', l') xs
genStmt (acc, n, l, ep) ((Simp (Expr e _) _) : xs) = 
  let
    (aasm, n', l') = genExp (n + 1, l) e (ATemp n)
  in genStmt (acc ++ aasm, n', l', ep) xs
genStmt (acc, n, l, ep) ((BlockStmt (Block stmts _) _) : xs) = 
  let
    (aasm, n', l', ep') = genStmt ([], n, l, ep) stmts
  in genStmt (acc ++ aasm, n', l', ep') xs
genStmt (acc, n, l, ep) ((Ctrl (Return (Just e) _) _) : xs) =
  let
    (aasm, n', l') = genExp (n, l) e (ARes)
    (epilogue, l'') = if ep > 0 then (ep, l') else (l'+1, l'+1)
  in (acc ++ aasm ++ [ACtrl $ Goto (show epilogue)], n', l'', epilogue)
genStmt (acc, n, l, ep) ((Ctrl (If e s Nothing _) _) : xs) =
  let
    (aasme, n', l') = genExp (n + 1, l) e (ATemp n)
    (aasms, n'', l'', ep') = genStmt ([], n', l', ep) [s] 
    aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l''+2),
            ACtrl $ Goto (show $ l''+1),
            ACtrl $ Lbl (show $ l''+1)]
    aasm' = aasme ++ aasm ++ aasms ++
            [ACtrl $ Goto (show $ l''+2), ACtrl $ Lbl (show $ l''+2)]
  in genStmt (acc ++ aasm', n'', l''+2, ep') xs
genStmt (acc, n, l, ep) ((Ctrl (If e s1 (Just s2) _) _) : xs) =
  case e of
   (TrueT _) -> genStmt (acc, n, l) (s1 : xs) 
   (FalseT _) -> genStmt (acc, n, l) (s2 : xs)
   _ -> let
     (aasme, n1, l1) = genExp (n+1, l) e (ATemp n)
     (aasms1, n2, l2, ep2) = genStmt ([], n1, l1, ep) [s1] 
     (aasms2, n3, l3, ep3) = genStmt ([], n2, l2) [s2] 
     aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l3+2),
             ACtrl $ Goto (show $ l3+1),
             ACtrl $ Lbl (show $ l3+1)]
     aasm' = aasme ++ aasm ++ aasms1 ++
             [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+2)] ++
             aasms2 ++ [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+3)]
     in genStmt (acc ++ aasm', n3, l3+3) xs
genStmt (acc, n, l) ((Ctrl (While e s _) _) : xs) =
  case e of
    (FalseT _) -> genStmt (acc, n, l) xs
    _ ->
      let
        (aasme, n1, l1) = genExp (n+1, l) e (ATemp n)
        (aasms, n2, l2) = genStmt ([], n1, l1) [s]
        aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l2+3),
                ACtrl $ Goto (show $ l2+2),
                ACtrl $ Lbl (show $ l2+2)]
        aasm' = [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+1)] ++ aasme ++ aasm ++ aasms ++
                [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+3)]
      in genStmt (acc ++ aasm', n2, l2+3) xs
genStmt (acc, n, l) ((Ctrl (For ms1 e ms2 s3 p) _) : xs) =
  let
    (init, n1, l1) = case ms1 of
      Nothing -> ([], n, l)
      (Just s1) -> genStmt ([], n, l) [Simp s1 p]
    (aasme, n2, l2) = genExp (n1+1, l1) e (ATemp n1)
    (step, n3, l3) = case ms2 of
      Nothing -> ([], n2, l2)
      (Just s2) -> genStmt ([], n2, l2) [Simp s2 p]
    (body, n4, l4) = genStmt ([], n3, l3) [s3]
    aasm = init ++ [ACtrl $ Goto (show $ l4+1), ACtrl $ Lbl (show $ l4+1)] ++ aasme ++
           [ACtrl $ Ifz (ALoc (ATemp n1)) (show $ l4+3),
            ACtrl $ Goto (show $ l4+2),
            ACtrl $ Lbl (show $ l4+2)] ++ body ++ step ++
           [ACtrl $ Goto (show $ l4+1),
            ACtrl $ Lbl (show $ l4+3)]
  in genStmt (acc ++ aasm, n4, l4+3) xs
     
genExp :: (Int, Int) -> Expr -> ALoc -> ([AAsm], Int, Int)
genExp (n,l) (ExpInt _ i _) loc = ([AAsm [loc] Nop [AImm $ fromIntegral i]], n, l)
genExp (n,l) (TrueT _) loc = ([AAsm [loc] Nop [AImm 1]], n, l)
genExp (n,l) (FalseT _) loc = ([AAsm [loc] Nop [AImm 0]], n, l)
genExp (n,l) (Ident s _) loc = ([AAsm [loc] Nop [ALoc $ AVar s]], n, l)
genExp (n,l) (ExpBinOp LAnd e1 e2 p) loc =
  genExp (n,l) (ExpTernOp e1 e2 (FalseT p) p) loc
genExp (n,l) (ExpBinOp LOr e1 e2 p) loc =
  genExp (n,l) (ExpTernOp e1 (TrueT p) e2 p) loc
genExp (n,l) (ExpBinOp op e1 e2 p) loc | op == Shl || op == Shr = let
  div = ExpBinOp Div (ExpInt Dec 1 p) (ExpInt Dec 0 p) p
  cond = ExpBinOp LOr (ExpBinOp Gt e2 (ExpInt Dec 31 p) p)
         (ExpBinOp Lt e2 (ExpInt Dec 0 p) p) p
  sop = case op of
    Shl -> SShl
    Shr -> SShr
  in genExp (n,l) (ExpTernOp cond div (ExpBinOp sop e1 e2 p) p) loc
genExp (n,l) (ExpBinOp op e1 e2 _) loc = let
  (i1, n', l') = genExp (n + 1, l) e1 (ATemp n)
  (i2, n'', l'') = genExp (n' + 1, l') e2 (ATemp n')
  aasm  = [AAsm [loc] op [ALoc $ ATemp n, ALoc $ ATemp $ n']]
  in (i1 ++ i2 ++ aasm, n'', l'')
genExp (n,l) (ExpUnOp Incr (Ident i _) p) _ = let
  e' = ExpBinOp Add (Ident i p) (ExpInt Dec 1 p) p
  in genExp (n, l) e' (AVar i)
genExp (n,l) (ExpUnOp Decr (Ident i _) p) _ = let
  e' = ExpBinOp Sub (Ident i p) (ExpInt Dec 1 p) p
  in genExp (n, l) e' (AVar i)
genExp (n,l) (ExpUnOp op e _) loc = let
  (i1, n', l') = genExp (n + 1, l) e (ATemp n)
  aasm = [AAsm [loc] op [ALoc $ ATemp n]]
  in (i1 ++ aasm, n', l')
genExp (n, l) (ExpTernOp e1 e2 e3 _) loc = 
  case e1 of
    (TrueT _) -> genExp (n, l) e2 loc
    (FalseT _) -> genExp (n, l) e3 loc
    _ ->
      let
        (i1, n1, l1) = genExp (n+1, l) e1 (ATemp n)
        (i2, n2, l2) = genExp (n1+1, l1) e2 loc
        (i3, n3, l3) = genExp (n2+1, l2) e3 loc
        aasm = i1 ++ [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l3+2),
                      ACtrl $ Goto (show $ l3+1),
                      ACtrl $ Lbl (show $ l3+1)] ++
               i2 ++ [ACtrl $ Goto (show $ l3+3),
                      ACtrl $ Lbl (show $ l3+2)] ++
               i3 ++ [ACtrl $ Goto (show $ l3+3),
                      ACtrl $ Lbl (show $ l3+3)]
      in (aasm, n3, l3+3)
genExp (n, l) (App f es _) loc = let
  (computeArgs, temps, n', l') =
    foldr (\e -> \(aasm, temps, n1, l1) -> let
              (code, n2, l2) = genExp (n1+1, l1) e (ATemp n1)
              in (code ++ aasm, n1 : temps, n2, l2)) ([], [], n, l) es
  --TODO: more than 6 args
  moveArgs = map (\(i, t) ->
                   AAsm {aAssign = [AArg i], aOp = Nop, aArgs = [ALoc $ ATemp t]})
             $ zip [0..] temps
  aasm = computeArgs ++ moveArgs ++ [ACtrl $ Goto f] ++
         [AAsm {aAssign = [loc], aOp = Nop, aArgs = [ALoc $ ARes]}]
  in (aasm, n', l')
                  
     
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
translate regMap (AAsm {aAssign = [dest], aOp = BNot, aArgs = [src]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src
  in
   case (s, dest') of
     (Stk _, Stk _) ->
       [Movl s (Reg R15D),
        Movl (Reg R15D) dest',
        Notl dest']
     _ ->
       [Movl (regFind regMap src) dest',
        Notl dest']
translate regMap (AAsm {aAssign = [dest], aOp = LNot, aArgs = [src]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src
  in
   case (s, dest') of
     (Stk _, Stk _) ->
       [Movl s (Reg R15D),
        Movl (Reg R15D) dest',
        Xorl (Val 1) dest']
     _ ->
       [Movl s dest',
        Xorl (Val 1) dest']
translate regMap (AAsm {aAssign = [dest], aOp = Lt, aArgs = [src1, src2]}) =
  cmpOp (dest,src2,src1) Lt regMap
translate regMap (AAsm {aAssign = [dest], aOp = Gt, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Gt regMap
translate regMap (AAsm {aAssign = [dest], aOp = Leq, aArgs = [src1, src2]}) =
  cmpOp (dest,src2,src1) Leq regMap
translate regMap (AAsm {aAssign = [dest], aOp = Geq, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Geq regMap
translate regMap (AAsm {aAssign = [dest], aOp = Eq, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Eq regMap
translate regMap (AAsm {aAssign = [dest], aOp = Neq, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Neq regMap
translate regMap (AAsm {aAssign = [dest], aOp = BAnd, aArgs = [src1, src2]}) =
  binOp (dest,src1,src2) BAnd regMap
translate regMap (AAsm {aAssign = [dest], aOp = BOr, aArgs = [src1, src2]}) =
  binOp (dest,src1,src2) BOr regMap
translate regMap (AAsm {aAssign = [dest], aOp = BXor, aArgs = [src1, src2]}) =
  binOp (dest,src1,src2) BXor regMap
translate regMap (ACtrl (Ret (ALoc loc))) =
  [Pop (Reg RBP), AsmRet]
translate regMap (ACtrl (Lbl l)) = 
  [AsmLbl l]
translate regMap (ACtrl (Goto l)) = 
  [Jmp l]
translate regMap (ACtrl (Ifz v l)) =
  let
    v' = regFind regMap v
  in 
   case v' of
     (Stk _) -> [Movl v' (Reg R15D), Testl (Reg R15D) (Reg R15D), Je l]
     _ -> [Testl v' v', Je l]
translate regMap (AAsm {aAssign = [dest], aOp = o, aArgs = [src1, src2]})
  | o == SShl || o == SShr =
  let
    asm = case o of
      SShl -> Sall
      SShr -> Sarl
    dest' = regFind regMap (ALoc dest)
    s1 = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (dest', s1) of
     (Stk _, Stk _) ->
       [Movl s2 (Reg ECX),
        Movl s1 (Reg R15D),
        Movl (Reg R15D) dest',
        asm (Reg CL) dest']
     _ ->
       [Movl s2 (Reg ECX),
        Movl s1 dest',
        asm (Reg CL) dest']
cmpOp (dest,src1,src2) op regMap = 
  let
    asm = case op of
      Lt -> Setl
      Leq -> Setle
      Gt -> Setl
      Geq -> Setle
      Eq -> Sete
      Neq -> Setne
    dest' = regFind  regMap (ALoc dest)
    s1 = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (dest', s1, s2) of
     (Stk _, Stk _, Stk _) ->
       [Movl s1 (Reg R15D),
        Cmpl (Reg R15D) s2,
        asm (Reg R15B),
        Movzbl (Reg R15B) (Reg R15D),
        Movl (Reg R15D) dest']
     (Stk _, _, _) ->
       [Cmpl s1 s2,
        asm (Reg R15B),
        Movzbl (Reg R15B) (Reg R15D),
        Movl (Reg R15D) dest']
     (_, Stk _, Stk _) ->
       [Movl s1 (Reg R15D),
        Cmpl (Reg R15D) s2,
        asm (Reg R15B),
        Movzbl (Reg R15B) dest']
     _ ->
       [Cmpl s1 s2,
        asm (Reg R15B),
        Movzbl (Reg R15B) dest']

binOp (dest,src1,src2) op regMap =
  let
    asm = case op of
      Add -> Addl
      BAnd -> Andl
      BOr -> Orl
      BXor -> Xorl
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (s, s2) of
     (Stk _, _) ->
       [Movl s (Reg R15D),
        asm s2 (Reg R15D),
        Movl (Reg R15D) dest']
     (_, Stk _) ->
       [Movl s2 (Reg R15D),
        asm s (Reg R15D),
        Movl (Reg R15D) dest']
     _ ->
       if s == dest' then
         [Movl s dest',
          asm s2 dest']
       else
         [Movl s2 dest',
          asm s dest']

regFind :: Map.Map AVal Arg -> AVal -> Arg
regFind regMap (AImm i) = Val i
regFind regMap aloc = 
  case Map.lookup aloc regMap of
    Just (reg) -> reg
    Nothing -> Reg EAX
