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

codeGen :: Program -> Map.Map String [Asm]
codeGen (Program gdecls) =
  let
    fdefns = concatMap (\x -> case x of
                           (FDefn _ s p (Block b _) _) -> [(s,p,b)]
                           _ -> []) gdecls
    lengths = map (\(s,_,b) -> (s, length b)) fdefns
    (res, _) = foldr (\f -> \(m, l) -> let
                    (s, aasm, l') = genFunction f l lengths
                    in (Map.insert s aasm m, l')) (Map.empty,0) fdefns
  in trace (show gdecls) res

genFunction (fun,p,b) l lengths =
  let
    (aasm, _, l', ep) = genStmt ([], length(p), l, Nothing) b lengths
    p' = zip (map (\(Param _ i) -> i) p) [0..]
    prefix = map (\(i, n) ->
                   AAsm {aAssign = [AVar i], aOp = Nop, aArgs = [ALoc $ AArg n]}) p'
    setup = [Push (Reg RBP),
             Mov (Reg RSP) (Reg RBP)]
    cleanup = case ep of
      Nothing -> [ACtrl $ Ret $ ALoc ARes]
      Just ep' -> [ACtrl $ Lbl (show ep'),
                   ACtrl $ Ret $ ALoc ARes]
    aasm' = trace (show aasm) prefix ++ aasm ++ cleanup
    s = ssa aasm' fun
    unssa = deSSA s
    (regMap, used) = allocateRegisters unssa
    code = 
      case used of
        0 ->
          setup ++ (concatMap (translate regMap 0) unssa)
        x | x < 5 -> let
          save = map (\(r, i) -> Push r) $ zip [Reg RBX, Reg R12, Reg R13, Reg R14] [0..(x-1)]
          restore = map (\(Push r) -> Pop r) $ reverse save
          code' =  concatMap (translate regMap (x + (mod x 2))) unssa
          (front, back) = splitAt (length(code')-2) code'
          in if ((mod x 2) == 0) then setup ++ save ++ front ++ restore ++ back
             else setup ++ save ++ [Push (Reg RBP)] ++ front ++ [Pop (Reg RBP)] ++ restore ++ back
        x -> let
          save = map (\(r, i) -> Push r) $ zip [Reg RBX, Reg R12, Reg R13, Reg R14] [0..(x-1)]
          restore = map (\(Push r) -> Pop r) $ reverse save
          n = x-3
          code' =  concatMap (translate regMap (x+1)) unssa
          (front, back) = splitAt (length(code')-2) code'
          sub = [Subb (Val (n*8)) (Reg RSP)]
          add = [Addd (Val (n*8 )) (Reg RSP)]
          in setup ++ save ++ sub ++ front ++ add ++ restore ++ back
        -- TODO: when x >= 5, we are storing local variables on stack.
             -- wat do here?!?!?
    code' = trace (show code) removeRedundant code
  in (fun, code', l')

removeRedundant code = 
  filter (\inst -> case inst of
             (Movl a1 a2) -> a1 /= a2
             _ -> True) code

-- updates the abstract assembly at a label
update aasm Nothing = Just aasm
update aasm (Just acc) = Just $ acc ++ aasm

updatePre aasm Nothing = Just aasm
updatePre aasm (Just acc) = Just $ aasm ++ acc
     
unroll (LIdent i) s = (Ident i s, i)
unroll (LDeref l) s = 
  let
    (v, i) = unroll l s
  in (ExpUnOp Deref v s, i)
 
genPost (LIdent i) target res n = ([AAsm [target] Nop [ALoc res]], n)
genPost (LDeref (LIdent i)) target res n = ([AAsm [Pt target] Nop [ALoc res]], n)
genPost (LDeref l) target res n = 
  let
    (aasm, n') = genPost l (ATemp n) res (n+1)
  in ((AAsm [ATemp n] Nop [ALoc $ Pt target]) : aasm, n')
                           
genStmt acc [] _ = acc
genStmt acc ((Simp (Decl _ _ Nothing _) _) : xs) lens = genStmt acc xs lens
genStmt (acc, n, l, ep) ((Simp (Decl _ i (Just e) _) _) : xs) lens =
  let
    (aasm, n', l') = genExp (n, l) e (AVar i) lens
  in genStmt (acc ++ aasm, n', l', ep) xs lens
genStmt (acc, n, l, ep) ((Simp (Asgn lval o e s) _) : xs) lens = 
  let
    (var, ident) = unroll lval s
    e' = case o of
      Nothing -> e
      Just op -> ExpBinOp op var e s
    (aasm, n', l') = genExp (n+1, l) e' (ATemp n) lens
    (post, n'') = genPost lval (AVar ident) (ATemp n) n'
  in genStmt (acc ++ aasm ++ post, n'', l', ep) xs lens
genStmt (acc, n, l, ep) ((Simp (PostOp o (LIdent i) s) _) : xs) lens =
  let
    op = case o of
      Incr -> Add
      Decr -> Sub
    e' = ExpBinOp op (Ident i s) (ExpInt Dec 1 s) s
    (aasm, n', l') = genExp (n, l) e' (AVar i) lens
  in genStmt (acc ++ aasm, n', l', ep) xs lens
genStmt (acc, n, l, ep) ((Simp (Expr e _) _) : xs) lens = 
  let
    (aasm, n', l') = genExp (n + 1, l) e (ATemp n) lens
  in genStmt (acc ++ aasm, n', l', ep) xs lens
genStmt (acc, n, l, ep) ((BlockStmt (Block stmts _) _) : xs) lens = 
  let
    (aasm, n', l', ep') = genStmt ([], n, l, ep) stmts lens
  in genStmt (acc ++ aasm, n', l', ep') xs lens
genStmt (acc, n, l, ep) ((Ctrl (Return (Just e) _) _) : xs) lens =
  let
    (aasm, n', l') = genExp (n, l) e (ARes) lens
    (epilogue, l'') = case ep of
      (Just ep') -> (ep', l') 
      Nothing -> (l'+1, l'+1)
  in (acc ++ aasm ++ [ACtrl $ Goto (show epilogue)], n', l'', Just epilogue)
genStmt (acc, n, l, ep) ((Ctrl (Return Nothing _) _) : xs) _ =
  let
    (epilogue, l') = case ep of
      (Just ep') -> (ep', l) 
      Nothing -> (l+1, l+1)
  in (acc ++ [ACtrl $ Goto (show epilogue)], n, l', Just epilogue)
genStmt (acc, n, l, ep) ((Ctrl (If e s Nothing _) _) : xs) lens =
  let
    (aasme, n', l') = genExp (n + 1, l) e (ATemp n) lens
    (aasms, n'', l'', ep') = genStmt ([], n', l', ep) [s] lens
    aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l''+2),
            ACtrl $ Goto (show $ l''+1),
            ACtrl $ Lbl (show $ l''+1)]
    aasm' = aasme ++ aasm ++ aasms ++
            [ACtrl $ Goto (show $ l''+2), ACtrl $ Lbl (show $ l''+2)]
  in genStmt (acc ++ aasm', n'', l''+2, ep') xs lens
genStmt (acc, n, l, ep) ((Ctrl (If e s1 (Just s2) _) _) : xs) lens =
  case e of
   (TrueT _) -> genStmt (acc, n, l, ep) (s1 : xs) lens
   (FalseT _) -> genStmt (acc, n, l, ep) (s2 : xs) lens
   _ -> let
     (aasme, n1, l1) = genExp (n+1, l) e (ATemp n) lens
     (aasms1, n2, l2, ep2) = genStmt ([], n1, l1, ep) [s1] lens
     (aasms2, n3, l3, ep3) = genStmt ([], n2, l2, ep2) [s2] lens
     aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l3+2),
             ACtrl $ Goto (show $ l3+1),
             ACtrl $ Lbl (show $ l3+1)]
     aasm' = aasme ++ aasm ++ aasms1 ++
             [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+2)] ++
             aasms2 ++ [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+3)]
     in genStmt (acc ++ aasm', n3, l3+3, ep3) xs lens
genStmt (acc, n, l, ep) ((Ctrl (While e s _) _) : xs) lens =
  case e of
    (FalseT _) -> genStmt (acc, n, l, ep) xs lens
    _ ->
      let
        (aasme, n1, l1) = genExp (n+1, l) e (ATemp n) lens
        (aasms, n2, l2, ep') = genStmt ([], n1, l1, ep) [s] lens
        aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l2+3),
                ACtrl $ Goto (show $ l2+2),
                ACtrl $ Lbl (show $ l2+2)]
        aasm' = [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+1)] ++ aasme ++ aasm ++ aasms ++
                [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+3)]
      in genStmt (acc ++ aasm', n2, l2+3, ep') xs lens
genStmt (acc, n, l, ep) ((Ctrl (For ms1 e ms2 s3 p) _) : xs) lens =
  let
    (init, n1, l1, ep1) = case ms1 of
      Nothing -> ([], n, l, ep)
      (Just s1) -> genStmt ([], n, l, ep) [Simp s1 p] lens
    (aasme, n2, l2) = genExp (n1+1, l1) e (ATemp n1) lens
    (step, n3, l3, ep2) = case ms2 of
      Nothing -> ([], n2, l2, ep1)
      (Just s2) -> genStmt ([], n2, l2, ep1) [Simp s2 p] lens
    (body, n4, l4, ep3) = genStmt ([], n3, l3, ep2) [s3] lens
    aasm = init ++ [ACtrl $ Goto (show $ l4+1), ACtrl $ Lbl (show $ l4+1)] ++ aasme ++
           [ACtrl $ Ifz (ALoc (ATemp n1)) (show $ l4+3),
            ACtrl $ Goto (show $ l4+2),
            ACtrl $ Lbl (show $ l4+2)] ++ body ++ step ++
           [ACtrl $ Goto (show $ l4+1),
            ACtrl $ Lbl (show $ l4+3)]
  in genStmt (acc ++ aasm, n4, l4+3, ep3) xs lens
genStmt acc ((Ctrl (Assert e _) p) : xs) lens = let
  s = Ctrl (If (ExpUnOp LNot e p) (Simp (Expr (App "_c0_abort" [] p) p) p) Nothing p) p
  in genStmt acc (s : xs) lens
     
genExp :: (Int, Int) -> Expr -> ALoc -> [(String, Int)] -> ([AAsm], Int, Int)
genExp (n,l) (ExpInt _ i _) loc _ = ([AAsm [loc] Nop [AImm $ fromIntegral i]], n, l)
genExp (n,l) (TrueT _) loc _ = ([AAsm [loc] Nop [AImm 1]], n, l)
genExp (n,l) (FalseT _) loc _ = ([AAsm [loc] Nop [AImm 0]], n, l)
genExp (n,l) (Ident s _) loc _ = ([AAsm [loc] Nop [ALoc $ AVar s]], n, l)
genExp (n,l) (ExpBinOp LAnd e1 e2 p) loc lens =
  genExp (n,l) (ExpTernOp e1 e2 (FalseT p) p) loc lens
genExp (n,l) (ExpBinOp LOr e1 e2 p) loc lens =
  genExp (n,l) (ExpTernOp e1 (TrueT p) e2 p) loc lens
genExp (n,l) (ExpBinOp op e1 e2 p) loc lens | op == Shl || op == Shr = let
  div = ExpBinOp Div (ExpInt Dec 1 p) (ExpInt Dec 0 p) p
  cond = ExpBinOp LOr (ExpBinOp Gt e2 (ExpInt Dec 31 p) p)
         (ExpBinOp Lt e2 (ExpInt Dec 0 p) p) p
  sop = case op of
    Shl -> SShl
    Shr -> SShr
  in genExp (n,l) (ExpTernOp cond div (ExpBinOp sop e1 e2 p) p) loc lens
genExp (n,l) (ExpBinOp op e1 e2 _) loc lens = 
  case (op, e1, e2) of
    (Add, ExpInt _ i1 _, ExpInt _ i2 _) ->
      ([AAsm [loc] Nop [AImm $ fromIntegral $ i1 + i2]], n, l)
    _ -> let
      (i1, n', l') = genExp (n + 1, l) e1 (ATemp n) lens
      (i2, n'', l'') = genExp (n' + 1, l') e2 (ATemp n') lens
      aasm  = [AAsm [loc] op [ALoc $ ATemp n, ALoc $ ATemp $ n']]
      in (i1 ++ i2 ++ aasm, n'', l'')
genExp (n,l) (ExpUnOp Incr (Ident i _) p) _ lens = let
  e' = ExpBinOp Add (Ident i p) (ExpInt Dec 1 p) p
  in genExp (n, l) e' (AVar i) lens
genExp (n,l) (ExpUnOp Decr (Ident i _) p) _ lens = let
  e' = ExpBinOp Sub (Ident i p) (ExpInt Dec 1 p) p
  in genExp (n, l) e' (AVar i) lens
genExp (n,l) (ExpUnOp op e _) loc lens = let
  (i1, n', l') = genExp (n + 1, l) e (ATemp n) lens
  aasm = [AAsm [loc] op [ALoc $ ATemp n]]
  in (i1 ++ aasm, n', l')
genExp (n, l) (ExpTernOp e1 e2 e3 _) loc lens = 
  case e1 of
    (TrueT _) -> genExp (n, l) e2 loc lens
    (FalseT _) -> genExp (n, l) e3 loc lens
    _ ->
      let
        (i1, n1, l1) = genExp (n+1, l) e1 (ATemp n) lens
        (i2, n2, l2) = genExp (n1+1, l1) e2 loc lens
        (i3, n3, l3) = genExp (n2+1, l2) e3 loc lens
        aasm = i1 ++ [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l3+2),
                      ACtrl $ Goto (show $ l3+1),
                      ACtrl $ Lbl (show $ l3+1)] ++
               i2 ++ [ACtrl $ Goto (show $ l3+3),
                      ACtrl $ Lbl (show $ l3+2)] ++
               i3 ++ [ACtrl $ Goto (show $ l3+3),
                      ACtrl $ Lbl (show $ l3+3)]
      in (aasm, n3, l3+3)
genExp (n, l) (App f es _) loc lens =
  case lookup f lens of
    Just 0 -> ([], n, l)
    _ ->
      let
        (computeArgs, temps, n', l') =
          foldr (\e -> \(aasm, temps, n1, l1) -> let
                    (code, n2, l2) = genExp (n1+1, l1) e (ATemp n1) lens
                    in (code ++ aasm, n1 : temps, n2, l2)) ([], [], n, l) es
        (front,rest) = splitAt 6 temps
        moveFrontArgs = map (\(i, t) ->
                              AAsm {aAssign = [AArg i], aOp = Nop, aArgs = [ALoc $ ATemp t]})
                        $ zip [0..] front
        aasm = computeArgs ++ moveFrontArgs ++ [ACtrl $ Call f rest] ++
               [AAsm {aAssign = [loc], aOp = Nop, aArgs = [ALoc $ ARes]}]
      in (aasm, n', l')
genExp (n, l) (Alloc Int _) loc lens =                
  let
    aasm = [ACtrl $ Call "_c0_malloc" [],
            AAsm [loc] Nop [ALoc $ ARes]]
  in (aasm, n, l)
     
-- begin 'temp -> register' translation
translate regMap n (AAsm {aAssign = [dest], aOp = Nop, aArgs = [src]}) =
  let
    s = regFind regMap src
  in
   case s of
     (Stk _) ->
       [Movl s (Reg R15D),
        Movl (Reg R15D) (regFind regMap (ALoc dest))]
     (Reg (SpillArg i)) ->
       [Movl (Stk ((i+n+1)*8)) (Reg R15D),
        Movl (Reg R15D) (regFind regMap (ALoc dest))]
     _ ->
       [Movl (regFind regMap src) (regFind regMap (ALoc dest))]
translate regMap _ (AAsm {aAssign = [dest], aOp = Add, aArgs = [src1, src2]}) =
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
translate regMap _ (AAsm {aAssign = [dest], aOp = Sub, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (s, s2) of
     _ ->
       if s2 == dest' then
         if s == s2 then
         [Negl s2,
          Movl s (Reg R15D),
          Addl (Reg R15D) s2] else
           [Negl s2,
            Addl s s2]
       else
         [Movl s (Reg R15D),
          Movl (Reg R15D) dest',
          Movl s2 (Reg R15D),
          Subl (Reg R15D) dest']
translate regMap _ (AAsm {aAssign = [dest], aOp = Mul, aArgs = [src1, src2]}) =
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
translate regMap _ (AAsm {aAssign = [dest], aOp = Div, aArgs = [src1, src2]}) =
  [Movl (regFind regMap src1) (Reg EAX),
   Cdq,
   Idivl (regFind regMap src2),
   Movl (Reg EAX) (regFind regMap (ALoc dest))]
translate regMap _ (AAsm {aAssign = [dest], aOp = Mod, aArgs = [src1, src2]}) =
  [Movl (regFind regMap src1) (Reg EAX),
   Cdq,
   Idivl (regFind regMap src2),
   Movl (Reg EDX) (regFind regMap (ALoc dest))]
translate regMap _ (AAsm {aAssign = [dest], aOp = Neg, aArgs = [src]}) =
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
translate regMap _ (AAsm {aAssign = [dest], aOp = BNot, aArgs = [src]}) =
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
translate regMap _ (AAsm {aAssign = [dest], aOp = LNot, aArgs = [src]}) =
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
translate regMap _ (AAsm {aAssign = [dest], aOp = Lt, aArgs = [src1, src2]}) =
  cmpOp (dest,src2,src1) Lt regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = Gt, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Gt regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = Leq, aArgs = [src1, src2]}) =
  cmpOp (dest,src2,src1) Leq regMap
translate regMap _(AAsm {aAssign = [dest], aOp = Geq, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Geq regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = Eq, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Eq regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = Neq, aArgs = [src1, src2]}) =
  cmpOp (dest,src1,src2) Neq regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = BAnd, aArgs = [src1, src2]}) =
  binOp (dest,src1,src2) BAnd regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = BOr, aArgs = [src1, src2]}) =
  binOp (dest,src1,src2) BOr regMap
translate regMap _ (AAsm {aAssign = [dest], aOp = BXor, aArgs = [src1, src2]}) =
  binOp (dest,src1,src2) BXor regMap
--translate regMap _ (APush loc) =
--  [Push $ fullReg (regFind regMap $ ALoc loc)]
--translate regMap _ (APop loc) =
--  [Pop $ fullReg (regFind regMap $ ALoc loc)]
translate regMap n (ACtrl (Call s ts)) = let
  (l, _) = 
    foldr (\t -> \(acc, i) -> 
            case regFind regMap $ ALoc $ ATemp t of
              (Stk j) -> ([Movl (Stk j) (Reg R15D),
                           Movl (Reg R15D) (Stk (-i*8))] : acc, i+1)
              s -> ([Movl s (Stk (-i*8))] : acc, i+1)) ([], 1) ts
  saves = concat l
  restores = map (\(Movl x y) -> Movl y x) (reverse saves)
  in if ((length ts)*8) > 0 then
       saves ++ [Subb (Val $ (length ts)*8) (Reg RSP)] ++ [AsmCall s] ++ 
       [Addd (Val $ (length ts)*8) (Reg RSP)] ++ restores
     else
       [AsmCall s]
translate regMap _ (ACtrl (Ret (ALoc loc))) =
  [Pop (Reg RBP), AsmRet]
translate regMap _ (ACtrl (Lbl l)) = 
  [AsmLbl l]
translate regMap _ (ACtrl (Goto l)) = 
  [Jmp l]
translate regMap _ (ACtrl (Ifz v l)) =
  let
    v' = regFind regMap v
  in 
   case v' of
     (Stk _) -> [Movl v' (Reg R15D), 
                 Movzbl (Reg R15B) (Reg R15D),
                 Testl (Reg R15D) (Reg R15D), 
                 Je l]
     _ -> [Movzbl (lowerReg v') v', Testl v' v', Je l]
translate regMap _ (AAsm {aAssign = [dest], aOp = o, aArgs = [src1, src2]})
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

regFind :: Map.Map ALoc Arg -> AVal -> Arg
regFind regMap (AImm i) = Val i
regFind regMap (ALoc (Pt aloc)) = 
  Loc (regFind regMap (ALoc aloc))
regFind regMap (ALoc loc) = 
  case Map.lookup loc regMap of
    Just (reg) -> reg
    Nothing -> Reg EAX

fullReg (Reg EAX) = Reg RAX
fullReg (Reg EBX) = Reg RBX
fullReg (Reg ECX) = Reg RCX
fullReg (Reg EDX) = Reg RDX
fullReg (Reg ESI) = Reg RSI
fullReg (Reg EDI) = Reg RDI
fullReg (Reg R8D) = Reg R8
fullReg (Reg R9D) = Reg R9
fullReg (Reg R10D) = Reg R10
fullReg (Reg R11D) = Reg R11
fullReg (Reg R12D) = Reg R12
fullReg (Reg R13D) = Reg R13
fullReg (Reg R14D) = Reg R14
fullReg x = x

lowerReg (Reg EAX) = Reg AL
lowerReg (Reg EBX) = Reg BL
lowerReg (Reg ECX) = Reg CL
lowerReg (Reg EDX) = Reg DL
lowerReg (Reg ESI) = Reg SIL
lowerReg (Reg EDI) = Reg DIL
lowerReg (Reg R8D) = Reg R8B
lowerReg (Reg R9D) = Reg R9B
lowerReg (Reg R10D) = Reg R10B
lowerReg (Reg R11D) = Reg R11B
lowerReg (Reg R12D) = Reg R12B
lowerReg (Reg R13D) = Reg R13B
lowerReg (Reg R14D) = Reg R14B
lowerReg x = x
