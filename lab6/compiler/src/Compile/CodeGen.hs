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
import Text.Parsec.Pos
import Debug.Trace

import Compile.SSA
import qualified Compile.CheckAST as Check

{- TODO: Our IR sucks pretty bad. I dont think we should need to use
a typechecker in the cogen phase (we are now). A lot of information is
being thrown out after elaboration. -}
codeGen :: (Program, Map.Map String (Maybe [String], [Param]), Bool, Int)
           -> Map.Map String [Asm]
codeGen (Program gdecls, sdefn, safe, opt) =
  let
    smap = Map.map (\(a,b,c,d) -> (a,b,d)) $ structInfo sdefn
    fdefns = concatMap (\x -> case x of
                           (FDefn _ s p (Block b _) _) -> [(s,p,b)]
                           _ -> []) gdecls
    lengths = map (\(s,_,b) -> (s, length b)) fdefns
    inl = if opt >= 2 then inline fdefns else fdefns
    gdecls' = if opt >= 2
              then map (\x -> case x of
                           FDefn t s p b p0 -> FDefn t s (map (parVar s) p) b p0
                           _ -> x) gdecls
              else gdecls
    ctx = foldr (\x -> \acc -> case x of
                    (FDefn t s p _ _) -> foldr (\(Param ty st)-> \a -> Map.insert st ty a)
                                         (Map.insert s t acc)
                                         p
                    _ -> acc) Map.empty gdecls'
    (res, _) = foldr (\f -> \(m, l) -> let
                    (s, aasm, l') = genFunction f l lengths (ctx, smap) safe opt
                    in (Map.insert s aasm m, l')) (Map.empty,0) inl
  in res


ptoe [] = []
ptoe ((Param t s):xs) = (Ident s $ newPos "" 0 0) : ptoe xs

funcVarE f (Ident s p0) = Ident (f++"_"++s) p0
funcVarE f (ExpUnOp o e p0) = ExpUnOp o (funcVarE f e) p0
funcVarE f (ExpBinOp Arrow e1 e2 p0) = ExpBinOp Arrow (funcVarE f e1) e2 p0
funcVarE f (ExpBinOp Dot e1 e2 p0) = ExpBinOp Dot (funcVarE f e1) e2 p0
funcVarE f (ExpBinOp o e1 e2 p0) = ExpBinOp o (funcVarE f e1) (funcVarE f e2) p0
funcVarE f (ExpTernOp e1 e2 e3 p0) = ExpTernOp (funcVarE f e1) (funcVarE f e2) (funcVarE f e3) p0
funcVarE f (App s le p0) = App s (map (\x-> funcVarE f x) le) p0
funcVarE f (AllocArray t e p0) = AllocArray t (funcVarE f e) p0
funcVarE f (Subscr e1 e2 p0) = Subscr (funcVarE f e1) (funcVarE f e2) p0
funcVarE f e = e

funcVarLV f (LIdent s) = LIdent (f++"_"++s)
funcVarLV f (LArrow lv s) = LArrow (funcVarLV f lv) s
funcVarLV f (LDot lv s) = LDot (funcVarLV f lv) s
funcVarLV f (LDeref lv) = LDeref (funcVarLV f lv)
funcVarLV f (LArray lv e) = LArray (funcVarLV f lv) (funcVarE f e)

funcVar f [] = []
funcVar f ((Simp s p0):xs) = 
  let s' = case s of
        Decl t i (Just e) p1 -> Decl t (f++"_"++i) (Just (funcVarE f e)) p1
        Asgn lv o e p1 -> Asgn (funcVarLV f lv) o (funcVarE f e) p1
        PostOp o lv p1 -> PostOp o (funcVarLV f lv) p1
        Expr e p1 -> Expr (funcVarE f e) p1
        e -> e
  in
   (Simp s' p0) : funcVar f xs
funcVar f ((Ctrl c p0) : xs) =
  let c' = case c of
        If e s (Just ms) p1 -> If (funcVarE f e) (head $ funcVar f [s]) (Just (head $ funcVar f [ms])) p1
        If e s Nothing p1 -> If (funcVarE f e) (head $ funcVar f [s]) Nothing p1
        While e s p1 -> While (funcVarE f e) (head $ funcVar f [s]) p1
        For (Just s1) e (Just s2) st p1 ->
          let Simp s1' _  = head $ funcVar f [(Simp s1 p1)]
              Simp s2' _ = head $ funcVar f [(Simp s2 p1)]
          in For (Just s1') (funcVarE f e) (Just s2') (head $ funcVar f [st]) p1
        For (Just s1) e Nothing st p1 ->
          let Simp s1' _ = head $ funcVar f [(Simp s1 p1)]
          in For (Just s1') (funcVarE f e) Nothing (head $ funcVar f [st]) p1
        For Nothing e (Just s2) st p1 ->
          let Simp s2' _ = head $ funcVar f [(Simp s2 p1)]
          in For Nothing (funcVarE f e) (Just s2') (head $ funcVar f [st]) p1
        Return (Just e) p1 -> Return (Just (funcVarE f e)) p1
        Assert e p1 -> Assert (funcVarE f e) p1
        e -> e
  in
   (Ctrl c' p0) : funcVar f xs
funcVar f ((BlockStmt(Block s p1) p0):xs) = (BlockStmt (Block (funcVar f s) p1) p0) : funcVar f xs

parVar f (Param t s) = Param t (f++"_"++s)

numStmts l = sum $ map (\x -> case x of
                           Simp _ _ -> 1
                           Ctrl (If _ s1 Nothing _) _ -> 1 + (numStmts [s1])
                           Ctrl (If _ s1 (Just s2) _) _ -> 1 + (max (numStmts [s1]) (numStmts [s2]))
                           Ctrl (For _ _ _ s _) _ -> 1 + (numStmts [s])
                           Ctrl (While _ s _) _ -> 1 + (numStmts [s])
                           Ctrl (Return _ _) _ -> 1
                           BlockStmt(Block s _) _ -> numStmts s
                           _ -> 1
                       ) l

replaceRets lv (Ctrl(Return(Just x) p1) p0) =
  Simp(Asgn lv Nothing x p0) p1
replaceRets lv (Ctrl(If e s1 (Just s2) p1) p0) =
    let
      s1' = replaceRets lv s1
      s2' = replaceRets lv s2
    in (Ctrl(If e s1' (Just s2') p1) p0)
replaceRets lv (Ctrl(If e s1 Nothing p1) p0) = Ctrl(If e (replaceRets lv s1) Nothing p1) p0
replaceRets lv (Ctrl(While e s p1) p0) = Ctrl(While e (replaceRets lv s) p1) p0
replaceRets lv (Ctrl(For ms1 e ms2 s p1) p0) = Ctrl(For ms1 e ms2 (replaceRets lv s) p1) p0
replaceRets lv (BlockStmt(Block s p1) p0) = BlockStmt(Block (map (replaceRets lv) s) p1) p0
replaceRets lv e = e


inline fdefns =
  let
    fdefns' = map(\(x,y,z) -> (x, map (parVar x) y, funcVar x z)) fdefns
    fmap = Map.fromList $ map (\(x,y,z) -> (x,(ptoe y,z))) fdefns'
    fdefns'' = map (\(f,p,stmts) -> (f, p, inline' f fmap [] stmts)) fdefns'
  in
   fdefns''

--inline (function name) (Map Function Name -> Stmts in Function) (New statements) (Curr Statements)
inline' :: String -> Map.Map String ([Expr],[Stmt]) -> [Stmt] -> [Stmt] -> [Stmt]
inline' _ _ nst [] = nst
inline' func fmap nst (s:st) =
  let
    maxstmts = 3
    s2 = case s of
      Simp s' p0 -> case s' of
        Decl t id (Just e) p1 -> case e of
          App s exprs p2 | case s of {FuncName f->f/=func; Ident f _->f/=func} ->
            let s' = case s of (FuncName f) -> f
                               (Ident f _) -> f
            in case Map.lookup s' fmap of
              Just (prms,sts) ->
                let
                  setprms = map (\(x,y) -> Simp (Asgn (roll x) Nothing y p2) p1) $ zip prms exprs
                  ret = case last sts of
                    (Ctrl(Return x _) _) -> x
                    _ -> trace "Decl hmm... why?" $ Nothing 
                in
                 if numStmts(sts) <= maxstmts
                 then setprms ++ (init sts) ++ [Simp (Decl t id ret p1) p1]
                 else [Simp (Decl t id (Just (App s exprs p2)) p1) p0]
              Nothing -> [Simp (Decl t id (Just (App s exprs p2)) p1) p0]
          _ -> [Simp (Decl t id (Just e) p1) p0]
        Asgn lv op e p1 -> case e of
          App s exprs p2 | case s of {FuncName f->f/=func; Ident f _->f/=func} ->
            let s' = case s of (FuncName f) -> f
                               (Ident f _) -> f
            in case Map.lookup s' fmap of
              Just (prms,sts) ->
                let
                  setprms = map (\(x,y) -> Simp (Asgn (roll x) Nothing y p2) p1) $ zip prms exprs
                in
                 if numStmts(sts) <= maxstmts
                 then 
                   setprms ++ (map (replaceRets lv) sts)
                 else  [Simp (Asgn lv op e p1) p0]
              Nothing -> [Simp (Asgn lv op e p1) p0]
          _ -> [Simp (Asgn lv op e p1) p0]
        Expr e p1 -> case e of
          App s exprs p2 | case s of {FuncName f->f/=func; Ident f _->f/=func} ->
            let s' = case s of {FuncName f -> f; Ident f _-> f}
            in case Map.lookup s' fmap of
              Just (prms,sts) ->
                let
                  setprms = map (\(x,y) -> Simp (Asgn (roll x) Nothing y p2) p1) $ zip prms exprs
                  sts' = case last sts of
                    (Ctrl(Return _ _) _) -> init sts
                    _ -> sts
                in
                 if numStmts(sts) <= maxstmts
                 then
                   setprms ++ sts'
                 else [Simp (Expr e p1) p0]
              Nothing -> [Simp (Expr e p1) p0]
          _ -> [Simp (Expr e p1) p0]
        _ -> [Simp s' p0]
      Ctrl c p0 -> case c of
        If e stif stel p1 -> case e of
          App s exprs p2 | case s of {FuncName f->f/=func; Ident f _->f/=func} ->
            let s' = case s of {FuncName f->f; Ident f _->f}
            in case Map.lookup s' fmap of
              Just (prms,sts) ->
                let
                  setprms = map (\(x,y) -> Simp (Asgn (roll x) Nothing y p2) p1) $ zip prms exprs
                  ret = case last sts of
                    (Ctrl(Return (Just x) _) _) -> Just x
                    _ -> trace "If hmm... why?" $ Nothing
                  stif' = inline' func fmap [] [stif]
                  stif'' = if length stif' == 1 then head stif' else trace "stif sadface" $ head stif'
                  stel' = case stel of
                    Just s -> Just $ head (inline' func fmap [] [s])
                    Nothing -> Nothing
                in
                 if numStmts(sts) <= maxstmts then
                   setprms ++ (init sts) ++ [Simp (Decl Bool (func++"_inline_if") ret p1) p0]  ++
                   [Ctrl (If (Ident (func++"_inline_if") p1) stif'' stel' p1) p0]
                 else [Ctrl (If e stif stel p1) p0]
              Nothing -> [Ctrl (If e stif stel p1) p0]
          _ -> [Ctrl (If e stif stel p1) p0]
        Return me p1 -> case me of 
          Just (App s exprs p2) | case s of {FuncName f->f/=func; Ident f _->f/=func} ->
            let s' = case s of {FuncName f -> f; Ident f _->f}
            in case Map.lookup s' fmap of
              Just (prms,sts) ->
                let
                  setprms = map (\(x,y) -> Simp (Asgn (roll x) Nothing y p2) p1) $ zip prms exprs 
                in
                 if numStmts(sts) <= maxstmts
                 then
                   setprms ++ sts -- includes final return otherwise wouldn't have typchecked
                 else [Ctrl (Return me p1) p0]
              _ -> [Ctrl (Return me p1) p0]
          _ -> [Ctrl (Return me p1) p0]
        _ -> [Ctrl c p0]
      BlockStmt (Block stmts p1) p0 -> [BlockStmt (Block (inline' func fmap [] stmts) p1) p0]
      --_ -> [s]
  in
   inline' func fmap (nst++s2) st
        
        

-- Computes struct size and field offsets in bytes.
structInfo :: Map.Map String (Maybe [String], [Param]) ->
              Map.Map String (Maybe [String], Int, Int, Map.Map String (Int, Type))
structInfo sdefn = 
  Map.foldWithKey (\s -> \(typeParams, params) -> \acc -> let
                      (largest, size, ps, acc') = computeStruct s params sdefn acc
                      size' = if largest == 0 then 0 else case mod size largest of
                         0 -> size
                         n -> size + largest - n
                      acc'' = Map.insert s (typeParams, size', largest, ps) acc'
                      in acc'') Map.empty sdefn

computeStruct s params sdefn m =
  foldl (addField sdefn) (0, 0, Map.empty, m) params
  
addField sdefn =
  (\(constraint, size, ps, m) -> \(Param t s) -> let
      (pSize, align, m') = case t of
        (Type _) -> (8, 8, m)
        Bool -> (4, 4, m)
        Int -> (4, 4, m)
        (Pointer _) -> (8, 8, m)
        (Array _) -> (8, 8, m)
        (Struct s) -> case Map.lookup s m of
          Just (_, len, align, _) -> (len, align, m)
          Nothing -> let
            (typeParams, params) = sdefn Map.! s
            (constraint, size, ps, m') = computeStruct s params sdefn m
            size' = if constraint == 0 then size else case mod size constraint of
              0 -> size
              n -> size + constraint - n
            m'' = Map.insert s (typeParams, size', constraint, ps) m'
            in (size', constraint, m'')
      offset = if align == 0 then size else case mod size align of
        0 -> size
        n -> size + pSize - n
      in (max constraint align, offset + pSize, Map.insert s (offset, t) ps, m'))
        
genFunction (fun,p,b) l lengths (c, smap) safe opt =
  let
    ctx = foldr (\(Param t i) -> \acc-> Map.insert i t acc) c p 
    sb = fun ++"\n"++ foldr (\x -> \acc -> (show x) ++ "\n" ++ acc) "" b
    (aasm, _, l', ep) = --trace sb $
      genStmt ([], length(p), l, Nothing) b lengths (ctx, smap) safe
    p' = zip (map (\(Param _ i) -> i) p) [0..]
    prefix = map (\(i, n) ->
                   AAsm {aAssign = [AVar i], aOp = Nop, aArgs = [ALoc $ AArg n]}) p'
    setup = [Push (Reg RBP),
             Mov (Reg RSP) (Reg RBP)]
    cleanup = case ep of
      Nothing -> [ACtrl $ Ret $ ALoc ARes]
      Just ep' -> [ACtrl $ Lbl (show ep'),
                   ACtrl $ Ret $ ALoc ARes]
    aasm' = prefix ++ aasm ++ cleanup
    s = ssa aasm' fun opt
    unssa = deSSA s
    (regMap, used) = allocateRegisters unssa
    program = foldr (\x -> \acc -> (show x) ++ "\n" ++ acc) "" unssa
    code = 
      case used of
        0 ->
          setup ++ (concatMap (translate regMap 0) unssa)
        x | x < 4 -> let
          save = map (\(r, i) -> Push r) $ zip [Reg RBX, Reg R12, Reg R13] [0..(x-1)]
          restore = map (\(Push r) -> Pop r) $ reverse save
          code' =  concatMap (translate regMap (x + (mod x 2))) unssa
          (front, back) = splitAt (length(code')-2) code'
          in if ((mod x 2) == 0) then setup ++ save ++ front ++ restore ++ back
             else setup ++ save ++ [Push (Reg RBP)] ++ front ++ [Pop (Reg RBP)] ++ restore ++ back
        x -> let
          save = map (\(r, i) -> Push r) $ zip [Reg RBX, Reg R12, Reg R13] [0..(x-1)]
          restore = map (\(Push r) -> Pop r) $ reverse save
          n = x-2
          code' =  concatMap (translate regMap ((x - (mod x 2))+2)) unssa
          (front, back) = splitAt (length(code')-2) code'
          sub = [Subq (Val ((n - (mod x 2) + 1)*8)) (Reg RSP)]
          add = [Addq (Val ((n - (mod x 2) + 1)*8)) (Reg RSP)]
          in setup ++ save ++ sub ++ front ++ add ++ restore ++ back
    code' = removeDead code
  in case opt >= 2 of
    False -> (fun, code', l')
    True -> (fun, asmOptimize code', l')

asmOptimize code = let
  opt = pairFold foldFun code
  in opt
  where foldFun acc (Jmp l1) (AsmLbl l2) = 
          if l1 == l2 then (Nothing, (AsmLbl l2) : acc)
          else (Just (Jmp l1), (AsmLbl l2) : acc)
        foldFun acc (Movq r1 r2) (Movq r3 r4) =
          if (r1 == r4 && r2 == r3) then (Just (Movq r1 r2), acc)
          else (Just (Movq r1 r2), (Movq r3 r4) : acc)
        foldFun acc x y = (Just x, y : acc)
        
pairFold f l = let
  (front, l') =
    foldr (\x -> \(y, acc) -> case (x,y) of
              (arg1, Just arg2) -> f acc arg1 arg2
              (_, Nothing) -> (Just x, acc)) (Nothing, []) l
  in case front of
    Just x -> x : l'
    Nothing -> l'

removeDead code = 
  filter (\inst -> case inst of
             (Movl a1 a2) -> (a1 /= a2) || (a1 == (Reg R15D)) || (a1 == (Reg R14D))
             (Movq a1 a2) -> (a1 /= a2)
             (Addq (Val 0) _) -> False
             _ -> True) code

-- updates the abstract assembly at a label
update aasm Nothing = Just aasm
update aasm (Just acc) = Just $ acc ++ aasm

updatePre aasm Nothing = Just aasm
updatePre aasm (Just acc) = Just $ aasm ++ acc

unroll (LIdent i) s = Ident i s
unroll (LDeref l) s = let
  e = unroll l s
  in ExpUnOp Deref e s
unroll (LArray l e) s = let
  a = unroll l s
  in Subscr a e s
unroll (LArrow l i) s = let
  l' = unroll l s
  in ExpBinOp Arrow l' (Ident i s) s
unroll (LDot l i) s = let
  l' = unroll l s
  in ExpBinOp Dot l' (Ident i s) s

roll (Ident i _) = LIdent i
roll (ExpUnOp Deref e _) = LDeref (roll e)
roll (Subscr a e _) = LArray (roll a) e
roll (ExpBinOp Arrow e (Ident i _) _) = LArrow (roll e) i
roll (ExpBinOp Dot e (Ident i _) _) = LDot (roll e) i
roll (ExpTernOp _ e2 _ _) = roll e2

getLvalAddr (LIdent _) _ n l _ _ _ = ([], n, l)
getLvalAddr (LDeref (LIdent i)) t n l _  _ _ =
  ([AAsm [t] Nop [ALoc $ AVar i]], n, l)
getLvalAddr (LDeref l) t n lbl ctx typs safe = let
  (aasm, n', lbl') = getLvalAddr l (ATemp n) (n+1) lbl ctx (tail typs) safe
  in (aasm ++ [AAsm [t] Nop [ALoc $ Pt $ ATemp n]], n', lbl')
getLvalAddr (LArray (LIdent i) e) t n l (ctx, smap) typs safe = let
  (exp, n', l') = genExp (n+1, l) e (ATemp n) [] (ctx, smap) safe
  (typs,size') = typecheck (Ident i (newPos "x" 1 1)) (ctx, smap) typs
  size = case size' of
    (Array Int) -> 4
    (Array Bool) -> 4
    (Array (Struct s)) -> let
      (_, size, _) = smap Map.! s in size
    _ -> 8                             
  op = case size of
    4 -> MemMov Small
    _ -> Nop
  in if safe then let
    checks = [AAsm [ATemp n'] AddrSub [ALoc $ AVar i, AImm $ fromIntegral size],
              AAsm [ATemp (n'+1)] op [ALoc $ Pt (ATemp n')],
              AAsm [ATemp (n'+2)] Nop [AImm $ fromIntegral 0],
              AAsm [ATemp (n'+3)] Geq [ALoc $ ATemp n, ALoc $ ATemp (n'+2)],
              ACtrl $ Ifz (ALoc (ATemp (n'+3))) "mem" False,
              AAsm [ATemp (n'+4)] Lt [ALoc $ ATemp n, ALoc $ ATemp (n'+1)],
              ACtrl $ Ifz (ALoc (ATemp (n'+4))) "mem" False]
    aasm = [AAsm [ATemp (n'+5)] Mul [AImm $ fromIntegral size, ALoc $ ATemp n],
            AAsm [t] AddrAdd [ALoc $ ATemp (n'+5), ALoc $ AVar i]]
    in (exp ++ checks ++ aasm, n'+6, l')
     else let
       aasm = [AAsm [ATemp n'] Mul [AImm $ fromIntegral size, ALoc $ ATemp n],
               AAsm [t] AddrAdd [ALoc $ ATemp n', ALoc $ AVar i]]
       in (exp ++ aasm, n'+1, l')
getLvalAddr (LArray l e) t n lbl (ctx, smap) typs safe = let
  e1 = unroll l (newPos "x" 1 1)
  (lvalAasm, n', lbl') = getLvalAddr l (ATemp n) (n+1) lbl (ctx, smap) (tail typs) safe
  (exp, n'', lbl'') = genExp (n'+1, lbl') e (ATemp n') [] (ctx, smap) safe
  size = case head typs of -- size' of
    (Array Int) -> 4
    (Array Bool) -> 4
    (Array (Struct s)) -> let
      (_, size, _) = smap Map.! s in size
    _ -> 8                             
  op = case size of
    4 -> MemMov Small
    _ -> Nop
  in if safe then let
    checks = [AAsm [ATemp (n''+7)] Nop [ALoc $ Pt $ ATemp n],
              AAsm [ATemp n''] AddrSub [ALoc $ ATemp (n''+7), AImm $ fromIntegral size],
              AAsm [ATemp (n''+1)] op [ALoc $ Pt (ATemp n'')],
              AAsm [ATemp (n''+2)] Nop [AImm $ fromIntegral 0],
              AAsm [ATemp (n''+3)] Geq [ALoc $ ATemp n', ALoc $ ATemp (n''+2)],
              ACtrl $ Ifz (ALoc (ATemp (n''+3))) "mem" False,
              AAsm [ATemp (n''+4)] Lt [ALoc $ ATemp n', ALoc $ ATemp (n''+1)],
              ACtrl $ Ifz (ALoc (ATemp (n''+4))) "mem" False]
    addr = [AAsm [ATemp (n''+6)] Nop [ALoc $ Pt $ ATemp n]]
    aasm = [AAsm [ATemp (n''+5)] Mul [AImm $ fromIntegral size, ALoc $ ATemp n'],
            AAsm [t] AddrAdd [ALoc $ ATemp (n''+5), ALoc $ ATemp (n''+6)]]
    in (lvalAasm ++ addr ++ exp ++ checks ++ aasm, n''+8, lbl'')
     else let
       addr = [AAsm [ATemp n''] Nop [ALoc $ Pt $ ATemp n]]
       aasm = [AAsm [ATemp (n''+1)] Mul [AImm $ fromIntegral size, ALoc $ ATemp n'],
               AAsm [t] AddrAdd [ALoc $ ATemp (n''+1), ALoc $ ATemp n'']]
       in (lvalAasm ++ addr ++ exp ++ aasm, n''+2, lbl'')
getLvalAddr (LArrow (LIdent s) i) t n lbl (ctx, smap) _ safe = let
  offset = case Map.lookup s ctx of
    Just (Pointer (Struct st)) -> case Map.lookup st smap of
      Just (_, _, m) -> case Map.lookup i m of
        Just (offset, _) -> offset
    Just (Pointer (Poly _ (Struct st))) -> case Map.lookup st smap of
      Just (_, _, m) -> case Map.lookup i m of
        Just (offset, _) -> offset
  in if safe then let
    aasm = [ACtrl $ Ifz (ALoc $ AVar s) "mem" True,
            AAsm [t] AddrAdd [ALoc $ AVar s, AImm $ fromIntegral offset]]
    in (aasm, n, lbl)
     else let
       aasm = [AAsm [t] AddrAdd [ALoc $ AVar s, AImm $ fromIntegral offset]]
       in (aasm, n, lbl)
getLvalAddr (LArrow l i) t n lbl (ctx, smap) typs safe = let
  e = unroll l (newPos "x" 1 1)
  (lvalAasm, n', lbl') = getLvalAddr l (ATemp n) (n+1) lbl (ctx, smap) (tail typs) safe
  s = case head typs of
    (Pointer (Struct i)) -> i
  offset = case Map.lookup s smap of
    Just (_, _, m) -> case Map.lookup i m of
      Just (offset, _) -> offset
  aasm = [AAsm [ATemp n'] Nop [ALoc $ Pt $ ATemp n],
          AAsm [t] AddrAdd [ALoc $ ATemp n', AImm $ fromIntegral offset]]
  in (lvalAasm ++ aasm, (n'+1), lbl')
getLvalAddr (LDot l i) t n lbl (ctx, smap) typs safe = let
  e = unroll l (newPos "x" 1 1)
  (lvalAasm, n', lbl') = getLvalAddr l (ATemp n) (n+1) lbl (ctx, smap) (tail typs) safe
  s = case head typs of
    (Struct i) -> i
  offset = case Map.lookup s smap of
    Just (_, _, m) -> case Map.lookup i m of
      Just (offset, _) -> offset
  aasm = [AAsm [t] AddrAdd [ALoc $ ATemp n, AImm $ fromIntegral offset]]
  in (lvalAasm ++ aasm, n', lbl')
 
lvalType (LIdent i) (ctx, smap) = ctx Map.! i
lvalType (LDeref l) ctx =
  case lvalType l ctx of
    (Pointer t) -> t
lvalType (LArray l _) ctx =
  case lvalType l ctx of
    (Array t) -> t
lvalType (LArrow l i) (ctx, smap) =
  case lvalType l (ctx, smap) of
    (Pointer (Struct s)) ->
      case Map.lookup s smap of
        (Just (_, _, fields)) ->
          case Map.lookup i fields of
            (Just (_, t)) -> t
    Pointer (Poly ts (Struct s)) ->
      case Map.lookup s smap of
        Just (Just l, _, fields) ->
          case Map.lookup i fields of
            Just (_, t') -> Check.findType (Map.fromList $ zip l ts) Set.empty t'
        Just (_, _, fields) ->
          case Map.lookup i fields of
            Just (_, t) -> t
lvalType (LDot l i) (ctx, smap) =
  case lvalType l (ctx, smap) of
    (Struct s) ->
      case Map.lookup s smap of
        (Just (_, _, fields)) ->
          case Map.lookup i fields of
            (Just (_, t)) -> t
     
typecheck (Ident i p) (ctx, smap) typs = let t = {-trace ((show i)++"\n"++(show ctx)) $ -}ctx Map.! i
                                             typs' = Map.insert (Ident i p) t typs
                                         in (typs',t)
typecheck (ExpUnOp Deref e _) ctx typs =
  case Map.lookup e typs of
    Just t' -> (typs,t')
    Nothing -> case typecheck e ctx typs of
      (typs',(Pointer t)) -> let typs'' = Map.insert e t typs in (typs'',t)
typecheck (App f p sp) (ctx, smap) typs =
  let f' = case f of {FuncName s->s; Ident s _->s}
      t = ctx Map.! f'
      typs' = Map.insert (App f p sp) t typs
  in (typs',t)
typecheck (ExpTernOp _ e2 e3 _) ctx typs =
  case Map.lookup e2 typs of
    Just t' -> (typs,t')
    Nothing -> let (typs',t) = typecheck e2 ctx typs
                   typs'' = Map.insert e2 t typs'
                   typs''' = Map.insert e3 t typs''
               in
                (typs''',t)
typecheck (Subscr e _ _) ctx typs = 
  case Map.lookup e typs of
    Just t' -> (typs,t')
    Nothing -> 
      case typecheck e ctx typs of
        (typs',(Array t)) -> let typs'' = Map.insert e t typs'
                             in (typs'',t)
typecheck (ExpBinOp Arrow e (Ident i _) _) (ctx, smap) typs =
  case Map.lookup e typs of
    Just t' -> (typs,t')
    Nothing -> 
      case typecheck e (ctx, smap) typs of
        (typs',(Pointer (Struct s))) ->
          case Map.lookup s smap of
            Just (_, _, m) ->
              case Map.lookup i m of
                Just (_, t) -> let typs'' = Map.insert e t typs'
                               in (typs'',t)
        (typs',(Pointer (Poly ts (Struct s)))) ->
          case Map.lookup s smap of
            Just (Just l, _, m) ->
              case Map.lookup i m of
                Just (_, t') -> (typs', Check.findType (Map.fromList $ zip l ts) Set.empty t')
            Just (_, _, m) ->
              case Map.lookup i m of
                Just (_, t) -> (typs', t)
typecheck (ExpBinOp Dot e (Ident i _) _) (ctx, smap) typs =
  case Map.lookup e typs of
    Just t' -> (typs,t')
    Nothing -> 
      case typecheck e (ctx, smap) typs of
        (typs',(Struct s)) ->
          case Map.lookup s smap of
            Just (_, _, m) ->
              case Map.lookup i m of
                Just (_, t) -> let typs'' = Map.insert e t typs'
                               in (typs'', t)
typecheck (Alloc t _) ctx typs = (typs,Pointer t)
typecheck (AllocArray t _ _) ctx typs = (typs,Array t)
                                        
------------------------

typExpr (Ident i p) (ctx, smap) l = ctx Map.! i : l
typExpr (ExpUnOp Deref e _) (ctx,smap) l =
  let l' = typExpr e (ctx, smap) l
  in case head l' of
    (Pointer t) -> t : l' 
typExpr (App (Ident f _) p sp) (ctx, smap) l = ctx Map.! f : l
typExpr (App (FuncName f) p sp) (ctx, smap) l = ctx Map.! f : l
typExpr (ExpTernOp _ e2 e3 _) (ctx, smap) l =
  typExpr e2 (ctx,smap) l
typExpr (Subscr e _ _) (ctx, smap) l = 
  let l' = typExpr e (ctx, smap) l
  in case head l' of
    (Array t) -> t : l'
typExpr (ExpBinOp Arrow e (Ident i _) _) (ctx, smap) l =
  let l' = typExpr e (ctx, smap) l
  in case head l' of
    (Pointer (Struct s)) ->
      case Map.lookup s smap of
        Just (_, _, m) ->
          case Map.lookup i m of
            Just (_, t) -> t : l'
    Pointer (Poly ts (Struct s)) ->
      case Map.lookup s smap of
        Just (Just l, _, m) ->
          case Map.lookup i m of
            Just (_, t') -> (Check.findType (Map.fromList $ zip l ts) Set.empty t') : l'
        Just (_, _, m) ->
          case Map.lookup i m of
            Just (_, t) -> t : l'
typExpr (ExpBinOp Dot e (Ident i _) _) (ctx, smap) l =
  let l' = typExpr e (ctx, smap) l
  in case head l' of
    (Struct s) ->
      case Map.lookup s smap of
        Just (_, _, m) ->
          case Map.lookup i m of
            Just (_, t) -> t : l' 
typExpr (Alloc t _) (ctx, smap) l = (Pointer t) : l
typExpr (AllocArray t _ _) (ctx, smap) l = (Array t) : l


lvaltypes (LDot lval s) ctx smap l =
  let
    l' = lvaltypes lval ctx smap l
  in
   case head l' of
     (Struct s') -> let (_, _,p) = smap Map.! s'
                        (_,t) = p Map.! s
                    in t:l'
lvaltypes (LDeref lval) ctx smap l =
  let
    l' = lvaltypes lval ctx smap l
  in
   case head l' of
     Pointer t -> t:l'
lvaltypes (LArray lval e) ctx smap l =
  let
    l' = lvaltypes lval ctx smap l
  in
   case head l' of
     Array t -> t : l'

     
genStmt acc [] _ _ _ = acc
genStmt acc ((Simp (Decl t i Nothing _) _) : xs) lens (ctx, smap) safe =
  genStmt acc xs lens ((Map.insert i t ctx), smap) safe
genStmt (acc, n, l, ep) ((Simp (Decl t i (Just e) _) _) : xs) lens (ctx, smap) safe =
  let
    (aasm, n', l') = genExp (n, l) e (AVar i) lens (ctx, smap) safe
  in genStmt (acc ++ aasm, n', l', ep) xs lens ((Map.insert i t ctx), smap) safe
genStmt (acc, n, l, ep) ((Simp (Asgn lval o e s) _) : xs) lens ctx safe =
  let
    typs = typExpr (unroll lval s) ctx []
    (compute, n', l') = getLvalAddr lval (ATemp n) (n+1) l ctx (tail typs) safe
    e1 = unroll lval s
    e' = case o of
      Nothing -> e
      Just op -> case compute of
        [] -> ExpBinOp op e1 e s
        _ -> ExpBinOp op (TempLoc n) e s
    (aasm, n'', l'') = genExp (n'+1, l') e' (ATemp n') lens ctx safe
    post = case compute of
      [] -> case lval of
        (LIdent i) -> [AAsm [AVar i] Nop [ALoc $ ATemp n']]
      _ ->
        let
          size = case lvalType lval ctx of
            Int -> Small
            Bool -> Small
            _ -> Large
        in case size of
          Small -> [AAsm [Pt $ ATemp n] (MemMov size) [ALoc $ ATemp n']]
          Large -> [AAsm [Pt $ ATemp n] Nop [ALoc $ ATemp n']]
  in genStmt (acc ++ compute ++ aasm ++ post, n'', l'', ep) xs lens ctx safe
genStmt (acc, n, l, ep) ((Simp (PostOp o lval s) _) : xs) lens ctx safe =
  let
    op = case o of
      Incr -> Add
      Decr -> Sub
    new = Simp (Asgn lval (Just op) (ExpInt Dec 1 s) s) s
  in genStmt (acc, n, l, ep) (new : xs) lens ctx safe
genStmt (acc, n, l, ep) ((Simp (Expr e _) _) : xs) lens ctx safe = 
  let
    (aasm, n', l') = genExp (n + 1, l) e (ATemp n) lens ctx safe
  in genStmt (acc ++ aasm, n', l', ep) xs lens ctx safe
genStmt (acc, n, l, ep) ((BlockStmt (Block stmts _) _) : xs) lens ctx safe = 
  let
    (aasm, n', l', ep') = genStmt ([], n, l, ep) stmts lens ctx safe
  in genStmt (acc ++ aasm, n', l', ep') xs lens ctx safe
genStmt (acc, n, l, ep) ((Ctrl (Return (Just e) _) _) : xs) lens ctx safe =
  let
    (aasm, n', l') = genExp (n, l) e (ARes) lens ctx safe
    (epilogue, l'') = case ep of
      (Just ep') -> (ep', l') 
      Nothing -> (l'+1, l'+1)
  in (acc ++ aasm ++ [ACtrl $ Goto (show epilogue)], n', l'', Just epilogue)
genStmt (acc, n, l, ep) ((Ctrl (Return Nothing _) _) : xs) _ _ _ =
  let
    (epilogue, l') = case ep of
      (Just ep') -> (ep', l) 
      Nothing -> (l+1, l+1)
  in (acc ++ [ACtrl $ Goto (show epilogue)], n, l', Just epilogue)
genStmt (acc, n, l, ep) ((Ctrl (If e s Nothing _) _) : xs) lens ctx safe =
  case e of
    (ExpBinOp op e1 e2 _) | op == Eq || op == Gt || op == Lt || op == Neq
                            || op == Geq || op == Leq -> let
      (e1code, n1, l1) = genExp (n+1, l) e1 (ATemp n) lens ctx safe
      (e2code, n2, l2) = genExp (n1+1, l1) e2 (ATemp n1) lens ctx safe
      (aasms, n3, l3, ep3) = genStmt ([], n2, l2, ep) [s] lens ctx safe
      aasm = e1code ++ e2code ++
             [ACtrl $ Comp (ALoc (ATemp n)) (ALoc (ATemp n1)) op (show $ l3+1)] ++
             [ACtrl $ Goto (show $ l3+2), ACtrl $ Lbl (show $ l3+2)] ++
             aasms ++ [ACtrl $ Goto (show $ l3+1), ACtrl $ Lbl (show $ l3+1)]
      in genStmt (acc ++ aasm, n3, l3+2, ep3) xs lens ctx safe
    _ -> let
      (aasme, n', l') = genExp (n + 1, l) e (ATemp n) lens ctx safe
      (aasms, n'', l'', ep') = genStmt ([], n', l', ep) [s] lens ctx safe
      aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l''+2) False,
              ACtrl $ Goto (show $ l''+1),
              ACtrl $ Lbl (show $ l''+1)]
      aasm' = aasme ++ aasm ++ aasms ++
              [ACtrl $ Goto (show $ l''+2), ACtrl $ Lbl (show $ l''+2)]
      in genStmt (acc ++ aasm', n'', l''+2, ep') xs lens ctx safe
genStmt (acc, n, l, ep) ((Ctrl (If e s1 (Just s2) _) _) : xs) lens ctx safe =
  case e of
   (TrueT _) -> genStmt (acc, n, l, ep) (s1 : xs) lens ctx safe
   (FalseT _) -> genStmt (acc, n, l, ep) (s2 : xs) lens ctx safe
   (ExpBinOp op e1 e2 _) | op == Eq || op == Gt || op == Lt || op == Neq
                           || op == Geq || op == Leq -> let
     (e1code, n1, l1) = genExp (n+1, l) e1 (ATemp n) lens ctx safe
     (e2code, n2, l2) = genExp (n1+1, l1) e2 (ATemp n1) lens ctx safe
     (aasms1, n3, l3, ep3) = genStmt ([], n2, l2, ep) [s1] lens ctx safe
     (aasms2, n4, l4, ep4) = genStmt ([], n3, l3, ep3) [s2] lens ctx safe
     aasm = [ACtrl $ Comp (ALoc (ATemp n)) (ALoc (ATemp n1)) op (show $ l4+2),
             ACtrl $ Goto (show $ l4+1),
             ACtrl $ Lbl (show $ l4+1)]
     aasm' = e1code ++ e2code ++ aasm ++ aasms1 ++
             [ACtrl $ Goto (show $ l4+3), ACtrl $ Lbl (show $ l4+2)] ++ aasms2 ++
             [ACtrl $ Goto (show $ l4+3), ACtrl $ Lbl (show $ l4+3)]
     in genStmt (acc ++ aasm', n4, l4+3, ep4) xs lens ctx safe
   _ -> let
     (aasme, n1, l1) = genExp (n+1, l) e (ATemp n) lens ctx safe
     (aasms1, n2, l2, ep2) = genStmt ([], n1, l1, ep) [s1] lens ctx safe
     (aasms2, n3, l3, ep3) = genStmt ([], n2, l2, ep2) [s2] lens ctx safe
     aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l3+2) False,
             ACtrl $ Goto (show $ l3+1),
             ACtrl $ Lbl (show $ l3+1)]
     aasm' = aasme ++ aasm ++ aasms1 ++
             [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+2)] ++
             aasms2 ++ [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+3)]
     in genStmt (acc ++ aasm', n3, l3+3, ep3) xs lens ctx safe
genStmt (acc, n, l, ep) ((Ctrl (While e s _) _) : xs) lens ctx safe =
  case e of
    (FalseT _) -> genStmt (acc, n, l, ep) xs lens ctx safe
    (ExpBinOp op e1 e2 _) | op == Eq || op == Gt || op == Lt || op == Neq
                            || op == Geq || op == Leq -> let
      (e1code, n1, l1) = genExp (n+1, l) e1 (ATemp n) lens ctx safe
      (e2code, n2, l2) = genExp (n1+1, l1) e2 (ATemp n1) lens ctx safe
      (aasms, n3, l3, ep1) = genStmt ([], n2, l2, ep) [s] lens ctx safe
      aasm = [ACtrl $ Goto (show $ l3+1), ACtrl $ Lbl (show $ l3+1)] ++
             e1code ++ e2code ++
             [ACtrl $ Comp (ALoc (ATemp n)) (ALoc (ATemp n1)) op (show $ l3+2)] ++
             [ACtrl $ Goto (show $ l3+3), ACtrl $ Lbl (show $ l3+3)] ++
             aasms ++
             [ACtrl $ Goto (show $ l3+1), ACtrl $ Lbl (show $ l3+2)]
      in genStmt (acc ++ aasm, n3, l3+3, ep1) xs lens ctx safe
    _ ->
      let
        (aasme, n1, l1) = genExp (n+1, l) e (ATemp n) lens ctx safe
        (aasms, n2, l2, ep') = genStmt ([], n1, l1, ep) [s] lens ctx safe
        aasm = [ACtrl $ Ifz (ALoc (ATemp n)) (show $ l2+3) False,
                ACtrl $ Goto (show $ l2+2),
                ACtrl $ Lbl (show $ l2+2)]
        aasm' = [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+1)] ++
                aasme ++ aasm ++ aasms ++
                [ACtrl $ Goto (show $ l2+1), ACtrl $ Lbl (show $ l2+3)]
      in genStmt (acc ++ aasm', n2, l2+3, ep') xs lens ctx safe
genStmt (acc, n, l, ep) ((Ctrl (For ms1 e ms2 s3 p) _) : xs) lens (ctx, smap) safe =
  let
    ((init, n1, l1, ep1), ctx') = case ms1 of
      Nothing -> (([], n, l, ep), ctx)
      (Just s1) -> case s1 of
        (Decl t s _ _) -> (genStmt ([], n, l, ep) [Simp s1 p] lens (ctx, smap) safe,
                           (Map.insert s t ctx))
        _ -> (genStmt ([], n, l, ep) [Simp s1 p] lens (ctx, smap) safe, ctx)
    (step, n2, l2, ep2) = case ms2 of
      Nothing -> ([], n1, l1, ep1)
      (Just s2) -> genStmt ([], n1, l1, ep1) [Simp s2 p] lens (ctx', smap) safe
    (body, n3, l3, ep3) = genStmt ([], n2, l2, ep2) [s3] lens (ctx', smap) safe
    in case e of
      (ExpBinOp op e1 e2 _) | op == Eq || op == Gt || op == Lt || op == Neq
                              || op == Geq || op == Leq -> let
        (e1code, n4, l4) = genExp (n3+1, l3) e1 (ATemp n3) lens (ctx', smap) safe
        (e2code, n5, l5) = genExp (n4+1, l4) e2 (ATemp n4) lens (ctx', smap) safe
        aasm = init ++ [ACtrl $ Goto (show $ l5+1), ACtrl $ Lbl (show $ l5+1)] ++
               e1code ++ e2code ++
               [ACtrl $ Comp (ALoc (ATemp n3)) (ALoc (ATemp n4)) op (show $ l5+2),
                ACtrl $ Goto (show $ l5+3), ACtrl $ Lbl (show $ l5+3)] ++
               body ++ step ++
               [ACtrl $ Goto (show $ l5+1), ACtrl $ Lbl (show $ l5+2)]
        in genStmt (acc ++ aasm, n5, l5+3, ep3) xs lens (ctx', smap) safe
      _ -> let
        (aasme, n4, l4) = genExp (n3+1, l3) e (ATemp n3) lens (ctx', smap) safe
        aasm = init ++ [ACtrl $ Goto (show $ l4+1), ACtrl $ Lbl (show $ l4+1)] ++ aasme ++
               [ACtrl $ Ifz (ALoc (ATemp n1)) (show $ l4+3) False,
                ACtrl $ Goto (show $ l4+2),
                ACtrl $ Lbl (show $ l4+2)] ++ body ++ step ++
               [ACtrl $ Goto (show $ l4+1),
                ACtrl $ Lbl (show $ l4+3)]
        in genStmt (acc ++ aasm, n4, l4+3, ep3) xs lens (ctx', smap) safe
genStmt acc ((Ctrl (Assert e _) p) : xs) lens ctx safe = let
  s = Ctrl (If (ExpUnOp LNot e p) (Simp (Expr (App (FuncName "_c0_abort") [] p) p) p) Nothing p) p
  in genStmt acc (s : xs) lens ctx safe

genExp :: (Int, Int) -> Expr -> ALoc -> [(String, Int)] ->
          (Map.Map String Type, Map.Map String (Maybe [String], Int, Map.Map String (Int, Type))) ->
          Bool -> ([AAsm], Int, Int)
genExp (n,l) (TempLoc i) loc _ _ _ = ([AAsm [loc] Nop [ALoc $ Pt $ ATemp i]], n, l)
genExp (n,l) (ExpInt _ i _) loc _ _ _ = ([AAsm [loc] Nop [AImm $ fromIntegral i]], n, l)
genExp (n,l) (Null _) loc _ _ _ = ([AAsm [loc] Nop [AImm 0]], n, l)
genExp (n,l) (TrueT _) loc _ _ _ = ([AAsm [loc] Nop [AImm 1]], n, l)
genExp (n,l) (FalseT _) loc _ _ _ = ([AAsm [loc] Nop [AImm 0]], n, l)
genExp (n,l) (Ident s _) loc _ _ _ = ([AAsm [loc] Nop [ALoc $ AVar s]], n, l)
genExp (n,l) (ExpBinOp Arrow e (Ident f _) p) loc lens (ctx, smap) safe = let
  (typs',s') = typecheck e (ctx, smap) Map.empty
  (exp, n', l') = genExp (n+1,l) e (ATemp n) lens (ctx, smap) safe
  s = case s' of
    (Pointer (Struct i)) -> i
    (Pointer (Poly _ (Struct i))) -> i
  offset = case Map.lookup s smap of
    Just (_, _, m) -> case Map.lookup f m of
      Just (offset, _) -> offset
  aasm = [AAsm [ATemp n'] AddrAdd [ALoc $ ATemp n, AImm $ fromIntegral offset],
          AAsm [loc] Nop [ALoc $ Pt $ ATemp n']]
  in (exp ++ aasm, n'+1, l')
genExp (n,l) (ExpBinOp Dot e (Ident f _) p) loc lens (ctx, smap) safe = let
  typs = typExpr e (ctx, smap) []
  (compute, n', l') = getLvalAddr (roll e) (ATemp n) (n+1) l (ctx, smap) (tail typs) safe
  s = case head typs of
    (Struct i) -> i
  offset = case Map.lookup s smap of
    Just (_, _, m) -> case Map.lookup f m of
      Just (offset, _) -> offset
  aasm = [AAsm [ATemp n'] AddrAdd [ALoc $ ATemp n, AImm $ fromIntegral offset],
          AAsm [loc] Nop [ALoc $ Pt $ ATemp n']]
  in (compute ++ aasm, n'+1, l')
genExp (n,l) (ExpBinOp LAnd e1 e2 p) loc lens ctx safe =
  genExp (n,l) (ExpTernOp e1 e2 (FalseT p) p) loc lens ctx safe
genExp (n,l) (ExpBinOp LOr e1 e2 p) loc lens ctx safe =
  genExp (n,l) (ExpTernOp e1 (TrueT p) e2 p) loc lens ctx safe
genExp (n,l) (ExpBinOp op e1 e2 p) loc lens ctx safe | op == Shl || op == Shr =
  if safe then let
    div = ExpBinOp Div (ExpInt Dec 1 p) (ExpInt Dec 0 p) p
    cond = ExpBinOp LOr (ExpBinOp Gt e2 (ExpInt Dec 31 p) p)
           (ExpBinOp Lt e2 (ExpInt Dec 0 p) p) p
    sop = case op of
      Shl -> SShl
      Shr -> SShr
    in genExp (n,l) (ExpTernOp cond div (ExpBinOp sop e1 e2 p) p) loc lens ctx safe
  else let
    sop = case op of
      Shl -> SShl
      Shr -> SShr
    in genExp (n,l) (ExpBinOp sop e1 e2 p) loc lens ctx safe
genExp (n,l) (ExpBinOp op e1 e2 _) loc lens ctx safe = 
  case (op, e1, e2) of
    (Add, ExpInt _ i1 _, ExpInt _ i2 _) ->
      ([AAsm [loc] Nop [AImm $ fromIntegral $ i1 + i2]], n, l)
    _ -> let
      (i1, n', l') = genExp (n + 1, l) e1 (ATemp n) lens ctx safe
      (i2, n'', l'') = genExp (n' + 1, l') e2 (ATemp n') lens ctx safe
      aasm  = [AAsm [loc] op [ALoc $ ATemp n, ALoc $ ATemp $ n']]
      in (i1 ++ i2 ++ aasm, n'', l'')
genExp (n,l) (ExpUnOp FnPtr (Ident f _) _) loc lens ctx safe =
  let aasm = [ACtrl $ Lea f $ ALoc loc]
  in (aasm, n+1, l)
genExp (n,l) (ExpUnOp Deref e _) loc lens ctx safe = let
  (aasm, n', l') = genExp (n+1, l) e (ATemp n) lens ctx safe
  in (aasm ++ [AAsm [loc] Nop [ALoc $ Pt $ ATemp n]], n', l')
genExp (n,l) (ExpUnOp BNot (ExpUnOp BNot e _) _) loc lens ctx safe = 
  genExp (n,l) e loc lens ctx safe
genExp (n,l) (ExpUnOp LNot (ExpBinOp op e1 e2 p) _) loc lens ctx safe | op == Gt ||
                                                                        op == Geq ||
                                                                        op == Lt ||
                                                                        op == Leq =
  let
    op' = case op of
      Gt -> Leq
      Geq -> Lt
      Lt -> Geq
      Leq -> Gt
  in genExp (n,l) (ExpBinOp op' e1 e2 p) loc lens ctx safe
genExp (n,l) (ExpUnOp op e _) loc lens ctx safe = let
  (i1, n', l') = genExp (n + 1, l) e (ATemp n) lens ctx safe
  aasm = [AAsm [loc] op [ALoc $ ATemp n]]
  in (i1 ++ aasm, n', l')
genExp (n, l) (ExpTernOp e1 e2 e3 _) loc lens ctx safe = 
  case e1 of
    (TrueT _) -> genExp (n, l) e2 loc lens ctx safe
    (FalseT _) -> genExp (n, l) e3 loc lens ctx safe
    _ -> let
      (i2, n1, l1) = genExp (n+1, l) e2 (ATemp n) lens ctx safe
      (i3, n2, l2) = genExp (n1+1, l1) e3 (ATemp n1) lens ctx safe
      in case e1 of
        (ExpBinOp op e1' e2' _) | op == Eq || op == Gt || op == Lt || op == Neq
                                  || op == Geq || op == Leq -> let
          (e1code, n3, l3) = genExp (n2+1,l2) e1' (ATemp n2) lens ctx safe
          (e2code, n4, l4) = genExp (n3+1,l3) e2' (ATemp n3) lens ctx safe
          aasm = e1code ++ e2code ++
                 [ACtrl $ Comp (ALoc (ATemp n2)) (ALoc (ATemp n3)) op (show $ l4+1),
                  ACtrl $ Goto (show $ l4+2), ACtrl $ Lbl (show $ l4+2)] ++
                 i2 ++ [AAsm [loc] NoTouch [ALoc $ ATemp n],
                        ACtrl $ Goto (show $ l4+3), ACtrl $ Lbl (show $ l4+1)] ++
                 i3 ++ [AAsm [loc] NoTouch [ALoc $ ATemp n1],
                        ACtrl $ Goto (show $ l4+3), ACtrl $ Lbl (show $ l4+3)]
          in (aasm, n4, l4+3)
        _ -> let
          (i1, n3, l3) = genExp (n2+1, l2) e1 (ATemp n2) lens ctx safe
          aasm = i1 ++ [ACtrl $ Ifz (ALoc (ATemp n2)) (show $ l3+2) False,
                        ACtrl $ Goto (show $ l3+1),
                        ACtrl $ Lbl (show $ l3+1)] ++
                 i2 ++ [AAsm [loc] NoTouch [ALoc $ ATemp n],
                        ACtrl $ Goto (show $ l3+3),
                        ACtrl $ Lbl (show $ l3+2)] ++
                 i3 ++ [AAsm [loc] NoTouch [ALoc $ ATemp n1],
                        ACtrl $ Goto (show $ l3+3),
                        ACtrl $ Lbl (show $ l3+3)]
          in (aasm, n3, l3+3)
genExp (n, l) (App f es _) loc lens ctx safe =
  let
    (computeArgs, temps, n', l') =
      foldr (\e -> \(aasm, temps, n1, l1) -> let
                (code, n2, l2) = genExp (n1+1, l1) e (ATemp n1) lens ctx safe
                in (code ++ aasm, n1 : temps, n2, l2)) ([], [], n, l) es
    (front,rest) = splitAt 6 temps
    moveFrontArgs = map (\(i, t) ->
                          AAsm {aAssign = [AArg i], aOp = Nop, aArgs = [ALoc $ ATemp t]})
                    $ zip [0..] front
    call = case f of
      Ident s _ -> ([ACtrl $ Call s rest] ++ [AAsm {aAssign = [loc], aOp = Nop, aArgs = [ALoc $ ARes]}], n',l')
      FuncName s -> ([ACtrl $ Call s rest] ++ [AAsm {aAssign = [loc], aOp = Nop, aArgs = [ALoc $ ARes]}], n',l')
      ExpUnOp Deref f _ -> let (aasm,n'',l'') = genExp (n'+1,l') f (ATemp n') lens ctx safe in
        (aasm ++ [ACtrl $ CallFn (ALoc $ ATemp n') rest, AAsm {aAssign=[loc], aOp = Nop, aArgs=[ALoc $ ARes]}],n'',l'')
    (caasm, n'', l'') = call
    aasm = computeArgs ++ moveFrontArgs ++ caasm
  in (aasm, n'', l'')
genExp (n, l) (Subscr e1 e2 _) loc lens ctx safe =
  let 
    (typs',size') = typecheck e1 ctx Map.empty
    size = case size' of
      (Array Int) -> 4
      (Array Bool) -> 4
      (Array _) -> 8
    (exp1, n1, l1) = genExp (n+1, l) e1 (ATemp n) lens ctx safe
    (exp2, n2, l2) = genExp (n1+1, l1) e2 (ATemp n1) lens ctx safe
    op = case size of
      4 -> MemMov Small
      8 -> Nop
  in if safe then let
       checks = [AAsm [ATemp n2] AddrSub [ALoc $ ATemp n, AImm $ fromIntegral size],
                 AAsm [ATemp (n2+1)] op [ALoc $ Pt (ATemp n2)],
                 AAsm [ATemp (n2+2)] Nop [AImm $ fromIntegral 0],
                 AAsm [ATemp (n2+3)] Geq [ALoc $ ATemp n1, ALoc $ ATemp (n2+2)],
                 ACtrl $ Ifz (ALoc (ATemp (n2+3))) "mem" False,
                 AAsm [ATemp (n2+4)] Lt [ALoc $ ATemp n1, ALoc $ ATemp (n2+1)],
                 ACtrl $ Ifz (ALoc (ATemp (n2+4))) "mem" False]
       aasm = [AAsm [ATemp (n2+5)] Mul [AImm $ fromIntegral size, ALoc $ ATemp n1],
               AAsm [ATemp (n2+6)] AddrAdd [ALoc $ ATemp (n2+5), ALoc $ ATemp n],
               AAsm [loc] Nop [ALoc $ Pt $ ATemp (n2+6)]]
       in (exp1 ++ exp2 ++ checks ++ aasm, n2+7, l2+1)
     else let
       aasm = [AAsm [ATemp n2] Mul [AImm $ fromIntegral size, ALoc $ ATemp n1],
               AAsm [ATemp (n2+1)] AddrAdd [ALoc $ ATemp n2, ALoc $ ATemp n],
               AAsm [loc] Nop [ALoc $ Pt $ ATemp (n2+1)]]
       in (exp1 ++ exp2 ++ aasm, n2+2, l2+1)
genExp (n, l) (Alloc t _) loc lens (ctx, smap) safe =
  let
    size = case t of
      Int -> 4
      Bool -> 4
      (Pointer _) -> 8
      (Array _) -> 8
      (Struct s) -> case Map.lookup s smap of
        Just (_, i, _) -> i
      Poly _ (Struct s) -> case Map.lookup s smap of
        Just (_, i, _) -> i
    aasm = [AAsm [AArg 1] Nop [AImm $ fromIntegral size],
            AAsm [AArg 0] Nop [AImm $ fromIntegral 1],
            ACtrl $ Call "_c0_calloc" [],
            AAsm [loc] Nop [ALoc $ ARes]]
  in (aasm, n, l)
genExp (n, l) (AllocArray t e _) loc lens (ctx, smap) safe =
  let
    size = case t of
      Int -> 4
      Bool -> 4
      (Pointer _) -> 8
      (Array _) -> 8
      (Struct s) -> let
        (_, size, _) = smap Map.! s in size
    (exp, n', l') = genExp (n+1, l) e (ATemp n) lens (ctx, smap) safe
    aasm = case safe of
      True -> [AAsm [ATemp (n'+2)] Nop [AImm $ fromIntegral 0],
               AAsm [ATemp (n'+3)] Geq [ALoc $ ATemp n, ALoc $ ATemp (n'+2)],
               ACtrl $ Ifz (ALoc (ATemp (n'+3))) "mem" False,
               AAsm [AArg 1] Nop [AImm $ fromIntegral size],
               AAsm [AArg 0] (MemMov Small) [ALoc $ ATemp n],
               AAsm [AArg 0] AddrAdd [ALoc $ AArg 0, AImm $ fromIntegral 1],
               ACtrl $ Call "_c0_calloc" [],
               AAsm [ATemp (n'+1)] Nop [ALoc $ ARes]]
      False -> [AAsm [AArg 1] Nop [AImm $ fromIntegral size],
                AAsm [AArg 0] (MemMov Small) [ALoc $ ATemp n],
                AAsm [AArg 0] AddrAdd [ALoc $ AArg 0, AImm $ fromIntegral 1],
                ACtrl $ Call "_c0_calloc" [],
                AAsm [ATemp (n'+1)] Nop [ALoc $ ARes]]
    writeSize = case size of
      4 -> [AAsm [Pt $ ATemp (n'+1)] (MemMov Small) [ALoc $ ATemp n]]
      _ -> [AAsm [Pt $ ATemp (n'+1)] Nop [ALoc $ ATemp n]]
    incr = [AAsm [loc] AddrAdd [ALoc $ ATemp (n'+1), AImm $ fromIntegral size]]
  in (exp ++ aasm ++ writeSize ++ incr, n'+4, l')

-- 32 -> 32 Mov or (Lower half 64) -> 32 Mov
translate regMap n (AAsm {aAssign = [dest], aOp = (MemMov Small), aArgs = [src]}) =
  let
    s = fullReg $ regFind regMap src
    d = fullReg $ regFind regMap (ALoc dest)
  in 
   case (s,d) of
     (Loc x, Loc y) ->
       [Movq x (Reg R14),
        Movq (Loc $ Reg R14) (Reg R14),
        Movq y (Reg R15),
        Movl (Reg R14D) (Loc $ Reg R15)]
     (Reg _, Loc (Reg _)) ->
       [Movl (regFind regMap src) d]
     (Val _, Loc (Reg _)) ->
       [Movl s d]
     (_, Loc y) ->
       [Movq s (Reg R14),
        Movq y (Reg R15),
        Movl (Reg R14D) (Loc $ Reg R15)]
     (Loc (Reg _), Reg _) ->
       [Movq s d]
     (Loc x, _) ->
       [Movq x (Reg R15),
        Movq (Loc $ Reg R15) (Reg R15),
        Movl (Reg R15D) $ regFind regMap (ALoc dest)]
     (Reg (SpillArg i), _) ->
       [Movq (Stk ((i+n+1)*8)) (Reg R15),
        Movl (Reg R15D) $ regFind regMap (ALoc dest)] 
     _ ->
       [Movq s (Reg R15),
        Movl (Reg R15D) $ regFind regMap (ALoc dest)]
-- 64 -> 64 Mov
translate regMap n (AAsm {aAssign = [dest], aOp = op, aArgs = [src]}) | op == Nop ||
                                                                        op == NoTouch =
  let
    s = fullReg $ regFind regMap src
    d = fullReg $ regFind regMap (ALoc dest)
  in
   case (s, d) of
     (Val _, Reg _) ->
       [Movq s d]
     (Val _, Loc (Reg _)) ->
       [Movq s d]
     (Reg (SpillArg i), Reg _) ->
       [Movq (Stk ((i+n+1)*8)) d]
     (Reg (SpillArg i), _) ->
       [Movq (Stk ((i+n+1)*8)) (Reg R15),
        Movq (Reg R15) d]
     (Reg _, Reg _) ->
       [Movq s d]
     (Stk i, Reg y) -> 
       [Movq (Stk i) (Reg y)]
     (Reg x, Stk i) -> 
       [Movq (Reg x) (Stk i)]
     (Loc x, Loc y) ->
       [Movq x (Reg R14),
        Movq (Loc $ Reg R14) (Reg R14),
        Movq y (Reg R15),
        Movq (Reg R14) (Loc $ Reg R15)]
     (Reg _, Loc (Reg _)) ->
       [Movq s d]
     (_, Loc y) ->
       [Movq s (Reg R14),
        Movq y (Reg R15),
        Movq (Reg R14) (Loc $ Reg R15)]
     (Loc (Reg _), Reg _) ->
       [Movq s d]
     (Loc x, _) ->
       [Movq x (Reg R15),
        Movq (Loc $ Reg R15) (Reg R15),
        Movq (Reg R15) d]
     _ ->
       [Movq s (Reg R15),
        Movq (Reg R15) d]
-- (64, 64) -> 64 addition
translate regMap _ (AAsm {aAssign = [dest], aOp = AddrAdd, aArgs = [src1, src2]}) =
  let
    d = fullReg $ regFind regMap (ALoc dest)
    s1 = fullReg $ regFind regMap src1
    s2 = fullReg $ regFind regMap src2
  in case (s1, s2) of
    (Reg _, Val _) -> if s1 == d then [Addq s2 d]
                      else [Movq s1 d, Addq s2 d]
    (Val _, Reg _) -> if s2 == d then [Addq s1 d]
                      else [Movq s2 d, Addq s1 d]
    (Reg x, Reg y) -> if s2 == d then [Addq s1 s2]
                      else if s1 == d then [Addq s2 s1]
                           else [Movq s2 d, Addq s1 d]
    (Stk _, Val _) -> if s1 == d then [Addq s2 d]
                      else case d of
                        (Stk _) -> [Movq s1 (Reg R15),
                                    Movq (Reg R15) d,
                                    Addq s2 d]
                        _ -> [Movq s1 d, Addq s2 d]
    (Val _, Stk _) -> if s2 == d then [Addq s1 d]
                      else case d of
                        (Stk _) -> [Movq s2 (Reg R15),
                                    Movq (Reg R15) d,
                                    Addq s1 d]
                        _ -> [Movq s2 d, Addq s1 d]
    (Stk i, Reg y) -> if s1 == d then [Addq s2 s1]
                      else if s2 == d then [Addq s1 s2]
                           else [Movq s1 (Reg R15), Movq (Reg R15) d, Addq s2 d]
    (Reg x, Stk i) -> if s1 == d then [Addq s2 s1]
                      else if s2 == d then [Addq s1 s2]
                           else [Movq s2 (Reg R15), Movq (Reg R15) d, Addq s1 d]
    (Stk i, Stk j) -> if s1 == d then [Movq s2 (Reg R15), Addq (Reg R15) s1]
                      else if s2 == d then [Movq s1 (Reg R15), Addq (Reg R15) s2]
                           else [Movq s1 (Reg R15), Addq s2 (Reg R15), Movq (Reg R15) d]
    _ ->
     [Movq s1 (Reg R15),
      Movq s2 (Reg R14),
      Addq (Reg R14) (Reg R15),
      Movq (Reg R15) d]
-- (64, 64) -> 64 subtraction
translate regMap _ (AAsm {aAssign = [dest], aOp = AddrSub, aArgs = [src1, src2]}) =
  let
    d = fullReg $ regFind regMap (ALoc dest)
    s1 = fullReg $ regFind regMap src1
    s2 = fullReg $ regFind regMap src2
  in case (s1,s2) of
{-    (Reg _, Reg _) | s1 == d -> [Subq s2 s1]
    (Reg _, Reg _) | s2 == d -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Reg _, Reg _) -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Reg _, Stk _) | s1 == d -> [Subq s2 s1]
    (Reg _, Stk _) | s2 == d -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Reg _, Stk _) -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Stk _, Reg _) | s1 == d -> [Subq s2 s1]
    (Stk _, Reg _) | s2 == d -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Stk _, Reg _) -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Stk _, Stk _) | s1 == d -> [Movq s2 (Reg R15), Subq (Reg R15) s1]
    (Stk _, Stk _) | s2 == d -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d]
    (Stk _, Stk _) -> [Movq s1 (Reg R15), Subq s2 (Reg R15), Movq (Reg R15) d] -}
    _ ->
      [Movq s1 (Reg R15),
       Movq s2 (Reg R14),
       Subq (Reg R14) (Reg R15),
       Movq (Reg R15) d]
translate regMap _ (AAsm {aAssign = [dest], aOp = Add, aArgs = [src1, src2]}) =
  let
    dest' = regFind regMap (ALoc dest)
    s = regFind regMap src1
    s2 = regFind regMap src2
  in
   case (s, s2) of
     (Val _, Reg _) ->
       [Movl s2 dest',
        Addl s dest']
     (Reg _, Val _) ->
       [Movl s dest',
        Addl s2 dest']
     (Stk _, _) ->
       if s2 == dest' then
         [Movl s (Reg R15D),
          Addl (Reg R15D) s2] else
       case dest' of
         (Reg _) ->
           if s2 == dest' then
              [Addl s dest']
           else 
             [Movl s dest',
              Addl s2 dest']
         _ ->
           [Movl s (Reg R15D),
            Addl s2 (Reg R15D),
            Movl (Reg R15D) dest']
     (_, Stk _) ->
       case dest' of
         (Reg _) ->
           if s == dest' then
             [Addl s2 dest']
           else
             [Movl s2 dest',
              Addl s dest']
         _ ->
           [Movl s2 (Reg R15D),
            Addl s (Reg R15D),
            Movl (Reg R15D) dest']
     _ ->
       if s == dest' then
         [Movl s dest',
          Addl s2 dest']
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
     (Stk _, _) ->
       case dest' of
         (Reg _) ->
           [Movl s dest',
            Subl s2 dest']
         _ ->
           [Movl s (Reg R15D),
            Subl s2 (Reg R15D),
            Movl (Reg R15D) dest']
     (_, Stk _) ->
       [Movl s (Reg R15D),
        Subl s2 (Reg R15D),
        Movl (Reg R15D) dest']
     _ ->
       if s2 == dest' then
         if s == s2 then
         [Negl s2,
          Movl s (Reg R15D),
          Addl (Reg R15D) s2] else
           [Negl s2,
            Addl s s2]
       else
         [Movl s dest',
          Subl s2 dest']
translate regMap _ (AAsm {aAssign = [dest], aOp = Mul, aArgs = [src1, src2]}) =
  let
    d = fullReg $ regFind regMap (ALoc dest)
    s1 = regFind regMap src1
    s2 = regFind regMap src2
  in case (s1, s2, d) of
    (Val _, Reg _, Reg _) ->
      [Movl s2 (Reg R15D),
       Imull s1 (Reg R15D),
       Movq (Reg R15) d]
    (Reg _, Reg _, Reg _) ->
      [Movl s1 (Reg R15D),
       Imull s2 (Reg R15D),
       Movq (Reg R15) d]
    _ ->
      [Movl s1 (Reg R14D),
       Movl s2 (Reg R15D),
       Imull (Reg R14D) (Reg R15D),
       Movq (Reg R15) d]
translate regMap _ (AAsm {aAssign = [dest], aOp = Div, aArgs = [src1, src2]}) =
  let
    s2 = regFind regMap src2
    s2' = case s2 of
      (Val _) -> Reg R15D
      x -> x
    stuff =
      [Movl (regFind regMap src1) (Reg EAX),
       Cdq,
       Idivl s2',
       Movl (Reg EAX) (regFind regMap (ALoc dest))]
  in case s2 of
    (Val _) -> [Movl s2 (Reg R15D)] ++ stuff
    Reg EAX -> [Movl (Reg EAX) (Reg R15D),
                Movl (regFind regMap src1) (Reg EAX),
                Cdq,
                Idivl (Reg R15D),
                Movl (Reg EAX) (regFind regMap (ALoc dest)),
                Movl (Reg R15D) (Reg EAX)]
    Reg EDX -> [Movl (Reg EDX) (Reg R15D),
                Movl (regFind regMap src1) (Reg EAX),
                Cdq,
                Idivl (Reg R15D),
                Movl (Reg EAX) (regFind regMap (ALoc dest)),
                Movl (Reg R15D) (Reg EDX)]
    _ -> stuff
translate regMap _ (AAsm {aAssign = [dest], aOp = Mod, aArgs = [src1, src2]}) =
  let
    s2 = regFind regMap src2
    s2' = case s2 of
      (Val _) -> Reg R15D
      x -> x
    stuff =
      [Movl (regFind regMap src1) (Reg EAX),
       Cdq,
       Idivl s2',
       Movl (Reg EDX) (regFind regMap (ALoc dest))]
  in case s2 of
    (Val _) -> [Movl s2 (Reg R15D)] ++ stuff
    Reg EAX -> [Movl (Reg EAX) (Reg R15D),
                Movl (regFind regMap src1) (Reg EAX),
                Cdq,
                Idivl (Reg R15D),
                Movl (Reg EDX) (regFind regMap (ALoc dest)),
                Movl (Reg R15D) (Reg EAX)]
    Reg EDX -> [Movl (Reg EDX) (Reg R15D),
                Movl (regFind regMap src1) (Reg EAX),
                Cdq,
                Idivl (Reg R15D),
                Movl (Reg EDX) (regFind regMap (ALoc dest)),
                Movl (Reg R15D) (Reg EDX)]
    _ -> stuff
translate regMap _ (AAsm {aAssign = [dest], aOp = Neg, aArgs = [src]}) =
  let
    d = regFind regMap (ALoc dest)
    s = regFind regMap src
  in
   case (s, d) of
     (Stk _, Stk _) ->
       [Movl s (Reg R15D),
        Movl (Reg R15D) d,
        Negl d]
     _ ->
       [Movl s d,
        Negl d]
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
translate regMap n (ACtrl (Lea f aval)) = 
  let reg = fullReg $ regFind regMap aval
  in
   case reg of
     (Reg _) -> [Leaq ("_c0_"++f++"(%rip)") reg]
     _ -> [Leaq ("_c0_"++f++"(%rip)") (Reg R15), Movq (Reg R15) reg]
translate regMap n (ACtrl (CallFn aval ts)) = let
  (l, _) = 
    foldr (\t -> \(acc, i) -> 
            case regFind regMap $ ALoc $ ATemp t of
              (Stk j) -> ([Movl (Stk j) (Reg R15D),
                           Movl (Reg R15D) (Stk (-i*8))] : acc, i+1)
              s -> ([Movl s (Stk (-i*8))] : acc, i+1)) ([], 1) ts
  saves = concat l
  restores = map (\(Movl x y) -> Movl y x) (reverse saves)
  reg = fullReg $ regFind regMap aval
  in if (length ts) > 0 then
       if (mod (length ts) 2) == 1 then let
           (l, _) = 
             foldr (\t -> \(acc, i) -> 
                     case regFind regMap $ ALoc $ ATemp t of
                       (Stk j) -> ([Movl (Stk (j+8)) (Reg R15D),
                                    Movl (Reg R15D) (Stk (-i*8))] : acc, i+1)
                       s -> ([Movl s (Stk (-i*8))] : acc, i+1)) ([], 1) ts
           saves = concat l
           restores = map (\(Movl x y) -> Movl y x) (reverse saves)
           in
            case reg of
              (Reg _) -> saves ++ [AsmCallFn reg] ++ restores
              _ -> saves ++ [Movq reg (Reg R15), AsmCallFn (Reg R15)] ++ restores
       else
         saves ++ [Subq (Val $ (length ts)*8) (Reg RSP)] ++ [AsmCallFn reg] ++ 
         [Addq (Val $ (length ts)*8) (Reg RSP)] ++ restores
     else
       [AsmCallFn reg]
translate regMap n (ACtrl (Call s ts)) = let
  (l, _) = 
    foldr (\t -> \(acc, i) -> 
            case regFind regMap $ ALoc $ ATemp t of
              (Stk j) -> ([Movl (Stk j) (Reg R15D),
                           Movl (Reg R15D) (Stk (-i*8))] : acc, i+1)
              s -> ([Movl s (Stk (-i*8))] : acc, i+1)) ([], 1) ts
  saves = concat l
  restores = map (\(Movl x y) -> Movl y x) (reverse saves)
  in if (length ts) > 0 then
       if (mod (length ts) 2) == 1 then let
           (l, _) = 
             foldr (\t -> \(acc, i) -> 
                     case regFind regMap $ ALoc $ ATemp t of
                       (Stk j) -> ([Movl (Stk (j+8)) (Reg R15D),
                                    Movl (Reg R15D) (Stk (-i*8))] : acc, i+1)
                       s -> ([Movl s (Stk (-i*8))] : acc, i+1)) ([], 1) ts
           saves = concat l
           restores = map (\(Movl x y) -> Movl y x) (reverse saves) in
           [Subq (Val 8) (Reg RSP)] ++
           saves ++ [Subq (Val $ (length ts)*8) (Reg RSP)] ++ [AsmCall s] ++ 
           [Addq (Val $ (length ts)*8) (Reg RSP)] ++ restores ++ [Addq (Val 8) (Reg RSP)]
       else
         saves ++ [Subq (Val $ (length ts)*8) (Reg RSP)] ++ [AsmCall s] ++ 
         [Addq (Val $ (length ts)*8) (Reg RSP)] ++ restores
     else
       [AsmCall s]
translate regMap _ (ACtrl (Ret (ALoc loc))) =
  [Pop (Reg RBP), AsmRet]
translate regMap _ (ACtrl (Lbl l)) = 
  [AsmLbl l]
translate regMap _ (ACtrl (Goto l)) = 
  [Jmp l]
translate regMap _ (ACtrl (Ifz v l False)) =
  let
    v' = regFind regMap v
  in 
   case v' of
     (Stk _) -> [Movl v' (Reg R15D), 
                 Movzbl (Reg R15B) (Reg R15D),
                 Testl (Reg R15D) (Reg R15D), 
                 Je l]
     (Val i) -> [Movl v' (Reg R15D), Testl (Reg R15D) (Reg R15D), Je l]
     _ -> [Movzbl (lowerReg v') v', Testl v' v', Je l]
translate regMap _ (ACtrl (Ifz v l True)) =
  let
    v' = fullReg $ regFind regMap v
  in 
   case v' of
     (Stk _) -> [Movq v' (Reg R15), 
                 Testq (Reg R15) (Reg R15), 
                 Je l]
     (Val i) -> [Movl v' (Reg R15), Testq (Reg R15) (Reg R15), Je l]
     _ -> [Testl v' v', Je l]
translate regMap _ (ACtrl (Comp v1' v2' op l)) | op == Eq || op == Neq =
  let
    v1 = regFind regMap v1'
    v2 = regFind regMap v2'
    jump = case op of
      Eq -> Jne
      Neq -> Je
  in case (v1, v2) of
    (Val _, Val _) ->
      [Movl v1 (Reg R15D),
       Cmpl v2 (Reg R15D),
       jump l]
    (_, Val _) ->
      [Cmpl v2 v1,
       jump l]
    (Val _, _) ->
      [Cmpl v1 v2,
       jump l]
    (Stk _, Stk _) ->
      [Movl v1 (Reg R15D),
       Cmpl v2 (Reg R15D),
       jump l]
    _ ->
      [Cmpl v1 v2,
       jump l]
translate regMap _ (ACtrl (Comp v1' v2' op l)) =
  let
    v1 = regFind regMap v1'
    v2 = regFind regMap v2'
    jump = case op of
      Lt -> Jge
      Gt -> Jle
      Leq -> Jg
      Geq -> Jl
    jump' = case op of
      Lt -> Jle
      Gt -> Jge
      Leq -> Jl
      Geq -> Jg
  in case (v1, v2) of
    (Val _, Val _) ->
      [Movl v1 (Reg R15D),
       Cmpl v2 (Reg R15D),
       jump l]
    (_, Val _) ->
      [Cmpl v2 v1,
       jump l]
    (Val _, _) ->
      [Cmpl v1 v2,
       jump' l]
    (Stk _, Stk _) ->
      [Movl v1 (Reg R15D),
       Cmpl v2 (Reg R15D),
       jump l]
    _ ->
      [Cmpl v2 v1,
       jump l]
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
     _ -> case s2 of
       Val i ->
         [Movl s1 dest',
          asm (Val i) dest']
       _ ->
         [Movl s2 (Reg ECX),
          Movl s1 dest',
          asm (Reg CL) dest']
translate _ _ x = trace (show x) []

                
{- TODO: we should think abou a better way to do this. In most (all?)
cases its just zero testing. Find a way to use testl along with subtraction
for inequalities. Cmpl is restrictive with no constants in the second
argument and that makes me sad :(
-}
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
    s2' = case s2 of
      (Val _) -> Reg R14D
      _ -> s2
    stuff = 
      case (dest', s1, s2') of
        (Stk _, Stk _, Stk _) ->
          [Movl s1 (Reg R15D),
           Cmpl (Reg R15D) s2',
           asm (Reg R15B),
           Movzbl (Reg R15B) (Reg R15D),
           Movl (Reg R15D) dest']
        (Stk _, _, _) ->
          [Cmpl s1 s2',
           asm (Reg R15B),
           Movzbl (Reg R15B) (Reg R15D),
           Movl (Reg R15D) dest']
        (_, Stk _, Stk _) ->
          [Movl s1 (Reg R15D),
           Cmpl (Reg R15D) s2',
           asm (Reg R15B),
           Movzbl (Reg R15B) dest']
        _ ->
          [Cmpl s1 s2',
           asm (Reg R15B),
           Movzbl (Reg R15B) dest']
  in case s2 of
    (Val _) -> [Movl s2 (Reg R14D)] ++ stuff
    _ -> stuff

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
fullReg (Loc r) = Loc (fullReg r)
fullReg x = x
