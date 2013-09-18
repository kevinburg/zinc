{- L1 Compiler
   Author: Matthew Maurer <mmaurer@andrew.cmu.edu>
   Modified by: Ryan Pearl <rpearl@andrew.cmu.edu>

   Beginnings of a typechecker
-}
module Compile.CheckAST where

import Control.Monad.State
import Control.Monad.Error
import Control.Monad

import qualified Data.Set as Set

import Compile.Types

-- Note to the student
-- When your checker gets larger, you may wish to formalize the state
-- a little more.

-- This is hacky and not designed to scale.

runErrorState :: ErrorT String (State s) a -> s -> Either String a
runErrorState m s = evalState (runErrorT m) s

assertMsg :: (Monad m) => String -> Bool -> ErrorT String m ()
assertMsg s True  = return ()
assertMsg s False = throwError s

assertMsgE :: String -> Bool -> Either String ()
assertMsgE s True  = Right ()
assertMsgE s False = Left s

declName (Decl name _ _) = name

getDecls y = filter pred y
             where
               pred = (\x -> case x of
                          (Decl _ _ _) -> True
                          _ -> False
                      )

checkAST :: AST -> Either String ()
checkAST ast@(Block stmts _) = do
  let decls = getDecls stmts
      variables = Set.fromList $ map declName decls
  assertMsgE (findDuplicate decls)
             $ (length decls) == (Set.size variables)
  rets <- fmap or $ runErrorState (mapM checkStmt stmts) $
                                  (Set.empty, Set.empty, False)
  assertMsgE "main does not return" rets

checkStmt (Return e _) = do
  (vars, defined, ret) <- get
  checkExpr e
  put (vars, defined, True)
  return True
checkStmt (Asgn i m e p) = do
  (vars, defined, ret) <- get
  assertMsg (i ++ " not declared at " ++ (show p)) (Set.member i vars)
  case m of
    Just _  -> assertMsg (i ++ " used undefined at " ++ (show p))
                         ((Set.member i defined) || ret)
    Nothing -> return ()
  checkExpr e
  put (vars, Set.insert i defined, ret)
  return False
checkStmt (Decl i Nothing _) = do
  (vars, defined, ret) <- get
  put (Set.insert i vars, defined, ret)
  return False
checkStmt (Decl i (Just e) _) = do
  (vars, defined, ret) <- get
  checkExpr e
  put (Set.insert i vars, Set.insert i defined, ret)
  return False

checkExpr (ExpInt Dec n p) =
  assertMsg ((show n) ++ " too large at " ++ (show p))
            (n <= 2^31)
checkExpr (ExpInt Hex n p) =
  assertMsg ((show n) ++ " too large at " ++ (show p))
            (n < 2^32)
checkExpr (Ident s p) = do
  (vars, defined, ret) <- get
  assertMsg (s ++ " used undeclared at " ++ (show p)) (Set.member s vars)
  assertMsg (s ++ " used undefined at " ++ (show p)) ((Set.member s defined) || ret)
checkExpr (ExpBinOp _ e1 e2 _) = mapM_ checkExpr [e1, e2]
checkExpr (ExpUnOp _ e _) = checkExpr e

findDuplicate xs = findDuplicate' xs Set.empty
  where findDuplicate' [] _ = error "no duplicate"
        findDuplicate' (Decl x _ pos : xs) s =
          if Set.member x s
            then x ++ " re-declared at " ++ (show pos)
            else findDuplicate' xs (Set.insert x s)
