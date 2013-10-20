{- L2 Compiler
   Authors: Kevin Burg <kburg@andrew.cmu.edu>
            John Cole <jhcole@andrew.cmu.edu>
-}
module Compile.Parse where

import Control.Monad.Error
import Data.ByteString as BS
import Data.ByteString.Char8 as C8
import Compile.Types

import LiftIOE

import Text.ParserCombinators.Parsec hiding (try)
import Control.Monad.Identity                 -- For our custom Language Definition
import Text.Parsec hiding (parse)             -- Parser Combinators
import Text.Parsec.Expr                       -- Expression Parser Generator
import Text.Parsec.Token (GenLanguageDef(..)) -- Language Definition Structure
import qualified Text.Parsec.Token as Tok

import Debug.Trace

parseAST :: FilePath -> ErrorT String IO Program
parseAST file = do
  code <- liftIOE $ BS.readFile file
  case parse programParser file code of
    Left e  -> throwError (show e)
    Right a -> return a

type C0Parser = Parsec ByteString ()

programParser :: C0Parser Program
programParser = do
  whiteSpace
  gdecls <- gdecls
  return $ Program gdecls
  <?> "program"

gdecls :: C0Parser [GDecl]
gdecls = try (do
                 eof
                 return []) <|>
         do
           g <- gdecl
           gs <- gdecls
           return $ (g : gs)
         <?> "gdecls"

gdecl :: C0Parser GDecl
gdecl = try (do
                p <- getPosition
                reserved "typedef"
                t <- typeParse
                i <- identifier
                semi
                return $ TypeDef t i p) <|>
        try (do
                p <- getPosition
                t <- typeParse
                i <- identifier
                params <- parens $ commaSep param
                semi
                return $ FDecl t i params p) <|>
        try (do
                p <- getPosition
                t <- typeParse
                i <- identifier
                params <- parens $ commaSep param
                b <- block
                return $ FDefn t i params b p) <|>
        try (do
                p <- getPosition
                reserved "struct"
                i <- identifier
                semi
                return $ SDecl i p) <|>
        try (do
                p <- getPosition
                reserved "struct"
                i <- identifier
                fields <- braces $ fieldList
                semi
                return $ SDefn i fields p)
        <?> "gdecl"

field = do
  t <- typeParse
  i <- identifier
  semi
  return $ Param t i

fieldList =
  try (do
          f <- field
          fs <- fieldList
          return $ f : fs
      ) <|> do return []

param :: C0Parser Param
param = do
  t <- typeParse
  i <- identifier
  return $ Param t i
  <?> "param"

block :: C0Parser Block
block = do
  braces (do
   pos   <- getPosition
   stmts <- many stmt
   return $ Block stmts pos)
   <?> "block"

stmt :: C0Parser Stmt
stmt = try (do 
               pos <- getPosition
               dest <- lvalue
               op <- postOp
               semi
               case op of
                 Just o -> return $ Simp (PostOp o (Ident dest pos) pos) pos
                 Nothing -> Text.ParserCombinators.Parsec.unexpected "asdfdsf") <|>
       try (do
               pos <- getPosition
               stmt <- simp
               semi
               return $ Simp stmt pos) <|>
       try (do
               pos <- getPosition
               stmt <- ctrl
               return $ Ctrl stmt pos) <|>
       try (do
               pos <- getPosition
               stmt <- block
               return $ BlockStmt stmt pos)
       <?> "stmt"

simp :: C0Parser Simp
simp = try (do
               pos <- getPosition
               dest <- lvalue
               op <- asnOp
               e <- expr
               case op of
                 Just Fail -> Text.ParserCombinators.Parsec.unexpected "Bad asnOp"
                 _ -> return $ Asgn dest op e pos) <|>
       try (do
               pos <- getPosition
               t <- typeParse
               ident <- identifier
               op <- asnOp
               e <- expr
               case op of
                 Nothing -> return $ Decl t ident (Just e) pos
                 Just _ -> Text.ParserCombinators.Parsec.unexpected "Bad Decl asnOp") <|>
       try (do
               pos <- getPosition
               t <- typeParse
               ident <- identifier
               return $ Decl t ident Nothing pos) <|>
       try (do
               pos <- getPosition
               dest <- lvalue
               op <- postOp
               case op of
                 Just o -> return $ PostOp o (Ident dest pos) pos
                 Nothing -> Text.ParserCombinators.Parsec.unexpected "asdfdsf") <|>
       try (do
               pos <- getPosition
               e <- expr
               return $ Expr e pos)
       <?> "simp"

ctrl :: C0Parser Ctrl
ctrl = try (do
               pos <- getPosition
               reserved "if"
               e <- parens expr
               s <- stmt
               eop <- elseOpt
               return $ If e s eop pos) <|>
       try (do
               pos <- getPosition
               reserved "while"
               e <- parens expr
               s <- stmt
               return $ While e s pos) <|>
       try (do
               pos <- getPosition
               reserved "return"
               semi
               return $ Return Nothing pos) <|>
       try (do
               pos <- getPosition
               reserved "return"
               e <- expr
               semi
               return $ Return (Just e) pos) <|>
       try (do
               pos <- getPosition
               reserved "for"
               (s1,e,s2) <- parens forBody
               s <- stmt
               return $ For s1 e s2 s pos) <|>
       try (do
               pos <- getPosition
               reserved "assert"
               e <- parens expr
               semi
               return $ Assert e pos)
       <?> "ctrl"
       
elseOpt :: C0Parser (Maybe Stmt)
elseOpt = (do
              reserved "else"
              s <- stmt
              return $ Just s) <|>
          do
            return Nothing
            <?> "elseOpt"

forBody :: C0Parser ((Maybe Simp), Expr, (Maybe Simp))
forBody = (do
              s1 <- simpOpt
              semi
              e <- expr
              semi
              s2 <- simpOpt
              return $ (s1, e, s2))
          <?> "forBody"

simpOpt :: C0Parser (Maybe Simp)
simpOpt = try (do
                  s <- simp
                  return $ Just s) <|>
              (do
                  return Nothing)
               <?> "simpOpt"


typeParse :: C0Parser Type
typeParse = do
  t <- simpleType
  f <- typeEnd
  return $ f t
  <?> "type"

typeEnd = try (do
                  reservedOp "*"
                  f <- typeEnd
                  return (\x -> f $ Pointer x)) <|>
          try (do
                  reservedOp "["
                  reservedOp "]"
                  f <- typeEnd
                  return (\x -> f $ Array x)) <|>
          try (do
                  return (\x -> x)) 
          <?> "typeEnd"

simpleType = try (do
                     reserved "int"
                     return Int) <|>
             try (do
                     reserved "bool"
                     return Bool) <|>
             try (do
                     reserved "void"
                     return Void) <|>
             try (do
                     reserved "struct"
                     i <- identifier
                     return $ Struct i) <|>
             try (do
                     i <- identifier
                     return $ Type i)
             <?> "type"

asnOp :: C0Parser (Maybe Op)
asnOp = do
   op <- operator
   return $ case op of
               "+="  -> Just Add
               "*="  -> Just Mul
               "-="  -> Just Sub
               "/="  -> Just Div
               "%="  -> Just Mod
               "&="  -> Just BAnd
               "^="  -> Just BXor
               "|="  -> Just BOr
               "<<=" -> Just Shl
               ">>=" -> Just Shr
               "="   -> Nothing
               x     -> Just Fail -- fail $ "Nonexistent assignment operator: " ++ x
   <?> "assignment operator"

postOp :: C0Parser (Maybe Op)
postOp = try (do
  reservedOp "++"
  return (Just Incr)) <|> do 
    reservedOp "--"
    return (Just Decr)
  <?> "postOp"

ternOp :: C0Parser (Maybe (Expr, Expr))
ternOp = try (do
                 reservedOp "?"
                 l <- expr
                 reservedOp ":"
                 r <- expr
                 return $ Just (l,r)) <|>
         do return Nothing

expr :: C0Parser Expr
expr = do
  e <- expr'
  e' <- ternOp
  case e' of
    Nothing -> return e
    Just (l,r) -> do p <- getPosition
                     return $ ExpTernOp e l r p 

expr' :: C0Parser Expr
expr' = buildExpressionParser opTable term <?> "expr"

term :: C0Parser Expr
term = do
  parens expr <|>
          try (do
                  p <- getPosition
                  i <- identifier
                  args <- parens $ commaSep expr
                  return $ App i args p) <|>
   (do p <- getPosition
       i <- identifier
       return $ Ident i p) <|>
   (do p <- getPosition
       reserved "true"
       return $ TrueT p) <|>
   (do p <- getPosition
       reserved "false"
       return $ FalseT p) <|>
   try (do
           p <- getPosition
           n <- hexadecimal
           return $ ExpInt Hex n p) <|>
   try (do
           p <- getPosition
           n <- natural
           return $ ExpInt Dec n p)
   <?> "term"

lvalue = do
  parens lvalue
  <|>
  (do
      i <- identifier
      return i)
  <?> "lvalue"

c0Def :: GenLanguageDef ByteString () Identity
c0Def = LanguageDef
   {commentStart    = string "/*",
    commentStartStr = "/*",
    commentEnd      = string "*/",
    commentEndStr   = "*/",
    commentLine     = string "//",
    nestedComments  = True,
    identStart      = letter <|> char '_',
    identLetter     = alphaNum <|> char '_',
    opStart         = oneOf "=+-*/%&^|<>!~",
    opLetter        = oneOf "=&|<>",
    reservedNames   = ["int", "char", "string", "void", "while", "for", "if",
                       "return", "break", "continue", "NULL", "alloc",
                       "alloc_array", "typedef", "struct", "else", "assert",
                       "true", "false", "bool"],
    reservedOpNames = ["+",  "*",  "-",  "/",  "%", "?", ":", "->", ".", "--",
                       "++", "[", "]"],
    caseSensitive   = True}

c0Tokens :: Tok.GenTokenParser ByteString () Identity
c0Tokens = Tok.makeTokenParser c0Def

reserved   :: String -> C0Parser ()
reserved   = Tok.reserved   c0Tokens
comma      :: C0Parser ()
comma      = do _ <- Tok.comma c0Tokens; return ()
semi       :: C0Parser ()
semi       = do _ <- Tok.semi c0Tokens; return ()
identifier :: C0Parser String
identifier = Tok.identifier c0Tokens
operator   :: C0Parser String
operator   = Tok.operator   c0Tokens
braces     :: C0Parser a -> C0Parser a
braces     = Tok.braces     c0Tokens
parens     :: C0Parser a -> C0Parser a
parens     = Tok.parens     c0Tokens
reservedOp :: String -> C0Parser ()
reservedOp = Tok.reservedOp c0Tokens
natural    :: C0Parser Integer
natural    = Tok.natural    c0Tokens
decimal = Tok.decimal c0Tokens
hexadecimal = Tok.hexadecimal c0Tokens
whiteSpace :: C0Parser ()
whiteSpace = Tok.whiteSpace c0Tokens
commaSep   :: C0Parser a -> C0Parser [a]
commaSep   = Tok.commaSep c0Tokens
semiSep    :: C0Parser a -> C0Parser [a]
semiSep    = Tok.semiSep c0Tokens
brackets   :: C0Parser a -> C0Parser a
brackets   = Tok.brackets c0Tokens

opTable = [[prefix "--" (ExpUnOp Fail),
            prefix  "-"   (ExpUnOp Neg),
            prefix  "*"   (ExpUnOp Deref),
            prefix  "~"   (ExpUnOp BNot),
            prefix  "!"   (ExpUnOp LNot)],
           [binary  "*"   (ExpBinOp Mul)  AssocLeft,
            binary  "/"   (ExpBinOp Div)  AssocLeft,
            binary  "%"   (ExpBinOp Mod)  AssocLeft],
           [binary  "+"   (ExpBinOp Add)  AssocLeft,
            binary  "-"   (ExpBinOp Sub)  AssocLeft],
           [binary  "<<"  (ExpBinOp Shl)  AssocLeft,
            binary  ">>"  (ExpBinOp Shr)  AssocLeft],
           [binary  "<"   (ExpBinOp Lt)   AssocLeft,
            binary  "<="  (ExpBinOp Leq)  AssocLeft,
            binary  ">"   (ExpBinOp Gt)   AssocLeft,
            binary  ">="  (ExpBinOp Geq)  AssocLeft],
           [binary  "=="  (ExpBinOp Eq)   AssocLeft,
            binary  "!="  (ExpBinOp Neq)  AssocLeft],
           [binary  "&"   (ExpBinOp BAnd) AssocLeft],
           [binary  "^"   (ExpBinOp BXor) AssocLeft],
           [binary  "|"   (ExpBinOp BOr)  AssocLeft],
           [binary  "&&"  (ExpBinOp LAnd) AssocLeft],
           [binary  "||"  (ExpBinOp LOr)  AssocLeft]]
          {-
We used a few helper functions which are in the Parsec documentation of Text.Parsec.Expr, located at \url{http://hackage.haskell.org/packages/archive/parsec/3.1.0/doc/html/Text-Parsec-Expr.html} The functions ``binary'', ``prefix'', and ``postfix'' were taken from there and are not my work, however they are used because rewriting them would look much the same, and they do not provide any core functionality, just make my code easier to read. Type signatures and location annotations were added by me.
-}
binary :: String -> (a -> a -> SourcePos -> a) -> Assoc -> Operator ByteString () Identity a
binary  name f = Infix $ do pos <- getPosition
                            reservedOp name
                            return $ \x y -> f x y pos
prefix :: String -> (a -> SourcePos -> a) -> Operator ByteString () Identity a
prefix  name f = Prefix $ do pos <- getPosition
                             reservedOp name
                             return $ \x -> f x pos

postfix name f = Postfix $ do pos <- getPosition
                              reservedOp name
                              return $ \x -> f x pos
