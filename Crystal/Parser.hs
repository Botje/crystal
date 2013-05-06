{-#LANGUAGE FlexibleContexts #-}
module Crystal.Parser (parseCrystal) where

import Control.Monad
import Control.Monad.Identity
import Data.Char
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.String
import Text.Parsec.Prim
import qualified Text.Parsec.Token as T

import Crystal.AST

makeExpr ie = do s <- getState
                 putState (succ s)
                 return $ Expr s ie

hashChar =     (char 'f' >> whiteSpace >> return (LitBool False))
           <|> (char 't' >> whiteSpace >> return (LitBool True))

literal = try number
          <|> (stringLiteral >>= return . LitString)
          <|> (char '#' >> hashChar)
          <?> "literal"

number = do mul <- option 1 (char '-' >> return (-1))
            num <- naturalOrFloat
            case num of 
                 Left i  -> return . LitInt . (* (round mul)) $ i
                 Right f -> return . LitFloat . (*mul) $ f

sexp =     (reserved "begin" >> exprs)
       <|> (reserved "lambda" >> liftM2 (Lambda) (parens (many ident)) exprs >>= makeExpr)
       <|> (reserved "let" >> parens (many (parens (liftM2 (,) ident expr))) >>= \bind -> exprs >>= makeExpr . Let bind)
       <|> (reserved "if" >> if')
       <|> (reserved "cond" >> cond)
       <|> (liftM2 Appl expr (many expr) >>= makeExpr) 
       <?> "S-expression"

cond = do clauses <- many (parens sexp)
          nestIfs clauses
  where nestIfs [Expr l (Appl (Expr _ (Ref "else")) es)] = return $ Expr l $ Begin es
        nestIfs (Expr l (Appl clause body):es) = 
          do body_ <- makeExpr (Begin body)
             es_ <- nestIfs es
             return $ Expr l $ If clause body_ es_

if' = do cons <- expr
         cond <- expr
         alt  <- expr <|> makeExpr (Lit $ LitInt 0)
         makeExpr $ If cons cond alt
  <?> "if"

expr =     (literal >>= makeExpr . Lit)
       <|> (ident >>= makeExpr . Ref)
       <|> parens sexp
       <?> "expression"
     
exprs = many1 expr >>= \es ->
        case es of
          [e] -> return e
          _   -> makeExpr (Begin es)
  <?> "function body"

decl = try (parens ((reserved "define" >> (fundecl <|> vardecl))))
       <?> "declaration"

fundecl = do
  name:args <- parens (many1 ident)
  body <- makeExpr . Lambda args =<< exprs
  return (name, body)
  <?> "function declaration"

vardecl = do
  name <- ident
  val <- expr
  return $ (name, val)
  <?> "variable declaration"

program :: Parsec String Label (Expr Label)
program = do whiteSpace 
             decls <- many decl 
             e <- expr
             eof 
             case decls of
                  [] -> return e
                  _  -> makeExpr $ LetRec decls e

parseCrystal = runParser program 1000

sexpDef = T.LanguageDef {
    T.commentStart = ""
  , T.commentEnd   = ""
  , T.commentLine  = ";"
  , T.nestedComments = False
  , T.identStart   = satisfy (\x -> not (isSpace x || isDigit x || x `elem` "$;()"))
  , T.identLetter  = satisfy (\x -> not (isSpace x || x `elem` "$;()"))
  , T.opStart      = satisfy (\x -> not (isSpace x || isDigit x || x `elem` "$;()"))
  , T.opLetter     = satisfy (\x -> not (isSpace x || x `elem` "$;()"))
  , T.reservedNames = words "lambda if let letrec begin define cond"
  , T.reservedOpNames = words "lambda if let letrec begin define cond"
  , T.caseSensitive = False
  }

tp :: T.GenTokenParser String st Identity
tp = T.makeTokenParser sexpDef

parens   = T.parens tp
integer  = T.integer tp
float    = T.float tp
ident    = T.identifier tp
op       = T.operator tp
symbol   = T.symbol tp
reserved = T.reserved tp
whiteSpace = T.whiteSpace tp
charLiteral = T.charLiteral tp
stringLiteral = T.stringLiteral tp
naturalOrFloat = T.naturalOrFloat tp
