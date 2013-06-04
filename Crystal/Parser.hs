{-#LANGUAGE FlexibleContexts #-}
module Crystal.Parser (parseCrystal) where

import Control.Lens
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

fresh p = do s <- getState
             putState (succ s)
             return (p ++ show s)

makeAppl name args = do ref <- makeExpr (Ref name)
                        makeExpr $ Appl ref args

hashChar =     (char 'f' >> whiteSpace >> return (LitBool False))
           <|> (char 't' >> whiteSpace >> return (LitBool True))
           <|> (char '\\' >> anyChar >>= \c -> whiteSpace >> return (LitChar c))

quote =     symbol
        <|> LitList `liftM` parens (many treeEl)
  where treeEl = literal <|> symbol <|> (LitList `liftM` parens (many treeEl))
        symbol = LitSymbol `liftM` ident

literal = try number
          <|> (stringLiteral >>= return . LitString)
          <|> (char '#' >> hashChar)
          <|> (char '\'' >> quote)
          <?> "literal"

number = do mul <- option 1 (char '-' >> return (-1))
            num <- naturalOrFloat
            case num of 
                 Left i  -> return . LitInt . (* (round mul)) $ i
                 Right f -> return . LitFloat . (*mul) $ f

sexp =     (reserved "begin" >> exprs)
       <|> (reserved "lambda" >> liftM2 (Lambda) (parens (many ident)) exprs >>= makeExpr)
       <|> (reserved "let" >> let')
       <|> (reserved "if" >> if')
       <|> (reserved "cond" >> cond)
       <|> (reserved "do" >> do')
       <|> (liftM2 Appl expr (many expr) >>= makeExpr) 
       <?> "S-expression"

makeVoid = makeExpr $ Lit (LitVoid)

cond = do clauses <- many (parens sexp)
          nestIfs clauses
  where nestIfs [] = makeVoid
        nestIfs [Expr l (Appl (Expr _ (Ref "else")) es)] = return $ Expr l $ Begin es
        nestIfs (Expr l (Appl clause body):es) = 
          do body_ <- makeExpr (Begin body)
             es_ <- nestIfs es
             return $ Expr l $ If clause body_ es_

if' = do cons <- expr
         cond <- expr
         alt  <- expr <|> makeVoid
         makeExpr $ If cons cond alt
  <?> "if"

bindings = parens (many (parens (liftM2 (,) ident expr))) 

simpleLet = do bnd <- bindings
               body <- exprs
               makeExpr $ Let bnd body
            <?> "simple let"

namedLet = do name <- ident
              bnd <- bindings
              fnBody <- exprs
              let (vars, vals) = unzip bnd
              fun <- makeExpr $ Lambda vars fnBody
              body <- makeAppl name vals
              makeExpr $ LetRec [(name, fun)] body


let' =     namedLet
       <|> simpleLet 
       <?> "let expression"

do' = do iterspecs <- parens (many iterspec)
         (check, result) <- parens terminate
         fnBody <- exprs
         let vars  = map (^. _1) iterspecs
         let vals  = map (^. _2) iterspecs
         let steps = map (^. _3) iterspecs
         name <- fresh "do-"
         recCall <- makeAppl name steps
         initCall <- makeAppl name vals
         fnBody' <- makeExpr $ Begin [fnBody, recCall]
         fnBody'' <- makeExpr $ If check result fnBody'
         fun <- makeExpr $ Lambda vars fnBody''
         makeExpr $ LetRec [(name, fun)] initCall

iterspec = do es <- parens (many expr)
              case es of
                [e@(Expr _ (Ref var)), init, step] -> return (var, init, step)
                [e@(Expr _ (Ref var)), init]       -> return (var, init, e)
                _                 -> parserFail "malformed iteration spec"

terminate = do es <- many expr
               case es of
                [check]         -> makeVoid >>= \v -> return (check, v)
                [check, result] -> return (check, result)
                _               -> parserFail "malformed termination"

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
