{-#LANGUAGE FlexibleContexts #-}
module Crystal.Parser (parseCrystal) where

import Control.Lens
import Control.Monad
import Control.Monad.Identity
import Data.Char
import Data.List
import Data.Maybe
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
           <|> (char '\\' >> 
                 (do     (try (string "space") >> whiteSpace >> return (LitChar ' '))
                     <|> (try (string "newline") >> whiteSpace >> return (LitChar '\n'))
                     <|> (try (string "tab") >> whiteSpace >> return (LitChar '\t'))
                     <|> (anyChar >>= \c -> whiteSpace >> return (LitChar c))))

quote =     literal
        <|> LitSymbol `liftM` (ident <|> reservedIdent)
        <|> parens (do vals <- many1 quote
                       rest <- optionMaybe (symbol "." >> quote)
                       case rest of
                            Nothing -> return $ LitList vals
                            Just (LitList l) -> return $ LitList (vals ++ l)
                            Just val -> return $ foldr LitPair val vals
                    <|> return (LitList []))

reservedIdent = choice $ map (\n -> reserved n >> return n) reservedNames

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
       <|> (reserved "lambda" >> lambda )
       <|> (reserved "let*" >> letStar)
       <|> (reserved "letrec" >> letRec)
       <|> (reserved "let" >> let')
       <|> (reserved "if" >> if')
       <|> (reserved "cond" >> cond)
       <|> (reserved "case" >> case')
       <|> (reserved "do" >> do')
       <|> (reserved "set!" >> assignment)
       <|> (reserved "quote" >> quote >>= makeExpr . Lit)
       <|> (liftM2 Appl expr (many expr) >>= makeExpr) 
       <?> "S-expression"

assignment = do set <- makeExpr $ Ref "set!"
                var <- makeExpr . Ref =<< ident
                exp <- expr
                makeExpr $ Appl set [var, exp]

ensureNoDuplicateVars :: Monad m => [String] -> m ()
ensureNoDuplicateVars vars =
  case concatMap head $ filter ((>1).length) $ group $ sort vars of
       []   -> return ()
       dups -> fail $ "Multiple bindings of the same variable(s): " ++ show dups

parameters =     do { i <- ident; return ([], Just i) }
             <|> parens (do vars <- many ident
                            rest <- optionMaybe (symbol "." >> ident)
                            when (null vars && isJust rest) $ fail $ "Malformed parameter bindings"
                            return (vars, rest))

lambda = do (fixed, rest) <- parameters
            body <- letBody
            ensureNoDuplicateVars (fixed ++ maybe [] return rest)
            makeExpr $ Lambda fixed rest body

makeVoid = makeExpr $ Lit (LitVoid)

cond = do clauses <- many (parens sexp)
          nestIfs clauses
  where nestIfs [] = makeVoid
        nestIfs [Expr l (Appl (Expr _ (Ref "else")) es)] = return $ Expr l $ Begin es
        nestIfs (test@(Expr l (Appl clause [])):es) = 
          do nam <- fresh "cond-"
             es_ <- nestIfs es
             ref_ <- makeExpr (Ref nam)
             if_ <- makeExpr (If ref_ ref_ es_)
             makeExpr $ Let [(nam, test)] if_
        nestIfs (Expr l (Appl clause body):es) = 
          do body_ <- makeExpr (Begin body)
             es_ <- nestIfs es
             return $ Expr l $ If clause body_ es_

case' = do scrutinee  <- expr
           clauses    <- many (try (parens clause))
           lastClause <- parens (symbol "else" >> exprs) <|> makeVoid
           caseVar    <- fresh "case-"
           bod        <- foldM (f caseVar) lastClause (reverse clauses)
           makeExpr $ Let [(caseVar, scrutinee)] bod
  where clause = parens (many quote) >>= \l -> exprs >>= \es -> return (l, es)
        f caseVar bod (datums, exp) = do test <- makeAppl "member" =<< mapM makeExpr [Ref caseVar, Lit (LitList datums)]
                                         makeExpr $ If test exp bod

              

if' = do cons <- expr
         cond <- expr
         alt  <- expr <|> makeVoid
         makeExpr $ If cons cond alt
  <?> "if"

bindings = parens (many (parens (liftM2 (,) ident expr))) 

simpleLet = do bnd <- bindings
               ensureNoDuplicateVars $ map fst bnd
               body <- letBody
               makeExpr $ Let bnd body
            <?> "simple let"

namedLet = do name <- ident
              bnd <- bindings
              fnBody <- exprs
              let (vars, vals) = unzip bnd
              fun <- makeExpr $ Lambda vars Nothing fnBody
              body <- makeAppl name vals
              makeExpr $ LetRec [(name, fun)] body
              <?> "named let"

let' =     namedLet
       <|> simpleLet 
       <?> "let expression"


letStar = do bnd <- bindings
             fnBody <- letBody
             foldM wrap fnBody (reverse bnd)
             <?> "let*"
  where wrap bod (nam, val) = makeExpr $ Let [(nam, val)] bod

letRec = do bnd <- bindings
            body <- letBody
            makeExpr $ LetRec bnd body
            <?> "letrec"

do' = do iterspecs <- parens (many iterspec)
         (check, result) <- parens terminate
         fnBody <- exprs <|> makeVoid
         let vars  = map (^. _1) iterspecs
         let vals  = map (^. _2) iterspecs
         let steps = map (^. _3) iterspecs
         name <- fresh "do-"
         recCall <- makeAppl name steps
         initCall <- makeAppl name vals
         fnBody' <- makeExpr $ Begin [fnBody, recCall]
         fnBody'' <- makeExpr $ If check result fnBody'
         fun <- makeExpr $ Lambda vars Nothing fnBody''
         makeExpr $ LetRec [(name, fun)] initCall

iterspec = do es <- parens (many expr)
              case es of
                [e@(Expr _ (Ref var)), init, step] -> return (var, init, step)
                [e@(Expr _ (Ref var)), init]       -> return (var, init, e)
                _                 -> parserFail "malformed iteration spec"

terminate = do check  <- expr
               result <- exprs <|> makeVoid
               return (check, result)

expr =     (literal >>= makeExpr . Lit)
       <|> (ident >>= makeExpr . Ref)
       <|> parens sexp
       <?> "expression"
     
exprs = many1 expr >>= \es ->
        case es of
          [e] -> return e
          _   -> makeExpr (Begin es)
  <?> "function body"

decl = do try (symbol "(" >> reserved "define")
          ret <- fundecl
          symbol ")"
          return ret
       <?> "declaration"

letBody = do
  decls <- many decl
  body <- exprs
  case decls of
       [] -> return body
       _  -> makeExpr $ LetRec decls body

fundecl = do
  (fixed, rest) <- parameters
  case (fixed, rest) of
       ([], Just name) -> do val <- expr
                             return (name, val)
       ((nam:args), r) -> do body <- makeExpr . Lambda args r =<< letBody
                             return (nam, body)
  <?> "declaration"

program :: Parsec String Label (Expr Label)
program = do whiteSpace 
             decls <- many decl 
             e <- exprs
             eof 
             case decls of
                  [] -> return e
                  _  -> makeExpr $ LetRec decls e

parseCrystal = runParser program 1000

reservedNames = words "lambda if let let* letrec begin define case cond do quote set!"

sexpDef = T.LanguageDef {
    T.commentStart = ""
  , T.commentEnd   = ""
  , T.commentLine  = ";"
  , T.nestedComments = False
  , T.identStart   = satisfy (\x -> not (isSpace x || isDigit x || x `elem` ";().#"))
  , T.identLetter  = satisfy (\x -> not (isSpace x || x `elem` "$;().#"))
  , T.opStart      = satisfy (\x -> not (isSpace x || isDigit x || x `elem` ";().#"))
  , T.opLetter     = satisfy (\x -> not (isSpace x || x `elem` "$;().#"))
  , T.reservedNames = reservedNames 
  , T.reservedOpNames = reservedNames
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
