module Crystal.Pretty (pretty, prettyD) where

import Data.List
import Text.PrettyPrint

import Crystal.AST

pretty expr = renderStyle style{lineLength=150} $ prettyE expr
prettyD (decls, expr) =
  renderStyle style{lineLength=150} $
    vcat (map toDecl decls) $+$ prettyE expr
  where toDecl (id, Expr l (Lambda args body)) = appl [text "define", parens (sep $ map text (id:args)), prettyE body]
        toDecl (id, value)                     = appl [text "define", text id, prettyE value]

prettyE (Expr l (Ref ident))         = text ident
prettyE (Expr l (Appl e args))       = appl $ map prettyE (e:args)
prettyE (Expr l (If cond cons alt))  = appl (text "if" : map prettyE [cond, cons, alt])
prettyE (Expr l (Let bds bod))       = appl [text "let" , parens (vcat $ map (\(i,e) -> appl [text i, prettyE e]) bds) , prettyE bod]
prettyE (Expr l (LetRec bds bod))    = appl [text "letrec" , parens (vcat $ map (\(i,e) -> appl [text i, prettyE e]) bds) , prettyE bod]
prettyE (Expr l (Lambda args body))  = appl [text "lambda", parens (sep $ map text args), prettyE body] 
prettyE (Expr l (Begin body))        = appl (text "begin" : map prettyE body)
prettyE (Expr l (Lit lit))           = prettyL lit

prettyL (LitChar c)   = text "#" <> text [c]
prettyL (LitString s) = text "\"" <> escape s <> text "\""
prettyL (LitSymbol s) = text "'" <> text s
prettyL (LitInt i)    = int (fromIntegral i)
prettyL (LitFloat f)  = double f
prettyL (LitBool True) = text "#t"
prettyL (LitBool False) = text "#f"

appl (x:xs) = parens (x <+> sep xs)

escape = text . concatMap (\x -> if x == '\n' then "\\n" else [x])
