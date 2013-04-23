module Crystal.Pretty (pretty) where

import Data.List
import Text.PrettyPrint

import Crystal.AST

pretty expr = renderStyle style{lineLength=150} $ prettyE expr

prettyE (Ref ident)         = text ident
prettyE (Appl e args)       = appl $ map prettyE (e:args)
prettyE (If cond cons alt)  = appl (text "if" : map prettyE [cond, cons, alt])
prettyE (Let bds bod)       = appl [text "let" , parens (vcat $ map (\(i,e) -> appl [text i, prettyE e]) bds) , prettyE bod]
prettyE (LetRec bds bod)    = appl [text "letrec" , parens (vcat $ map (\(i,e) -> appl [text i, prettyE e]) bds) , prettyE bod]
prettyE (Lambda args body)  = appl [text "lambda", parens (sep $ map text args), prettyE body] 
prettyE (Begin body)        = appl (text "begin" : map prettyE body)
prettyE (Lit lit)           = prettyL lit

prettyL (LitChar c)   = text "#" <> text [c]
prettyL (LitString s) = text "\"" <> text s <> text "\""
prettyL (LitInt i)    = int (fromIntegral i)
prettyL (LitFloat f)  = double f
prettyL (LitBool True) = text "#t"
prettyL (LitBool False) = text "#f"

appl (x:xs) = parens (x <+> sep xs)
