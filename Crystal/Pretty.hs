module Crystal.Pretty (pretty, prettyD) where

import Data.List
import Text.PrettyPrint

import Crystal.AST

pretty expr = renderStyle style{lineLength=150} $ prettyE expr
prettyD (decls, expr) =
  renderStyle style{lineLength=150} $
    vcat (map toDecl decls) $+$ prettyE expr
  where toDecl (id, Expr l (Lambda args r body)) = appl [text "define", renderArgs (id:args) r, prettyE body]
        toDecl ("_", value)                      = prettyE value
        toDecl (id, value)                       = appl [text "define", text id, prettyE value]

prettyE (Expr l (Ref ident))         = text ident
prettyE (Expr l (Appl e args))       = appl $ map prettyE (e:args)
prettyE (Expr l (If cond cons alt))  =
  case alt of
       Expr _ (Lit LitVoid) -> appl (text "if" : map prettyE [cond, cons])
       otherwise            -> appl (text "if" : map prettyE [cond, cons, alt])
prettyE (Expr l (Let bds bod))        = appl [op, parens (vcat $ map (\(i,e) -> appl [text i, prettyBE e]) bds) , prettyBE bod]
  where op = if length bds > 1 then text "let*" else text "let"
prettyE (Expr l (LetRec bds bod))     = appl [text "letrec" , parens (vcat $ map (\(i,e) -> appl [text i, prettyBE e]) bds) , prettyBE bod]
prettyE (Expr l (Lambda args r body)) = appl [text "lambda", renderArgs args r, prettyBE body] 
prettyE (Expr l (Begin body))         = appl (text "begin" : map prettyBE body)
prettyE (Expr l (Lit lit))            = prettyL False lit

prettyBE (Expr l (Begin exps)) = vcat $ map prettyBE exps
prettyBE other                 = prettyE other

prettyL _ (LitChar c)   = text "#\\" <> text [c]
prettyL _ (LitString s) = text "\"" <> escape s <> text "\""
prettyL l (LitSymbol s) = quoted l <> text s
prettyL _ (LitInt i)    = int (fromIntegral i)
prettyL _ (LitFloat f)  = double f
prettyL _ (LitBool True) = text "#t"
prettyL _ (LitBool False) = text "#f"
prettyL _ (LitVoid) = text "(void)"
prettyL l (LitList els) = quoted l <> parens (hsep $ map (prettyL True) els)
prettyL l (LitPair x y) = quoted l <> parens (prettyL True x <+> text "." <+> prettyL True y)

appl (x:xs) = parens (x <+> sep xs)
quoted l = if l then empty else text "'"

escape = text . concatMap (\x -> if x == '\n' then "\\n" else [x])

renderArgs :: [Ident] -> Maybe Ident -> Doc
renderArgs vs Nothing  = parens (sep $ map text vs)
renderArgs [] (Just r) = text r
renderArgs vs (Just r) = parens (sep (map text vs ++ [text "."] ++ [text r]))
