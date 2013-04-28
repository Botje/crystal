{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Check where

import Data.List
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Type

data Check = Cnone
           | Cand Check Check
           | Cor [Check]
           | Check TLabel Type (Either LitVal Ident)
             deriving (Show, Eq, Data, Typeable)

type CheckedLabel = TLabel :*: Check

addChecks :: Expr TypedLabel -> Expr TLabel
addChecks = reifyChecks . introduceChecks

introduceChecks :: Expr TypedLabel -> Expr CheckedLabel
introduceChecks expr = go expr
  where go (Expr (l :*: t) e) =
          let simply = Expr (l :*: Cnone) in
          case e of 
               Appl op args         -> Expr (l :*: typeToChecks labLookup t) (Appl (go op) args')
                 where labLookup l = head [ litOrIdent e | (Expr (l' :*: _) e) <- args', l == l' ]
                       args' = map go args
                       litOrIdent (Ref r) = Right r
                       litOrIdent (Lit l) = Left l
               Lit lit              -> simply (Lit lit)
               Ref r                -> simply (Ref r)
               If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
               Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
               LetRec [(id, e)] bod -> simply (LetRec [(id, go e)] (go bod))
               Lambda ids bod       -> simply (Lambda ids (go bod))
               Begin es             -> simply (Begin $ map go es)

typeToChecks :: (TLabel -> Either LitVal Ident) -> Type -> Check
typeToChecks look (TIf (blame, cause) prim var rest) =
  let checks = typeToChecks look rest in
  case checks of 
       Cnone -> Check blame prim (look cause) 
       _     -> Cand (Check blame prim (look cause)) checks
typeToChecks look (Tor types) =
  let checks = nub $ map (typeToChecks look) types in
  case checks of
       [x] -> x
       _ -> Cor checks
typeToChecks look _ = Cnone

reifyChecks :: Expr CheckedLabel -> Expr TLabel
reifyChecks expr = go expr
  where go (Expr (l :*: checks) e) = 
          let simply e = reify checks (Expr l e) in
              case e of
                 Appl op args         -> simply (Appl (go op) (map go args))
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec [(id, e)] bod -> simply (LetRec [(id, go e)] (go bod))
                 Lambda ids bod       -> simply (Lambda ids (go bod))
                 Begin es             -> simply (Begin $ map go es)

reify :: Check -> Expr TLabel -> Expr TLabel
reify Cnone e = e
reify checks e = appl "check" [reify' checks, e]
  where reify' :: Check -> Expr TLabel
        reify' (Cor cs) = appl "or" $ map reify' cs
        reify' (Cand c cs) = appl "and" [reify' c, reify' cs]
        reify' (Check blame prim cause) = appl (test prim) [syn $ toExpr cause, syn $ toBlame blame]
          where test TInt       = "number?"
                test TString    = "string?"
                test TBool      = "boolean?"
                test (TFun _ _) = "function?"
        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
