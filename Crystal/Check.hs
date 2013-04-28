{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Check where

import Control.Lens
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

ann :: Simple Lens (Expr a) a
ann op (Expr a e) = fmap (\a' -> Expr a' e) (op a)

_check :: Simple Lens CheckedLabel Check
_check op (l :*: c) = fmap (\c' -> l :*: c') (op c)

annCheck :: Simple Lens (Expr CheckedLabel) Check
annCheck = ann._check

addChecks :: Expr TypedLabel -> Expr TLabel
addChecks = reifyChecks . moveChecksUp . introduceChecks

introduceChecks :: Expr TypedLabel -> Expr CheckedLabel
introduceChecks expr = go expr
  where go (Expr (l :*: t) e) =
          let simply = Expr (l :*: Cnone) in
          case e of 
               Appl op args         -> Expr (l :*: checks) (Appl (go op) args')
                 where labLookup l = head [ litOrIdent e | (Expr (l' :*: _) e) <- args', l == l' ]
                       args' = map go args
                       checks = simplifyC (typeToChecks labLookup t)
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
  Cand (Check blame prim (look cause)) $ typeToChecks look rest
typeToChecks look (Tor types) =
  Cor $ map (typeToChecks look) types
typeToChecks look _ = Cnone


partitionC :: Ident -> Check -> (Check, Check)
partitionC i Cnone = (Cnone, Cnone)
partitionC i (Cand c1 c2) = 
  let (with1, without1) = partitionC i c1
      (with2, without2) = partitionC i c2 in
      (simplifyC (Cand with1 with2), simplifyC (Cand without1 without2))
partitionC i (Cor checks) = 
  let (withs, withouts) = unzip $ map (partitionC i) checks in
      (simplifyC (Cor withs), simplifyC (Cor withouts))
partitionC i c@(Check blame prim litOrIdent)
  | litOrIdent == Right i = (c, Cnone)
  | otherwise             = (Cnone, c)

simplifyC :: Check -> Check
simplifyC (Cand c1 c2) = 
  case (c1, c2) of
       (Cnone, _) -> c2
       (_, Cnone) -> c1
       (_, _)     -> Cand c1 c2
  where (c1', c2') = (simplifyC c1, simplifyC c2)
simplifyC (Cor cs) =
  case cs' of
       [c] -> c
       _   -> Cor cs'
  where cs' = nub $ map simplifyC cs
simplifyC c = c

moveChecksUp :: Expr CheckedLabel -> Expr CheckedLabel
moveChecksUp = transformBi f
  where f :: Expr CheckedLabel -> Expr CheckedLabel
        f simple@(Expr (l :*: checks) e) =
          case e of
               Appl op args         -> simple
               Lit lit              -> simple
               Ref r                -> simple
               If cond cons alt     -> Expr (l :*: Cor [cons ^. annCheck , alt ^. annCheck]) e
               LetRec [(id, e)] bod -> simple
               Lambda ids bod       -> simple
               Begin es             -> simple
               Let [(id, e)] bod    ->
                 Expr (l :*: Cand e_c checksNoId) $ Let [(id, set annCheck Cnone e)] (set annCheck checksId bod)
                   where (e_c, bod_c)   = (e ^. annCheck, bod ^. annCheck)
                         (checksId, checksNoId) = partitionC id bod_c



reifyChecks :: Expr CheckedLabel -> Expr TLabel
reifyChecks expr = go expr
  where go (Expr (l :*: checks) e) = 
          let simply e = reify (simplifyC checks) (Expr l e) in
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
        reify' (Cnone) = syn (Lit (LitBool True))
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
