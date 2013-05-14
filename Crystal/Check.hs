{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Check where

import Control.Lens hiding (transform)
import Data.List
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Tuple
import Crystal.Type

data Check = Cnone
           | Cand Check Check
           | Cor [Check]
           | Check TLabel Type (Either LitVal Ident)
             deriving (Show, Eq, Data, Typeable)

type CheckedLabel = TLabel :*: Check

_check :: Simple Lens CheckedLabel Check
_check = _2

annCheck :: Simple Lens (Expr CheckedLabel) Check
annCheck = ann._check

addChecks :: Expr TypedLabel -> Expr TLabel
addChecks = reifyChecks . moveChecksUp . introduceChecks

introduceChecks :: Expr TypedLabel -> Expr CheckedLabel
introduceChecks expr = go expr
  where go (Expr (l :*: t) e) =
          let simply = Expr (l :*: Cnone) in
          case e of 
               Appl op args         -> Expr (l :*: checks) (Appl op' args')
                 where labLookup l =
                           head [ litOrIdent e | (Expr (l' :*: _) e) <- op':args', l == l' ]
                       (op':args') = map go (op:args)
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


simplifyC :: Check -> Check
simplifyC (Cand c1 c2) = 
  case (c1', c2') of
       (Cnone, _) -> c2'
       (_, Cnone) -> c1'
       (_, _)     -> Cand c1' c2'
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
                 Expr (l :*: Cand e_c checksNoId) $ Let [(id, set annCheck Cnone e)] bod
                   where (e_c, bod_c) = (e ^. annCheck, bod ^. annCheck)
                         checksNoId = simplifyC (Cand e_c (removeChecksOn id bod_c))

removeChecksOn id = transform f
  where f c@(Check _ _ (Right id')) | id == id' = Cnone
        f c = c


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
                test TSymbol    = "symbol?"
                test (TFun _ _) = "function?"

        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
