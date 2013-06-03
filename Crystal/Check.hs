{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Check where

import Control.Lens hiding (transform)
import Control.Monad.Reader
import Control.Monad.State
import Data.List
import qualified Data.Map as M
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Tuple
import Crystal.Type

data Check = Cnone
           | Cand [Check]
           | Cor [Check]
           | Check [TLabel] Type (Either LitVal Ident)
             deriving (Show, Eq, Data, Typeable)

type CheckedLabel = TLabel :*: Check

_check :: Simple Lens CheckedLabel Check
_check = _2

annCheck :: Simple Lens (Expr CheckedLabel) Check
annCheck = ann._check

addChecks :: Expr TypedLabel -> Expr TLabel
addChecks = reifyChecks . eliminateRedundantChecks . moveChecksUp . introduceChecks

introduceChecks :: Expr TypedLabel -> Expr CheckedLabel
introduceChecks expr = go expr
  where go (Expr (l :*: t) e) =
          let simply = Expr (l :*: Cnone) in
          case e of 
               Appl op args         -> Expr (l :*: checks) (Appl op' args')
                 where labLookup l =
                         case [ litOrIdent e | (Expr (l' :*: _) e) <- op':args', l == l' ] of
                              [] -> error ("Label lookup failed. Failing expression: " ++ show e)
                              (x:xs) -> x
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
  Cand [Check [blame] prim (look cause), typeToChecks look rest]
typeToChecks look (Tor types) =
  Cor $ map (typeToChecks look) types
typeToChecks look _ = Cnone


simplifyC :: Check -> Check
simplifyC c@(Cand cs) =
  case cs' of
       [c] -> c
       [] -> Cnone
       _ -> Cand cs'
  where cs' = simplifyMerge c
        simplifyMerge (Cand cs) = nub $ filter (/= Cnone) $ concatMap simplifyMerge cs
        simplifyMerge c = [simplifyC c]
simplifyC (Cor cs) =
  case cs' of
       [c] -> c
       _ | Cnone `elem` cs' -> Cnone
       _ -> Cor cs' 
  where cs' = nub $ map simplifyC cs
simplifyC c = c

mergeC Cnone     check     = check
mergeC check     Cnone     = check
mergeC (Cor  as) check     = Cand [Cor as, check]
mergeC (Cand as) check = 
  case check of 
       Cand bs -> foldl mergeC (Cand as) bs
       Cor bs  -> Cand (as ++ [Cor bs])
       c@(Check l t (Left lit)) -> Cand (as ++ [c])
       c@(Check l t (Right id)) -> if any (checks t id) as
                                      then Cand as
                                      else Cand (as ++ [c])
mergeC checkA    checkB    = mergeC (Cand [checkA]) checkB

checks t id (Check _ t' (Right id')) = t == t' && id == id'
checks t id c = False



moveChecksUp :: Expr CheckedLabel -> Expr CheckedLabel
moveChecksUp = transformBi f
  where f :: Expr CheckedLabel -> Expr CheckedLabel
        f simple@(Expr (l :*: checks) e) =
          case e of
               Appl op args         -> simple
               Lit lit              -> simple
               Ref r                -> simple
               If cond cons alt     -> Expr (l :*: simplifyC (Cor [cons ^. annCheck , alt ^. annCheck])) e
               LetRec [(id, e)] bod -> simple
               Lambda ids bod       -> simple
               Begin es             -> simple
               Let [(id, e)] bod    ->
                 Expr (l :*: checksNoId) $ Let [(id, set annCheck Cnone e)] bod
                   where (e_c, bod_c) = (e ^. annCheck, bod ^. annCheck)
                         checksNoId = mergeC e_c (simplifyC $ removeChecksOn id bod_c)

removeChecksOn id = transform f
  where f c@(Check _ _ (Right id')) | id == id' = Cnone
        f c = c

type TypeMap = M.Map Ident Type

eliminateRedundantChecks :: Expr CheckedLabel -> Expr CheckedLabel
eliminateRedundantChecks expr = runReader (go expr) M.empty
  where go orig@(Expr (l :*: checks) e) =
          do env <- ask
             let (checks', env') = elimRedundant env checks
             e' <- local (const env') $ f e
             return (Expr (l :*: simplifyC checks') e')
        f e =
          case e of
             Appl op args         -> return e
             Lit lit              -> return e
             Ref r                -> return e
             If cond cons alt     -> liftM2 (If cond) (go cons) (go alt)
             Let [(id, e)] bod    -> Let [(id, e)] `liftM` local (M.insert id TAny) (go bod)
             LetRec [(id, e)] bod ->
               case e of
                 Expr _ (Lambda ids _) ->
                   do let t_f = TFun (map (const 0) ids) TAny
                      (e_, bod_) <- local (M.insert id t_f) $ liftM2 (,) (go e) (go bod)
                      return $ LetRec [(id, e_)] bod_
             Lambda ids bod       -> Lambda ids `liftM` local (M.union (defaultEnv ids)) (go bod)
        defaultEnv ids = M.fromList [ (x, TAny) | x <- ids ]

elimRedundant :: TypeMap -> Check -> (Check, TypeMap)
elimRedundant env checks = runState (go checks) env
  where go Cnone     = return Cnone
        go (Cand cs) = Cand `liftM` mapM go cs
        go (Cor cs)  = do env <- get
                          let cs' = map (\c -> evalState (go c) env) cs
                          return $ Cor cs'
        go c@(Check lab typ target) =
          case target of
               Left lit -> return c
               Right id ->
                 case M.lookup id env  of
                      Nothing   -> error ("Unbound identifier " ++ id)
                      Just TAny -> modify (M.insert id typ) >> return c
                      Just typ' | typ == typ' -> return Cnone
                                | otherwise   -> return c

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
        reify' (Cand cs) = appl "and" $ map reify' cs
        reify' (Check blame prim cause) = appl (test prim) (syn (toExpr cause) : map (syn . toBlame) blame)
          where test TInt       = "number?"
                test TString    = "string?"
                test TBool      = "boolean?"
                test TSymbol    = "symbol?"
                test TVoid      = "void?"
                test TVec       = "vector?"
                test TPair      = "pair?"
                test (TFun _ _) = "function?"

        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
