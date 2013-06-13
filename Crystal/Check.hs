{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Check where

import Control.Lens hiding (transform)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
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

insertC :: Check -> [Check] -> [Check]
insertC            c                []   = [c]
insertC cc@(Check l t (Right id)) (c:cs) =
  case cc of
       Check l' t' (Right id')
        | id == id' && t == t' -> Check (l++l') t' (Right id) : cs
       _                       -> c : insertC cc cs

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
                         checksNoId = simplifyC $ Cand [e_c, removeChecksOn id bod_c]

removeChecksOn id = transform f
  where f c@(Check _ _ (Right id')) | id == id' = Cnone
        f c = c

type TypeMap = M.Map Ident Type
type Dups    = [(Ident, [TLabel])]
type DupsMap = M.Map Ident [TLabel]

toDupsMap :: Dups -> DupsMap
toDupsMap = M.fromListWith (++)

eliminateRedundantChecks :: Expr CheckedLabel -> Expr CheckedLabel
eliminateRedundantChecks expr = fst $ runReader (runWriterT $ go expr) M.empty
  where go orig@(Expr (l :*: checks) e) =
          do env <- ask
             let (env', checks', dupsC) = elimRedundant env checks
             (e', dupsE) <- listen $ local (const env') $ f e
             let dups = M.unionWith (++) (toDupsMap dupsC) (toDupsMap dupsE)
             tell $ M.toList dups
             return (Expr (l :*: addDuplicates dups (simplifyC checks')) e')
        f e =
          case e of
             Appl op args         -> Appl op `liftM` mapM go args
             Lit lit              -> return e
             Ref r                -> return e
             If cond cons alt     -> liftM2 (If cond) (go cons) (go alt)
             Let [(id, e)] bod    -> do e_ <- go e
                                        bod_ <- local (M.insert id TAny) $ go bod
                                        return $ Let [(id, e_)] bod_
             LetRec [(id, e)] bod ->
               case e of
                 Expr _ (Lambda ids _) ->
                   do let t_f = TFun (map (const 0) ids) TAny
                      (e_, bod_) <- local (M.insert id t_f) $ liftM2 (,) (go e) (go bod)
                      return $ LetRec [(id, e_)] bod_
             Lambda ids bod       -> Lambda ids `liftM` local (M.union (defaultEnv ids)) (go bod)
        defaultEnv ids = M.fromList [ (x, TAny) | x <- ids ]

addDuplicates :: DupsMap -> Check -> Check
addDuplicates dups c | M.null dups = c
addDuplicates dups c = transform f c
  where f (Check lab typ (Right i)) =
          let lab' = maybe [] id (M.lookup i dups) in
              Check (lab++lab') typ (Right i)
        f c = c

elimRedundant :: TypeMap -> Check -> (TypeMap, Check, Dups)
elimRedundant env checks = (env', simplifyC checks', duplicates)
  where ((checks', env'), duplicates) = runWriter (runStateT (go checks) env)
        go :: Check -> StateT TypeMap (Writer Dups) Check
        go Cnone     = return Cnone
        go (Cand cs) = Cand `liftM` mapM go cs
        go (Cor cs)  = do env <- get
                          cs' <- lift $ mapM (\c -> evalStateT (go c) env) cs
                          return $ Cor cs'
        go c@(Check lab typ target) =
          do env <- get
             case target of
                  Left lit -> return c
                  Right id ->
                    case M.lookup id env  of
                         Nothing   -> return c -- error ("Unbound identifier " ++ id ++ " in check " ++ show c)
                         Just TAny -> modify (M.insert id typ) >> return c
                         Just typ' | typ == typ' -> tell [(id, lab)] >> return Cnone
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
        reify' (Check blame prim cause) = appl (test prim) (syn (toExpr cause) : map (syn . toBlame) (nub blame))
          where test TInt       = "number?"
                test TString    = "string?"
                test TBool      = "boolean?"
                test TChar      = "character?"
                test TSymbol    = "symbol?"
                test TVoid      = "void?"
                test TVec       = "vector?"
                test TPair      = "pair?"
                test (TFun _ _) = "procedure?"

        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
