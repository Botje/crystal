{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Infer where

import Control.Lens hiding (transform)
import Control.Monad
import Data.Function
import Data.Generics
import Data.Generics.Biplate
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M

import Crystal.AST
import Crystal.Config
import Crystal.Env
import Crystal.Misc
import Crystal.RecursiveType
import Crystal.Seq
import Crystal.Tuple
import Crystal.Type

infer :: Expr Label -> Step (Expr TypedLabel)
infer = maybeDumpTypes <=< simplifyLabels <=< generate

maybeDumpTypes :: Expr TypedLabel -> Step (Expr TypedLabel)
maybeDumpTypes expr =
  do dump <- asks (^.cfgDumpTypes)
     when dump $ do
       let types = [ show k ++ " ==> " ++ show v | (k,v) <- sort $ dumpTypes expr ]
       report "Types dump" $ unlines types
     return expr

simplifyLabels :: Expr TypedLabel -> Step (Expr TypedLabel)
simplifyLabels = return . transformBi simplify

simplify :: Type -> Type
simplify (Tor ts) | length ts' == 1 = head ts'
                  | otherwise       = Tor ts'
  where (ts') = nub $ concatMap (expandOr . simplify) ts
simplify (TFun args body) = TFun args (simplify body)
simplify (TIf l t_1 t_2 t) | trivial t_1' t_2' = t'
                           | otherwise         = TIf l t_1' t_2' t'
  where (t_1', t_2', t') = (simplify t_1, simplify t_2, simplify t)
simplify t = t

expandOr :: Type -> [Type]
expandOr (Tor xs) = xs
expandOr t = [t]

trivial (TFun args_1 TAny) (TFun args_2 _) = length args_1 == length args_2
trivial (TFun _ _) (TVarFun _) = True
trivial x y | x == y = True
trivial _ _ = False

type Infer a = ReaderT Env (State TVar) a

dumpTypes :: Expr TypedLabel -> [(Ident, Type)]
dumpTypes (Expr _ (Let bnds bod))    = over (mapped._2) getType bnds ++ dumpTypes bod
dumpTypes (Expr _ (LetRec bnds bod)) = over (mapped._2) getType bnds ++ dumpTypes bod
dumpTypes (Expr _ _) = []

generate :: Expr Label -> Step (Expr TypedLabel)
generate ast = do ts <- asks (^.cfgTypeSys)
                  case ts of
                       Smart -> return $ generateSmart ast
                       Dumb  -> return $ generateDumb  ast

generateDumb :: Expr Label -> Expr TypedLabel
generateDumb e = go e
     where go (Expr l expr) =
             let l' = LSource l
                 simply = Expr (l' :*: TAny) in
               case expr of
                 Appl op args         -> 
                  let (op_, args_) = (go op, map go args)
                      (Expr l_r (Ref r)) = op_
                  in case M.lookup r main_env of
                          Just (LPrim nam :*: t_f) -> Expr (l' :*: applyPrim (instantiatePrim nam l' t_f) (map getTypeAndLabel args_)) (Appl op_ args_)
                          -- TODO: Generate TVar in l_r, reference with a TIf.
                          Nothing       -> Expr (l' :*: TAny) (Appl op_ args_)
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
                 Lambda ids bod       -> simply (Lambda ids (go bod))
                 Begin es             -> simply (Begin $ map go es)

generateSmart :: Expr Label -> Expr TypedLabel
generateSmart e@(Expr start _) = evalState (runReaderT (go e) main_env) (succ start)
  where goT :: Expr Label -> Infer (Expr TypedLabel, Type)
        goT e = go e >>= \e' -> return (e', getType e')

        go :: Expr Label -> Infer (Expr TypedLabel)
        go (Expr l e) = let l' = LSource l in
          case e of
          (Lit (LitString s)) -> return $ Expr (l' :*: TString) (Lit (LitString s))
          (Lit (LitChar c)) -> return $ Expr (l' :*: TChar) (Lit (LitChar c))
          (Lit (LitFloat f)) -> return $ Expr (l' :*: TInt) (Lit (LitFloat f)) -- TODO float
          (Lit (LitInt i)) -> return $ Expr (l' :*: TInt) (Lit (LitInt i))
          (Lit (LitBool b)) -> return $ Expr (l' :*: TBool) (Lit (LitBool b))
          (Lit (LitSymbol s)) -> return $ Expr (l' :*: TSymbol) (Lit (LitSymbol s))
          (Lit (LitVoid)) -> return $ Expr (l' :*: TVoid) (Lit (LitVoid))
          (Lit (LitList els)) | null els  -> return $ Expr (l' :*: TNull) (Lit (LitList els))
                              | otherwise -> return $ Expr (l' :*: TPair) (Lit (LitList els))
          (Ref i) -> do lt <- asks (M.lookup i)
                        case lt of
                          Just (l :*: t) -> return $ Expr (l :*: t) (Ref i)
                          Nothing -> error ("Unbound variable " ++ show i)
          (If cond cons alt) -> do (e_0, t_0) <- goT cond
                                   (e_1, t_1) <- goT cons
                                   (e_2, t_2) <- goT alt
                                   let t_if = Tor [t_1, t_2]
                                   return $ Expr (l' :*: t_if) (If e_0 e_1 e_2)
          (Let [(nam, exp)] bod) -> do (e_x, t_1) <- goT exp
                                       let t_l = leaves t_1
                                       let bod_tl = getLabel e_x :*: t_l
                                       (e_bod, t_bod) <- local (extend nam bod_tl) (goT bod)
                                       return $ Expr (l' :*: chain t_1 t_bod) (Let [(nam, e_x)] e_bod)
          (Lambda args bod) -> do a_args <- mapM (const freshTVar) args
                                  (e_bod, t_bod) <- local (extendMany args $ map (\v -> LVar v :*: TVar v) a_args) (goT bod)
                                  return $ Expr (l' :*: TFun a_args t_bod) (Lambda args e_bod)
          (Appl f args) -> do (e_f, t_f) <- goT f
                              e_args <- mapM go args
                              let tvars = [1..length args]
                              let tl_args = map getTypeAndLabel e_args
                              let (Expr _ (Ref fun)) = e_f
                              case M.lookup fun main_env of
                                   Just (LPrim nam :*: typ) ->
                                     do let applType = applyPrim (instantiatePrim nam l' t_f) tl_args
                                        return $ Expr (l' :*: applType) (Appl e_f e_args)
                                   _                             ->
                                     do let applType = TIf (l', getLabel e_f) (TFun tvars TAny) t_f (apply t_f tl_args)
                                        return $ Expr (l' :*: applType) (Appl e_f e_args)
          (Begin exps) -> do exps_ <- mapM go exps 
                             let t_last = last exps_ ^. ann._2
                             return $ Expr (l' :*: t_last) (Begin exps_)
          (LetRec bnds bod) -> let (nams, funs) = unzip bnds
                               in do vars <- replicateM (length nams) freshTVar
                                     let mkFun var n = TFun [1..n] (TAppl (TVar var) [LVar v :*: TVar v | v <- [1..n]])
                                     let bnds_tl = zipWith (\var (Expr l (Lambda vs _)) -> LSource l :*: mkFun var (length vs)) vars funs
                                     funs_tl <- local (extendMany nams bnds_tl) $ mapM go funs
                                     let t_funs = map getType funs_tl
                                     let t_funs' = solveLetrec vars t_funs
                                     let funs_tl' = zipWith (\var t -> LVar var :*: t) vars t_funs'
                                     local (extendMany nams funs_tl') $
                                       do e_funs <- mapM go funs
                                          (e_bod, t_bod) <- goT bod
                                          return $ Expr (l' :*: t_bod) (LetRec (zip nams e_funs) e_bod)
          _ -> error ("Don't know how to infer type for " ++ show e)


extendMany :: Ord k => [k] -> [v] -> M.Map k v -> M.Map k v
extendMany keys vals env = foldr (uncurry M.insert) env (zip keys vals)

apply :: Type -> [TypedLabel] -> Type
apply (Tor ts) a_args = Tor $ map (flip apply a_args) ts
apply (TIf l t_t t_a t) a_args = TIf l t_t t_a (apply t a_args)
apply vf@(TVarFun _) a_args = expand (TAppl vf a_args)
apply t_f@(TFun t_args t_bod) a_args | applies t_f a_args = expand (TAppl (TFun t_args t_bod) a_args)
                                     | otherwise = TError
apply (TVar v) a_args = TAppl (TVar v) a_args
apply _ a_args = TError

applies :: Type -> [TypedLabel] -> Bool
applies (TFun t_args t_bod) a_args = length t_args == length a_args  
applies _ _ = False

applyPrim :: Type -> [TypedLabel] -> Type
applyPrim t_f@(Tor funs) t_args =
  case listToMaybe $ filter (flip applies t_args) funs of
       Nothing -> apply t_f t_args
       Just fun -> apply fun t_args
applyPrim t_f@(TFun t_args t_bod) a_args | applies t_f a_args = apply t_f a_args
applyPrim t_f t_args = apply t_f t_args

instantiatePrim :: String -> TLabel -> Type -> Type
instantiatePrim nam lab t = transform f t
  where f (TIf (LPrim blame, cause) t1 t2 rest) | blame == nam = TIf (lab, cause) t1 t2 rest
        f x = x

expand :: Type -> Type
expand (TAppl (TFun t_args t_bod) a_args) = replace (M.fromList $ zip t_args a_args) t_bod
expand (TAppl (TVarFun (VarFun _ lab vf)) a_args) = vf a_args lab
expand typ = typ

chain :: Type -> Type -> Type
chain (Tor ts) t_c = Tor $ map (flip chain t_c) ts
chain (TIf l t_t t_1 t) t_c = TIf l t_t t_1 $ chain t t_c
chain t t_c = t_c

leaves :: Type -> Type
leaves (Tor ts) = Tor $ map leaves ts
leaves (TIf _ t_t t t_1) = leaves t_1
leaves t = t

replace :: M.Map TVar TypedLabel -> Type -> Type
replace env (TVar var) | Just (l :*: t) <- M.lookup var env = t
replace env (Tor ts) = Tor $ map (replace env) ts
replace env (TFun args bod) = TFun args $ replace (extendMany args (map (\v -> LVar v :*: TVar v) args) env) bod
replace env (TIf (l1,l2) t_1 t_2 t_3) = TIf (l1,l2') (replace env t_1) (replace env t_2) (replace env t_3)
  where l2' = case l2 of LVar tv | Just (l :*: t) <- M.lookup tv env -> l
                         x -> x
replace env (TAppl fun args) = apply (replace env fun) (map (over _2 (replace env)) args)
replace env x = x
