{-#LANGUAGE FlexibleContexts, TypeOperators #-}
module Crystal.Type  where

import Control.Monad
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M

import Crystal.AST
import Crystal.Seq

freshTVar :: (MonadState TVar m) => m TVar
freshTVar = nextSeq

type TVar = Int

data a :*: b = a :*: b deriving (Show, Eq)

type TypedLabel = Label :*: Type

data Type = TInt | TString | TBool
          | Tor [Type]
          | TVar TVar
          | TFun [TVar] Type
          | TIf Type Type Type
          | TError
          | TAny
            deriving (Show, Eq)

infer :: Expr Label -> Expr TypedLabel
infer = generate
--   where simplify30 = foldl (.) id $ replicate 30 simplify

simplify :: Type -> Type
simplify (Tor ts) | length ts' == 1 = head ts'
                  | otherwise       = Tor ts'
  where (ts') = nub $ map simplify ts
simplify (TFun args body) = TFun args (simplify body)
simplify (TIf t_1 t_2 t) | trivial t_1' t_2' = t'
                         | otherwise         = TIf t_1' t_2' t'
  where (t_1', t_2', t') = (simplify t_1, simplify t_2, simplify t)
simplify t = t

trivial (TFun args_1 TAny) (TFun args_2 _) = length args_1 == length args_2
trivial x y | x == y = True
trivial _ _ = False

getType :: Expr TypedLabel -> Type
getType (Expr (_ :*: t) _) = t

generate :: Expr Label -> Expr TypedLabel
generate e@(Expr start _) = evalState (runReaderT (go e) main_env) (succ start)
  where goT :: Expr Label -> ReaderT Env (State TVar) (Expr TypedLabel, Type)
        goT e = go e >>= \e' -> return (e', getType e')

        go :: Expr Label -> ReaderT Env (State TVar) (Expr TypedLabel)
        go (Expr l e) = case e of
          (Lit (LitString s)) -> return $ Expr (l :*: TString) (Lit (LitString s))
          (Lit (LitInt i)) -> return $ Expr (l :*: TInt) (Lit (LitInt i))
          (Lit (LitBool b)) -> return $ Expr (l :*: TBool) (Lit (LitBool b))
          (Ref i) -> do Just t <- asks (M.lookup i)
                        return $ Expr (l :*: t) (Ref i)
          (If cond cons alt) -> do (e_0, t_0) <- goT cond
                                   (e_1, t_1) <- goT cons
                                   (e_2, t_2) <- goT alt
                                   let t_if = TIf TBool t_0 (Tor [t_1, t_2])
                                   return $ Expr (l :*: t_if) (If e_0 e_1 e_2)
          (Let [(nam, exp)] bod) -> do (e_x, t_1) <- goT exp
                                       let t_l = leaves t_1
                                       (e_bod, t_bod) <- local (extend nam t_l) (goT bod)
                                       return $ Expr (l :*: chain t_1 t_bod) (Let [(nam, e_x)] e_bod)
          (Lambda args bod) -> do a_args <- mapM (const freshTVar) args
                                  (e_bod, t_bod) <- local (extendMany args $ map TVar a_args) (goT bod)
                                  return $ Expr (l :*: TFun a_args t_bod) (Lambda args e_bod)
          (Appl f args) -> do (e_f, t_f) <- goT f
                              (e_args, t_args) <- unzip `liftM` mapM goT args
                              a_args <- mapM (const freshTVar) args
                              let base = TIf (TFun a_args TAny) t_f
                              let applType = TIf (TFun a_args TAny) t_f (apply t_f t_args)
                              return $ Expr (l :*: applType) (Appl e_f e_args)
          -- TODO wrong.
          (LetRec [(nam, exp)] bod) -> do (e_1, t_1) <- goT exp
                                          let t_l = leaves t_1
                                          (e_bod, t_bod) <- local (extend nam t_l) (goT bod)
                                          return $ Expr (l :*: chain t_1 t_bod) (LetRec [(nam, e_1)] e_bod)


main_env :: Env
main_env = M.fromList [
    "=" --> TFun [0,1] TBool,
    "+" --> TFun [0,1] (TIf TInt (TVar 0) (TIf TInt (TVar 1) TInt))
  ] where (-->) = (,)

type Env = M.Map Ident Type

extend :: Ident -> Type -> Env -> Env
extend = M.insert

extendMany :: Ord k => [k] -> [v] -> M.Map k v -> M.Map k v
extendMany keys vals env = foldr (uncurry M.insert) env (zip keys vals)

apply :: Type -> [Type] -> Type
apply (Tor ts) a_args = Tor $ map (flip apply a_args) ts
apply (TIf t_t t_a t) a_args = TIf t_t t_a (apply t a_args)
apply (TFun t_args t_bod) a_args | length t_args == length a_args = replace (M.fromList $ zip t_args a_args) t_bod
apply (TFun t_args t_bod) a_args | otherwise = TError
apply t a_args = TError

chain :: Type -> Type -> Type
chain (Tor ts) t_c = Tor $ map (flip chain t_c) ts
chain (TIf t_t t_1 t) t_c = TIf t_t t_1 $ chain t t_c
chain t t_c = t_c

leaves :: Type -> Type
leaves (Tor ts) = Tor $ map leaves ts
leaves (TIf t_t t t_1) = leaves t_1
leaves t = t

replace :: M.Map TVar Type -> Type -> Type
replace env (TVar var) | var `M.member` env = fromJust $ M.lookup var env
replace env (Tor ts) = Tor $ map (replace env) ts
replace env (TFun args bod) = TFun args $ replace (extendMany args (map TVar args) env) bod
replace env (TIf t_1 t_2 t_3) = TIf (replace env t_1)(replace env t_2)(replace env t_3)
replace env x = x
