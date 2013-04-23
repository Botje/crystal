{-#LANGUAGE FlexibleContexts #-}
module Crystal.Type  where

import Control.Monad
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M

import Crystal.AST
import Crystal.Seq

freshTVar :: (MonadState TVar m) => m TVar
freshTVar = nextSeq

type TVar = Int

data Type = TInt | TString | TBool
          | Tor Type Type
          | TVar TVar
          | TFun [TVar] Type
          | TIf Type Type Type
          | TError
          | TAny
            deriving (Show, Eq)

infer :: Expr -> Type
infer = simplify30 . generate
  where simplify30 = foldl (.) id $ replicate 30 simplify

simplify :: Type -> Type
simplify (Tor t_1 t_2) = if t_1' == t_2' then t_1' else Tor t_1' t_2'
  where (t_1', t_2') = (simplify t_1, simplify t_2)
simplify (TFun args body) = TFun args (simplify body)
simplify (TIf t_1 t_2 t) | trivial t_1' t_2' = t'
                         | otherwise         = TIf t_1' t_2' t'
  where (t_1', t_2', t') = (simplify t_1, simplify t_2, simplify t)
simplify t = t

trivial (TFun args_1 TAny) (TFun args_2 _) = length args_1 == length args_2
trivial x y | x == y = True
trivial _ _ = False

generate :: Expr -> Type
generate e = evalState (runReaderT (go e) main_env) 1
  where go :: Expr -> ReaderT Env (State TVar) Type
        go (Lit (LitString _)) = return TString
        go (Lit (LitInt _)) = return TInt
        go (Lit (LitBool _)) = return TBool
        go (Ref i) = do Just t <- asks (M.lookup i)
                        return t
        go (If cond cons alt) = do t_0 <- go cond
                                   t_1 <- go cons
                                   t_2 <- go alt
                                   let base = TIf TBool t_0
                                   return . base $ Tor t_1 t_2
        go (Let [(nam, exp)] bod) = do t_1 <- go exp
                                       let t_l = leaves t_1
                                       t_bod <- local (extend nam t_l) (go bod)
                                       return $ chain t_1 t_bod
        go (Lambda args bod) = do a_args <- mapM (const freshTVar) args
                                  t_bod <- local (extendMany args $ map TVar a_args) (go bod)
                                  return $ TFun a_args t_bod
        go (Appl e_f args) = do t_f <- go e_f
                                t_args <- mapM go args
                                a_args <- mapM (const freshTVar) args
                                let base = TIf (TFun a_args TAny) t_f
                                return . base $ apply t_f t_args
        -- TODO wrong.
        go (LetRec [(nam, exp)] bod) = do t_1 <- go exp
                                          let t_l = leaves t_1
                                          t_bod <- local (extend nam t_l) (go bod)
                                          return $ chain t_1 t_bod


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
apply (Tor t_a t_b) a_args = apply t_a a_args `Tor` apply t_b a_args
apply (TIf t_t t_a t) a_args = TIf t_t t_a (apply t a_args)
apply (TFun t_args t_bod) a_args | length t_args == length a_args = replace (M.fromList $ zip t_args a_args) t_bod
apply (TFun t_args t_bod) a_args | otherwise = TError
apply t a_args = TError

chain :: Type -> Type -> Type
chain (Tor t_1 t_2) t_c = chain t_1 t_c `Tor` chain t_2 t_c
chain (TIf t_t t_1 t) t_c = TIf t_t t_1 $ chain t t_c
chain t t_c = t_c

leaves :: Type -> Type
leaves (Tor t_1 t_2) = leaves t_1 `Tor` leaves t_2
leaves (TIf t_t t t_1) = leaves t_1
leaves t = t

replace :: M.Map TVar Type -> Type -> Type
replace env (TVar var) | var `M.member` env = fromJust $ M.lookup var env
replace env (Tor t_a t_b) = replace env t_a `Tor` replace env t_b
replace env (TFun args bod) = TFun args $ replace (extendMany args (map TVar args) env) bod
replace env (TIf t_1 t_2 t_3) = TIf (replace env t_1)(replace env t_2)(replace env t_3)
replace env x = x
