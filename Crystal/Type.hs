{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Type  where

import Control.Monad
import Data.Generics
import Data.Generics.Biplate
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

data a :*: b = a :*: b deriving (Show, Eq, Data, Typeable)
infix 8 :*:

data TLabel = LSource Int
            | LPrim String
            | LVar TVar
            | LSyn
              deriving (Show, Eq, Data, Typeable)

type TypedLabel = TLabel :*: Type

getType :: Expr TypedLabel -> Type
getType (Expr (_ :*: t) _) = t

getLabel :: Expr TypedLabel -> TLabel
getLabel (Expr (l :*: _) _) = l

getTypeAndLabel :: Expr TypedLabel -> TypedLabel
getTypeAndLabel (Expr tl _) = tl


data Type = TInt | TString | TBool
          | Tor [Type]
          | TVar TVar
          | TFun [TVar] Type
          | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
          | TError
          | TAny
            deriving (Show, Eq, Data, Typeable)

infer :: Expr Label -> Expr TypedLabel
infer = simplifyLabels . generate

simplifyLabels = transformBi simplify

simplify :: Type -> Type
simplify (Tor ts) | length ts' == 1 = head ts'
                  | otherwise       = Tor ts'
  where (ts') = nub $ map simplify ts
simplify (TFun args body) = TFun args (simplify body)
simplify (TIf l t_1 t_2 t) | trivial t_1' t_2' = t'
                           | otherwise         = TIf l t_1' t_2' t'
  where (t_1', t_2', t') = (simplify t_1, simplify t_2, simplify t)
simplify t = t

trivial (TFun args_1 TAny) (TFun args_2 _) = length args_1 == length args_2
trivial x y | x == y = True
trivial _ _ = False

type Infer a = ReaderT Env (State TVar) a

generate :: Expr Label -> Expr TypedLabel
generate e@(Expr start _) = evalState (runReaderT (go e) main_env) (succ start)
  where goT :: Expr Label -> Infer (Expr TypedLabel, Type)
        goT e = go e >>= \e' -> return (e', getType e')

        go :: Expr Label -> Infer (Expr TypedLabel)
        go (Expr l e) = let l' = LSource l in
          case e of
          (Lit (LitString s)) -> return $ Expr (l' :*: TString) (Lit (LitString s))
          (Lit (LitInt i)) -> return $ Expr (l' :*: TInt) (Lit (LitInt i))
          (Lit (LitBool b)) -> return $ Expr (l' :*: TBool) (Lit (LitBool b))
          (Ref i) -> do Just (_ :*: t) <- asks (M.lookup i)
                        return $ Expr (l' :*: t) (Ref i)
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
                              let applType = TIf (getLabel e_f, l') (TFun tvars TAny) t_f (apply t_f tl_args)
                              return $ Expr (l' :*: applType) (Appl e_f e_args)
          -- TODO wrong.
          (LetRec [(nam, exp)] bod) -> do (e_1, t_1) <- goT exp
                                          let t_l = leaves t_1
                                          let bod_tl = getLabel e_1 :*:t_l
                                          (e_bod, t_bod) <- local (extend nam bod_tl) (goT bod)
                                          return $ Expr (l' :*: chain t_1 t_bod) (LetRec [(nam, e_1)] e_bod)

type Env = M.Map Ident TypedLabel

main_env :: Env
main_env = M.fromList [
    "=" --> \this -> TFun [0,1] TBool,
    "+" --> TFun [0,1] . require [(TInt,0), (TInt, 1)] TInt,
    "string-append" --> TFun [0,1] . require [(TString,0), (TString,1)] TString
  ] where (-->) nam fun = (nam, LPrim nam :*: fun (LPrim nam))
          infix 5 -->
          require tests return blame = foldr (f blame) return tests
          f blame (prim, cause) return = TIf (blame, LVar cause) prim (TVar cause) return


extend :: Ident -> TypedLabel -> Env -> Env
extend = M.insert

extendMany :: Ord k => [k] -> [v] -> M.Map k v -> M.Map k v
extendMany keys vals env = foldr (uncurry M.insert) env (zip keys vals)

apply :: Type -> [TypedLabel] -> Type
apply (Tor ts) a_args = Tor $ map (flip apply a_args) ts
apply (TIf l t_t t_a t) a_args = TIf l t_t t_a (apply t a_args)
apply (TFun t_args t_bod) a_args | length t_args == length a_args = replace (M.fromList $ zip t_args a_args) t_bod
apply (TFun t_args t_bod) a_args | otherwise = TError
apply t a_args = TAny

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
replace env x = x
