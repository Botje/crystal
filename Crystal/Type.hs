{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Type  where

import Control.Lens
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
import Crystal.Tuple

freshTVar :: (MonadState TVar m) => m TVar
freshTVar = nextSeq

type TVar = Int

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


data Type = TInt | TString | TBool | TSymbol | TVoid
          | Tor [Type]
          | TVar TVar
          | TFun [TVar] Type
          | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
          | TAppl Type [TypedLabel]
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
          (Lit (LitSymbol s)) -> return $ Expr (l' :*: TSymbol) (Lit (LitSymbol s))
          (Lit (LitVoid)) -> return $ Expr (l' :*: TVoid) (Lit (LitVoid))
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
                              let applType = TIf (l', getLabel e_f) (TFun tvars TAny) t_f (apply t_f tl_args)
                              return $ Expr (l' :*: applType) (Appl e_f e_args)
          -- TODO multiple bindings.
          (LetRec [(nam, exp)] bod) -> do var <- freshTVar
                                          let var_tl = LVar var :*: TVar var
                                          Expr (e_l :*: TFun abod tbod) _ <- local (extend nam var_tl) (go exp)
                                          let t_l = simplify $ leaves tbod
                                          let e_tl = e_l :*: TFun abod t_l
                                          (e_1', t_1) <- local (extend nam e_tl) (goT exp)
                                          (e_bod, t_bod) <- local (extend nam e_tl) (goT bod)
                                          return $ Expr (l' :*: t_bod) (LetRec [(nam, e_1')] e_bod)

type Env = M.Map Ident TypedLabel

main_env :: Env
main_env = M.fromList [
    "=" --> \this -> TFun [0,1] TBool,
    "+" --> TFun [2,3] . require [(TInt,2), (TInt,3)] TInt,
    "string-append" --> TFun [4,5] . require [(TString,4), (TString,5)] TString,
    "<" --> TFun [6,7] . require [(TInt,6), (TInt,7)] TBool,
    "*" --> TFun [8,9] . require [(TInt,8), (TInt,9)] TInt,
    "-" --> TFun [10,11] . require [(TInt,10), (TInt,11)] TInt,
    "display" --> TFun [12] . require [(TString,12)] TAny,
    "eq?" --> TFun [13,14] . require [] TBool,
    ">" --> TFun [15,16] . require [(TInt,15), (TInt,16)] TBool,
    "read" --> const (TFun [] TAny)
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
apply (TFun t_args t_bod) a_args | length t_args == length a_args = expand (TAppl (TFun t_args t_bod) a_args)
apply (TFun t_args t_bod) a_args | otherwise = TError
apply (TVar v) a_args = TAppl (TVar v) a_args
apply _ a_args = TError

expand (TAppl (TFun t_args t_bod) a_args) = replace (M.fromList $ zip t_args a_args) t_bod
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
