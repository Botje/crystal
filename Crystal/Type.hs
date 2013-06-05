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


data Type = TInt | TString | TBool | TSymbol | TVoid | TVec | TPair | TNull | TChar
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
          (Lit (LitChar c)) -> return $ Expr (l' :*: TChar) (Lit (LitChar c))
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
    "="             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "+"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "*"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "-"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "/"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "<"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    ">"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    ">="            --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "<="            --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "append"        --> TFun [1..2] . require [(TPair,1), (TPair,2)] TPair,
    "assoc"         --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "assq"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "assv"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "atan"          --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "boolean?"      --> TFun [1..1] . require [] TBool,
    "car"           --> TFun [1..1] . require [(TPair,1)] TAny,
    "cdr"           --> TFun [1..1] . require [(TPair,1)] TAny,
    "char?"         --> TFun [1..1] . require [] TBool,
    "cons"          --> TFun [1..2] . require [] TPair,
    "cos"           --> TFun [1..1] . require [(TInt,1)] TInt,
    "display"       --> TFun [1..1] . require [(TString,1)] TAny,
    "eq?"           --> TFun [1..2] . require [] TBool,
    "equal?"        --> TFun [1..2] . require [] TBool,
    "eqv?"          --> TFun [1..2] . require [] TBool,
    "error"         --> TFun [1..1] . require [(TString,1)] TAny,
    "even?"         --> TFun [1..1] . require [] TBool,
    "expt"          --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "for-each"      --> TFun [1..2] . require [(TFun [3] TAny,1), (TPair,2)] TVoid,
    "gcd"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "lcm"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "length"        --> TFun [1..1] . require [(TPair,1)] TInt,
    "list->vector"  --> TFun [1..1] . require [(TPair,1)] TVec,
    "make-vector"   --> TFun [1..2] . require [(TInt,1)] TVec,
    "map"           --> TFun [1..2] . require [(TFun [3] TAny,1), (TPair,2)] TPair,
    "member"        --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memq"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memv"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "modulo"        --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "negative?"     --> TFun [1..1] . require [] TBool,
    "newline"       --> TFun []     . require [] TVoid,
    "not"           --> TFun [1..1] . require [] TBool,
    "null?"         --> TFun [1..1] . require [] TBool,
    "number?"       --> TFun [1..1] . require [] TBool,
    "odd?"          --> TFun [1..1] . require [] TBool,
    "pair?"         --> TFun [1..1] . require [] TBool,
    "port?"         --> TFun [1..1] . require [] TBool,
    "positive?"     --> TFun [1..1] . require [] TBool,
    "procedure?"    --> TFun [1..1] . require [] TBool,
    "quotient"      --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "read"          --> TFun []     . require [] TAny,
    "remainder"     --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "reverse"       --> TFun [1..1] . require [(TPair,1)] TPair,
    "set!"          --> TFun [1..1] . require [] TVoid,
    "set-car!"      --> TFun [1..2] . require [(TPair, 1)] TVoid,
    "set-cdr!"      --> TFun [1..2] . require [(TPair, 1)] TVoid,
    "sin"           --> TFun [1..1] . require [(TInt,1)] TInt,
    "string-append" --> TFun [1..2] . require [(TString,1), (TString,2)] TString,
    "string?"       --> TFun [1..1] . require [] TBool,
    "symbol?"       --> TFun [1..1] . require [] TBool,
    "time"          --> TFun [1..1] . require [] TAny,
    "vector->list"  --> TFun [1..1] . require [(TVec,1)] TPair,
    "vector-length" --> TFun [1..1] . require [(TVec,1)] TInt,
    "vector-ref"    --> TFun [1..2] . require [(TVec,1), (TInt,2)] (TAny),
    "vector-set!"   --> TFun [1..3] . require [(TVec,1), (TInt,2)] (TVar 3),
    "vector?"       --> TFun [1..1] . require [] TBool,
    "void?"         --> TFun [1..1] . require [] TBool,
    "write"         --> TFun [1..1] . require [(TString,1)] TAny,
    "zero?"         --> TFun [1..1] . require [] TBool
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
