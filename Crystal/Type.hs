{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Type  where

import Control.Lens
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
import Crystal.Misc
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
          | TVarFun VarFun
          | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
          | TAppl Type [TypedLabel]
          | TError
          | TAny
            deriving (Show, Eq, Data, Typeable)

data VarFun = VarFun { vfName  :: Ident,
                       vfLabel :: TLabel,
                       vfFun   :: [TypedLabel] -> TLabel -> Type }
                 deriving (Data, Typeable)


instance Eq VarFun where
  (==) = (==) `on` vfName

instance Show VarFun where
  showsPrec _ vf s = "<function " ++ (show $ vfLabel vf) ++ ">" ++ s

infer :: Expr Label -> Step (Expr TypedLabel)
infer = simplifyLabels <=< generate

simplifyLabels :: Expr TypedLabel -> Step (Expr TypedLabel)
simplifyLabels = return . transformBi simplify

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
trivial (TFun _ _) (TVarFun _) = True
trivial x y | x == y = True
trivial _ _ = False

type Infer a = ReaderT Env (State TVar) a

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
                          Just (_ :*: t_f) -> Expr (l' :*: applyPrim t_f (map getTypeAndLabel args_)) (Appl op_ args_)
                          -- TODO: Generate TVar in l_r, reference with a TIf.
                          Nothing       -> Expr (l' :*: TAny) (Appl op_ args_)
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec [(id, e)] bod -> simply (LetRec [(id, go e)] (go bod))
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
                                   Just (_ :*: typ) | typ == t_f ->
                                     do let applType = applyPrim t_f tl_args
                                        return $ Expr (l' :*: applType) (Appl e_f e_args)
                                   _                             ->
                                     do let applType = TIf (l', getLabel e_f) (TFun tvars TAny) t_f (apply t_f tl_args)
                                        return $ Expr (l' :*: applType) (Appl e_f e_args)
          (LetRec [(nam, exp)] bod) -> do var <- freshTVar
                                          let var_tl = LVar var :*: TVar var
                                          Expr (e_l :*: TFun abod tbod) _ <- local (extend nam var_tl) (go exp)
                                          let t_l = simplify $ leaves tbod
                                          let e_tl = e_l :*: TFun abod t_l
                                          (e_1', t_1) <- local (extend nam e_tl) (goT exp)
                                          (e_bod, t_bod) <- local (extend nam e_tl) (goT bod)
                                          return $ Expr (l' :*: t_bod) (LetRec [(nam, e_1')] e_bod)
          -- TODO: More precision for mutually recursive functions
          (LetRec bnds bod) -> let (nams, funs) = unzip bnds
                                   types = map (\(Expr l (Lambda vs _)) -> LSource l :*: TFun [1..length vs] TAny) funs
                               in local (extendMany nams types) $ do
                                    funs_ <- mapM go funs
                                    (e_bod, t_bod) <- goT bod
                                    return $ Expr (l' :*: t_bod) $ LetRec (zip nams funs_) e_bod
          _ -> error ("Don't know how to infer type for " ++ show e)


type Env = M.Map Ident TypedLabel

main_env :: Env
main_env = M.fromListWith or [
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
    "apply"         --> TFun [1..2] . require [] TAny, -- todo function
    "assoc"         --> TFun [1..2] . require [(TPair,2)] (Tor [TPair, TBool]),
    "assq"          --> TFun [1..2] . require [(TPair,2)] (Tor [TPair, TBool]),
    "assv"          --> TFun [1..2] . require [(TPair,2)] (Tor [TPair, TBool]),
    "atan"          --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "boolean?"      --> TFun [1..1] . require [] TBool,
    "car"           --> TFun [1..1] . require [(TPair,1)] TAny,
    "cdr"           --> TFun [1..1] . require [(TPair,1)] TAny,
    "char?"         --> TFun [1..1] . require [] TBool,
    "char->integer" --> TFun [1..1] . require [(TChar, 1)] TInt,
    "char-alphabetic?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-downcase" --> TFun [1..1] . require [(TChar,1)] TChar,
    "char-lower-case?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-numeric?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-upcase"   --> TFun [1..1] . require [(TChar,1)] TChar,
    "char-upper-case?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-whitespace?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-ci<=?"    --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci<?"     --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci=?"     --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci>=?"    --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci>?"     --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char<=?"       --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char<?"        --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char=?"        --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char>=?"       --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char>?"        --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
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
    "list"          --> makeVarFun "list" (\args -> require [] (if null args then TNull else TPair)),
    "list->vector"  --> TFun [1..1] . require [(TPair,1)] TVec,
    "make-vector"   --> TFun [1..1] . require [(TInt,1)] TVec,
    "make-vector"   --> TFun [1..2] . require [(TInt,1)] TVec,
    "map"           --> TFun [1..2] . require [(TFun [3] TAny,1), (TPair,2)] TPair,
    "max"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "member"        --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memq"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memv"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "min"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
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
    "symbol->string"--> TFun [1..1] . require [(TSymbol,1)] TString,
    "time"          --> TFun [1..1] . require [] TAny,
    "vector->list"  --> TFun [1..1] . require [(TVec,1)] TPair,
    "vector-length" --> TFun [1..1] . require [(TVec,1)] TInt,
    "vector-ref"    --> TFun [1..2] . require [(TVec,1), (TInt,2)] (TAny),
    "vector-set!"   --> TFun [1..3] . require [(TVec,1), (TInt,2)] (TVar 3),
    "vector"        --> makeVarFun "vector" (\args -> require [] TVec),
    "vector?"       --> TFun [1..1] . require [] TBool,
    "void?"         --> TFun [1..1] . require [] TBool,
    "write"         --> TFun [1..1] . require [(TString,1)] TAny,
    "zero?"         --> TFun [1..1] . require [] TBool
  ] where (-->) nam fun = (nam, LPrim nam :*: fun (LPrim nam))
          infix 5 -->
          require tests return blame = foldr (f blame) return tests
          f blame (prim, cause) return = TIf (blame, LVar cause) prim (TVar cause) return
          makeVarFun name vf blame = TVarFun (VarFun name blame vf)
          (LPrim nam :*: fun1) `or` (LPrim _ :*: fun2) = LPrim nam :*: Tor [fun1, fun2]


extend :: Ident -> TypedLabel -> Env -> Env
extend = M.insert

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
