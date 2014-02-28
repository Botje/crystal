{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Infer where

import Control.Applicative
import Control.Lens hiding (transform)
import Control.Monad
import Data.Function
import Data.Generics
import Data.Generics.Biplate
import Data.List
import Data.Maybe
import Data.Monoid
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S

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
                 simply = Expr (l' :*: TAny :*: mempty) in
               case expr of
                 Appl op args         -> 
                  let (op_, args_) = (go op, map go args)
                      (Expr l_r (Ref r)) = op_
                  in case M.lookup r main_env of
                          Just (LPrim nam :*: t_f :*: _) -> Expr (l' :*: applyPrim (instantiatePrim nam l' t_f) (map getTypeAndLabel args_) :*: mempty) (Appl op_ args_)
                          -- TODO: Generate TVar in l_r, reference with a TIf.
                          Nothing       -> Expr (l' :*: TAny :*: mempty) (Appl op_ args_)
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
                 Lambda ids bod       -> simply (Lambda ids (go bod))
                 Begin es             -> simply (Begin $ map go es)

type Infer a = ReaderT Env (State TVar) a

generateSmart :: Expr Label -> Expr TypedLabel
generateSmart e@(Expr start _) = evalState (runReaderT (go e) main_env) (succ start)
  where allSet :: Effect
        allSet = effectFromList [ r | Expr _ (Ref r) <- sets ]
          where sets = [ var | Expr _ (Appl f [var, _]) <- universeBi e :: [Expr Label], isRefTo "set!" f ]

        effectToLabels :: Effect -> Infer (S.Set TLabel)
        effectToLabels ef = do env <- ask
                               let typedlabels = catMaybes $ map (flip M.lookup env) $ S.toList ef
                               return $ S.fromList $ map (^._1) typedlabels

        goT :: Expr Label -> Infer (Expr TypedLabel, Type, Effect)
        goT e = go e >>= \e' -> return (e', getType e', getEffect e')

        go :: Expr Label -> Infer (Expr TypedLabel)
        go (Expr l e) = let l' = LSource l in
          case e of
          (Lit (LitString s)) -> return $ Expr (l' :*: TString :*: mempty) (Lit (LitString s))
          (Lit (LitChar c))   -> return $ Expr (l' :*: TChar :*: mempty) (Lit (LitChar c))
          (Lit (LitFloat f))  -> return $ Expr (l' :*: TInt :*: mempty) (Lit (LitFloat f)) -- TODO float
          (Lit (LitInt i))    -> return $ Expr (l' :*: TInt :*: mempty) (Lit (LitInt i))
          (Lit (LitBool b))   -> return $ Expr (l' :*: TBool :*: mempty) (Lit (LitBool b))
          (Lit (LitSymbol s)) -> return $ Expr (l' :*: TSymbol :*: mempty) (Lit (LitSymbol s))
          (Lit (LitVoid))     -> return $ Expr (l' :*: TVoid :*: mempty) (Lit (LitVoid))
          (Lit (LitList els)) | null els  -> return $ Expr (l' :*: TNull :*: mempty) (Lit (LitList els))
                              | otherwise -> return $ Expr (l' :*: TPair :*: mempty) (Lit (LitList els))
          (Ref i) -> do lt <- asks (M.lookup i)
                        case lt of
                          Just (l :*: t :*: ef)
                            | i `varInEffect` allSet -> return $ Expr (l :*: TAny :*: emptyEffect) (Ref i)
                            | otherwise              -> return $ Expr (l :*: t    :*: ef) (Ref i)
                          Nothing -> error ("Unbound variable " ++ show i)
          (If cond cons alt) -> do (e_0, t_0, ef_0) <- goT cond
                                   (e_1, t_1, ef_1) <- goT cons
                                   (e_2, t_2, ef_2) <- goT alt
                                   let t_if = Tor [t_1, t_2]
                                   let ef_if = ef_1 `mappend` ef_2
                                   return $ Expr (l' :*: t_if :*: ef_if) (If e_0 e_1 e_2)
          -- TODO: Type rule for this is wrong in thesis!
          (Let [(nam, exp)] bod) -> do (e_x, t_1, ef_x) <- goT exp
                                       let t_l = leaves t_1
                                       let bod_tl = getLabel e_x :*: t_l :*: mempty
                                       (e_bod, t_bod, ef_bod) <- local (extend nam bod_tl) (goT bod)
                                       forbiddenLabels <- local (extend nam bod_tl) $ effectToLabels ef_x
                                       let t_let = chainWithEffect t_1 forbiddenLabels t_bod
                                       let ef_let = ef_x `mappend` (S.delete nam ef_bod)
                                       return $ Expr (l' :*: t_let :*: ef_let) (Let [(nam, e_x)] e_bod)
          (Lambda args bod) -> do a_args <- mapM (const freshTVar) args
                                  (e_bod, t_bod, ef_bod) <- local (extendMany args $ map (\v -> LVar v :*: TVar v :*: mempty) a_args) (goT bod)
                                  let t_lambda = TFun a_args ef_bod t_bod
                                  return $ Expr (l' :*: t_lambda :*: emptyEffect) (Lambda args e_bod)
          (Appl f args)
            | isRefTo "set!" f -> do let [Expr l_v (Ref var), exp] = args
                                     (e_exp, t_exp, ef_exp) <- goT exp
                                     let t_set = TVoid 
                                     let ef_set = effectSingleton var `mappend` ef_exp
                                     let e_f = Expr (LSource (f^.ann) :*: TAny :*: emptyEffect) (Ref "set!")
                                     let e_var = Expr (LSource l_v :*: TAny :*: mempty) (Ref var)
                                     return $ Expr (l' :*: t_set :*: ef_set) (Appl e_f [e_var, e_exp])
            | otherwise -> do (e_f, t_f, ef_f) <- goT f
                              e_args <- mapM go args
                              let tvars = [1..length args]
                              let tl_args = map getTypeAndLabel e_args
                              let (Expr _ (Ref fun)) = e_f
                              case M.lookup fun main_env of -- TODO: why main_env?
                                   Just (LPrim nam :*: typ :*: _) ->
                                     -- TODO: Extract effect from function (see FunEffects)
                                     do let t_apply = applyPrim (instantiatePrim nam l' t_f) tl_args
                                        return $ Expr (l' :*: t_apply :*: mempty) (Appl e_f e_args)
                                   _ ->
                                     do let t_apply = TIf (l', getLabel e_f) (TFun tvars emptyEffect TAny) t_f (apply t_f tl_args)
                                        let ef_apply = maybe allSet id $ funEffects t_f
                                        return $ Expr (l' :*: t_apply :*: ef_apply) (Appl e_f e_args)
          -- Chain types of expressions together, removing checks on variables that are set beforehand
          (Begin exps) -> do exps_ <- mapM go exps 
                             typesEffects <- mapM (\e -> liftM2 (,) (return $ getType e) (effectToLabels $ getEffect e)) exps_
                             let t_begin = foldr (\(t1, labs) t -> chainWithEffect t1 labs t) (fst $ last typesEffects) (init typesEffects)
                             let ef_begin = mconcat $ map getEffect exps_
                             return $ Expr (l' :*: t_begin :*: ef_begin) (Begin exps_)
          (LetRec bnds bod) -> let (nams, funs) = unzip bnds
                               in do vars_binds_tl <- forM funs $ \fun ->
                                        do var <- freshTVar
                                           let (Expr l (Lambda vs _)) = fun
                                           let n = length vs
                                           let t_fun = TFun [1..n] emptyEffect $ TAppl (TVar var) [LVar v :*: TVar v | v <- [1..n]]
                                           let ef_fun = mempty
                                           return (var, LSource l :*: t_fun :*: ef_fun)
                                     let (vars, bnds_tl) = unzip vars_binds_tl
                                     funs_tl <- local (extendMany nams bnds_tl) $ mapM go funs
                                     let t_funs = map getType funs_tl
                                     -- TODO: Infer effects and use below
                                     let t_funs' = solveLetrec vars t_funs
                                     let funs_tl' = zipWith (\var t -> LVar var :*: t :*: mempty) vars t_funs'
                                     local (extendMany nams funs_tl') $
                                       do e_funs <- mapM go funs
                                          (e_bod, t_bod, ef_bod) <- goT bod
                                          return $ Expr (l' :*: t_bod :*: ef_bod) (LetRec (zip nams e_funs) e_bod)
          _ -> error ("Don't know how to infer type for " ++ show e)

-- Just ef: only those in ef, Nothing: *all* the variables.
funEffects :: Type -> Maybe Effect
funEffects (Tor ts)      = mconcat <$> mapM funEffects ts
funEffects (TIf _ _ _ t) = funEffects t
funEffects (TVarFun _)   = Just emptyEffect
funEffects (TFun _ ef _) = Just ef
funEffects (TVar _)      = Nothing
funEffects _             = Just emptyEffect

extendMany :: Ord k => [k] -> [v] -> M.Map k v -> M.Map k v
extendMany keys vals env = foldr (uncurry M.insert) env (zip keys vals)

apply :: Type -> [TypeNLabel] -> Type
apply (Tor ts) a_args = Tor $ map (flip apply a_args) ts
apply (TIf l t_t t_a t) a_args = TIf l t_t t_a (apply t a_args)
apply vf@(TVarFun _) a_args = expand (TAppl vf a_args)
apply t_f@(TFun t_args ef t_bod) a_args | applies t_f a_args = expand (TAppl (TFun t_args ef t_bod) a_args)
                                        | otherwise = TError
apply (TVar v) a_args = TAppl (TVar v) a_args
apply _ a_args = TError

applies :: Type -> [TypeNLabel] -> Bool
applies (TFun t_args _ t_bod) a_args = length t_args == length a_args  
applies _ _ = False

applyPrim :: Type -> [TypeNLabel] -> Type
applyPrim t_f@(Tor funs) t_args =
  case listToMaybe $ filter (flip applies t_args) funs of
       Nothing  -> apply t_f t_args
       Just fun -> apply fun t_args
applyPrim t_f@(TFun t_args _ t_bod) a_args | applies t_f a_args = apply t_f a_args
applyPrim t_f t_args = apply t_f t_args

instantiatePrim :: Ident -> TLabel -> Type -> Type
instantiatePrim nam lab t = transform f t
  where f (TIf (LPrim blame, cause) t1 t2 rest) | blame == nam = TIf (lab, cause) t1 t2 rest
        f x = x

expand :: Type -> Type
expand (TAppl (TFun t_args _ t_bod) a_args) = replace (M.fromList $ zip t_args a_args) t_bod
expand (TAppl (TVarFun (VarFun _ lab vf)) a_args) = vf a_args lab
expand typ = typ

chainWithEffect :: Type -> S.Set TLabel -> Type -> Type
chainWithEffect t forbidden t_c = go t
  where t_c' = transform strip t_c
        go (Tor ts) = Tor $ map go ts
        go (TIf (blame, cause) t_t t_1 t) 
          = TIf (blame, cause) t_t t_1 $ go t
        go t = t_c'
        strip tif@(TIf (blame, cause) t_t t_1 t)
              | cause `S.member` forbidden = t
              | otherwise                  = tif
        strip t = t

chain :: Type -> Type -> Type
chain t1 t2 = chainWithEffect t1 S.empty t2

leaves :: Type -> Type
leaves (Tor ts) = Tor $ map leaves ts
leaves (TIf _ t_t t t_1) = leaves t_1
leaves t = t

replace :: M.Map TVar TypeNLabel -> Type -> Type
replace env (TVar var) | Just (l :*: t) <- M.lookup var env = t
replace env (Tor ts) = Tor $ map (replace env) ts
replace env (TFun args ef bod) = TFun args ef $ replace (extendMany args (map (\v -> LVar v :*: TVar v) args) env) bod
replace env (TIf (l1,l2) t_1 t_2 t_3) = TIf (l1,l2') (replace env t_1) (replace env t_2) (replace env t_3)
  where l2' = case l2 of LVar tv | Just (l :*: t) <- M.lookup tv env -> l
                         x -> x
replace env (TAppl fun args) = apply (replace env fun) (map (over _2 (replace env)) args)
replace env x = x
