{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
{-#LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}
module Crystal.Infer where

import Control.Applicative
import Control.Lens hiding (transform, (.=))
import Control.Monad
import Data.Aeson hiding (encode)
import Data.Function
import Data.Generics
import Data.Generics.Uniplate.Operations
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text.Lazy as T

import Crystal.AST
import Crystal.Config
import Crystal.Env
import Crystal.JSON
import Crystal.Misc
import Crystal.RecursiveType
import Crystal.Seq
import Crystal.Tuple
import Crystal.Type

infer :: Expr Label -> Step (Expr TypedLabel)
infer = maybeDumpTree <=< maybeDumpTypes <=< generate

maybeDumpTree :: Expr TypedLabel -> Step (Expr TypedLabel)
maybeDumpTree expr =
  do dump <- asks (^.cfgDumpTree)
     when dump $ do
       report "check-inference" $ encode expr
     return expr

instance ToJSON TypedLabel where
  toJSON (l :*: t :*: ef) = object [ "label" .= show l, "type" .= show t, "effect" .= toJSON (S.toList ef) ]

maybeDumpTypes :: Expr TypedLabel -> Step (Expr TypedLabel)
maybeDumpTypes expr =
  do dump <- asks (^.cfgDumpTypes)
     when dump $ do
       let types = [ show k ++ " ==> " ++ show v | (k,v) <- sort $ dumpTypes expr ]
       report "Types dump" $ T.pack $ unlines types
     return expr

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
                 Appl op [var, arg] | Expr l_op (Ref "set!") <- op ->
                   let op'  = Expr (LSource l_op :*: TAny :*: emptyEffect) (Ref "set!")
                       Expr l_arg (Ref r) = var
                       var' = Expr (LSource l_arg :*: TAny :*: emptyEffect) (Ref r)
                   in Expr (l' :*: TAny :*: emptyEffect) (Appl op' [var', go arg])
                 Appl op args ->
                  let (op_, args_) = (go op, map go args)
                      (Expr (l_r :*: _) (Ref r)) = op_
                      typ = TIf (l', l_r) (TFun (zipWith const [1..] args_) emptyEffect TAny) TAny TAny
                  in Expr (l' :*: typ :*: mempty) (Appl op_ args_)
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
                 Lambda ids r bod     -> simply (Lambda ids r (go bod))
                 Begin es             -> simply (Begin $ map go es)

type Infer a = ReaderT Env (State TVar) a

generateSmart :: Expr Label -> Expr TypedLabel
generateSmart e@(Expr start _) = evalState (runReaderT (go e) main_env) (succ start)
  where allSet :: Effect
        allSet = effectFromList [ r | Expr _ (Ref r) <- sets ]
          where sets = [ var | Expr _ (Appl f [var, _]) <- universeBi e :: [Expr Label], isRefTo "set!" f ]

        effectToLabels :: Effect -> Infer (S.Set TLabel)
        effectToLabels ef = do env <- ask
                               let effects = [ tl^._1 | nam <- S.toList ef, Just tl <- return (M.lookup nam env) ]
                               return $ S.fromList effects

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
          (Lit (LitList els)) -> return $ Expr (l' :*: TList :*: mempty) (Lit (LitList els))
          (Lit (LitPair x y)) -> return $ Expr (l' :*: TPair :*: mempty) (Lit (LitPair x y))
          (Ref i) -> do lt <- asks (M.lookup i)
                        case lt of
                          Just (l :*: t :*: ef)
                            | i `varInEffect` allSet -> return $ Expr (l' :*: TAny :*: emptyEffect) (Ref i)
                            | otherwise              -> return $ Expr (l' :*: simplify t :*: ef) (Ref i)
                          Nothing -> error ("Unbound variable " ++ show i)
          (If cond cons alt) -> do (e_0, t_0, ef_0) <- goT cond
                                   (e_1, t_1, ef_1) <- goT cons
                                   (e_2, t_2, ef_2) <- goT alt
                                   let t_if = if t_1 == t_2 then t_1 else Tor [t_1, t_2]
                                   let ef_if = ef_1 `mappend` ef_2
                                   return $ Expr (l' :*: t_if :*: ef_if) (If e_0 e_1 e_2)
          -- TODO: Type rule for this is wrong in thesis!
          (Let [(nam, exp)] bod) -> do (e_x, t_1, ef_x) <- goT exp
                                       let t_l = simplify $ leaves t_1
                                       case t_l of
                                            TAppl _ _ -> do var <- freshTVar
                                                            let bod_tl = getLabel e_x :*: TVar var :*: emptyEffect
                                                            (e_bod, t_bod, ef_bod) <- local (extend nam bod_tl) (goT bod)
                                                            forbiddenLabels <- local (extend nam bod_tl) $ effectToLabels ef_x
                                                            let t_let = chainWith (\t -> TChain t var (getLabel e_x) $ stripLabels forbiddenLabels t_bod) t_1
                                                            let ef_let = ef_x `mappend` (S.delete nam ef_bod)
                                                            return $ Expr (l' :*: t_let :*: ef_let) (Let [(nam, e_x)] e_bod)
                                            _ -> do let bod_tl = getLabel e_x :*: t_l :*: mempty
                                                    (e_bod, t_bod, ef_bod) <- local (extend nam bod_tl) (goT bod)
                                                    forbiddenLabels <- local (extend nam bod_tl) $ effectToLabels ef_x
                                                    let t_let = chainWithEffect t_1 forbiddenLabels t_bod
                                                    let ef_let = ef_x `mappend` (S.delete nam ef_bod)
                                                    return $ Expr (l' :*: t_let :*: ef_let) (Let [(nam, e_x)] e_bod)
          (Lambda ids r bod) -> do a_ids <- mapM (const freshTVar) ids
                                   a_r   <- freshTVar
                                   env'  <- asks (extendMany ids $ map (\v -> LVar v :*: TVar v :*: mempty) a_ids)
                                   let env'' = maybe env' (\x -> extend x (LVar a_r :*: TList :*: mempty) env') r
                                   (e_bod, t_bod, ef_bod) <- local (const env'') (goT bod)
                                   let t_lambda = case r of
                                         Nothing -> TFun a_ids ef_bod $ simplify t_bod
                                         Just _  ->
                                           -- TODO: checks on a_r will crash.
                                           let f tls cause | length tls < length ids = TError
                                               f tls cause = apply (TFun a_ids ef_bod t_bod) (take (length a_ids) tls)
                                           in TVarFun $ VarFun ("lambda-" ++ show l) l' f
                                   return $ Expr (l' :*: t_lambda :*: emptyEffect) (Lambda ids r e_bod)
          (Appl f args)
            | isRefTo "set!" f -> do let [Expr l_v (Ref var), exp] = args
                                     (e_exp, t_exp, ef_exp) <- goT exp
                                     let t_set = TVoid 
                                     let ef_set = effectSingleton var `mappend` ef_exp
                                     let e_f = Expr (LSource (f^.ann) :*: TAny :*: emptyEffect) (Ref "set!")
                                     let e_var = Expr (LSource l_v :*: TAny :*: emptyEffect) (Ref var)
                                     return $ Expr (l' :*: t_set :*: ef_set) (Appl e_f [e_var, e_exp])
            | otherwise -> do (e_f, t_f, ef_f) <- goT f
                              e_args <- mapM go args
                              let tvars = [1..length args]
                              let tl_args = map getTypeAndLabel e_args
                              let (Expr _ (Ref fun)) = e_f
                              case M.lookup fun main_env of -- TODO: why main_env?
                                   Just (LPrim nam :*: typ :*: _) ->
                                     -- TODO: Extract effect from function (see FunEffects)
                                     do let t_apply = simplify $ instantiatePrim nam l' (applyPrim t_f tl_args)
                                        return $ Expr (l' :*: t_apply :*: mempty) (Appl e_f e_args)
                                   _ ->
                                     do let t_apply = simplify $ TIf (l', getLabel e_f) (TFun tvars emptyEffect TAny) t_f (apply t_f tl_args)
                                        let ef_apply = maybe allSet id $ funEffects t_f
                                        return $ Expr (l' :*: t_apply :*: ef_apply) (Appl e_f e_args)
          -- Chain types of expressions together, removing checks on variables that are set beforehand
          (Begin exps) -> do exps_ <- mapM go exps 
                             typesEffects <- mapM (\e -> liftM2 (,) (return $ getType e) (effectToLabels $ getEffect e)) exps_
                             let t_begin = simplify $ foldr (\(t1, labs) t -> chainWithEffect t1 labs t) (fst $ last typesEffects) (init typesEffects)
                             let ef_begin = mconcat $ map getEffect exps_
                             return $ Expr (l' :*: t_begin :*: ef_begin) (Begin exps_)
          (LetRec bnds bod) -> let (nams, funs) = unzip bnds
                               in do vars_binds_tl <- forM funs $ \(Expr l (Lambda vs _ _)) ->
                                        do var <- freshTVar
                                           -- TODO r
                                           vars <- replicateM (length vs) freshTVar
                                           let t_fun = TFun vars emptyEffect $ TAppl (TVar var) [LVar v :*: TVar v | v <- vars]
                                           let ef_fun = emptyEffect
                                           return (var, LSource l :*: t_fun :*: ef_fun)
                                     let (vars, bnds_tl) = unzip vars_binds_tl
                                     -- reuse the inferred labels and tvars for the actual inference of functions
                                     funs_tl <- local (extendMany nams bnds_tl) $
                                       forM bnds $ \(nam, Expr _ (Lambda vs r bod)) ->
                                         do Just (l_fun :*: TFun tvars _ _ :*: _) <- asks $ M.lookup nam
                                            let tl_vars = map (\v -> LVar v :*: TVar v :*: emptyEffect) tvars
                                            (e_funbod, t_funbod, ef_funbod) <- local (extendMany vs tl_vars) (goT bod)
                                            let t_fun = TFun tvars ef_funbod t_funbod
                                            return $ Expr (l_fun :*: t_fun :*: emptyEffect) (Lambda vs r e_funbod)
                                     let t_funs = map getType funs_tl
                                     let t_funs' = solveLetrec (zip vars t_funs)
                                     let ef_fun = mconcat $ map (\(_, TFun _ ef _) -> ef) t_funs'
                                     let funs_tl' = map (\(var,t) -> LVar var :*: simplify t :*: ef_fun) t_funs'
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

applyPrim :: Type -> [TypeNLabel] -> Type
applyPrim t_f@(Tor funs) t_args =
  case listToMaybe $ filter (flip applies t_args) funs of
       Nothing  -> apply t_f t_args
       Just fun -> apply fun t_args
applyPrim t_f t_args = apply t_f t_args

instantiatePrim :: Ident -> TLabel -> Type -> Type
instantiatePrim nam lab t = transform f t
  where f (TIf (LPrim blame, cause) t1 t2 rest) | blame == nam = TIf (lab, cause) t1 t2 rest
        f x = x

chainWithEffect :: Type -> S.Set TLabel -> Type -> Type
chainWithEffect t forbidden t_c = chain t $ stripLabels forbidden t_c

stripLabels :: S.Set TLabel -> Type -> Type
stripLabels set t | S.null set = simplify t
stripLabels forbidden t = maybe t' id $ strip t'
  where t' = simplify t
        a `plus` b = a `mplus` Just b
        strip to@(Tor ts) | isNothing all = Nothing
                          | otherwise     = Just $ Tor (zipWith f ts' ts)
          where ts' = map strip ts
                all = foldl' mplus Nothing ts'
                f mt t = maybe t id mt
        strip tf@(TFun args ef body) = TFun args ef `fmap` strip body
        strip tif@(TIf (blame, cause) t_t t_1 t)
              | cause `S.member` forbidden = t' `plus` t
              | isNothing all              = Nothing
              | otherwise                  = liftA2 (TIf (blame, cause) t_t)  (t_1' `plus` t_1) (t' `plus` t)
          where (t_1', t') = (strip t_1, strip t)
                all = t_1' `mplus` t'
        strip ta@(TAppl fun tls) | isNothing all = Nothing
                                 | otherwise     = Just $ TAppl (maybe fun id fun') (zipWith f ts' tls)
          where (fun', ts') = (strip fun, map (strip . view _2) tls)
                all = foldl' mplus fun' ts'
                f Nothing tl = tl
                f (Just t) tl = tl & _2 .~ t
        strip tc@(TChain appl var lab body) | isNothing all = Nothing
                                            | otherwise     = liftA2 (\a b -> TChain a var lab b) (appl' `plus` appl) (body' `plus` body)
          where (appl', body') = (strip appl, strip body)
                all = appl' `mplus` body'
        strip t = Nothing

leaves :: Type -> Type
leaves (Tor ts) = Tor $ map leaves ts
leaves (TIf _ t_t t t_1) = leaves t_1
leaves t = t
