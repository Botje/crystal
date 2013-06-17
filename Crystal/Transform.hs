{-# LANGUAGE PatternGuards #-}
module Crystal.Transform (transformC) where

import Control.Arrow
import Control.Lens
import Control.Monad
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Data.Function
import Data.Generics
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Misc
import Crystal.Pretty
import Crystal.Seq

transformC :: Expr Label -> Step (Expr Label)
transformC = removeSimpleLets <=< toANF <=< expandMacros <=< flattenLets <=< splitLetRecs

splitLetRecs, flattenLets, expandMacros, toANF, removeSimpleLets :: Expr Label -> Step (Expr Label)

toANF expr@(Expr start _) = return $ evalState (go expr return >>= updateRootLabel) (succ start)
  where go :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        go e@(Expr l (Lit x)) k = k e
        go e@(Expr l (Ref r)) k = k e
        go (Expr l (Lambda ids bod)) k = do body_ <- go bod return
                                            k (Expr l (Lambda ids body_))
        go (Expr l (Begin [])) k  = error "Empty begin"
        go (Expr l (Begin [x]) ) k = go x k
        go (Expr l (Begin (x:xs))) k =
          go x $ \e -> do l' <- nextSeq
                          body <- go (Expr l (Begin xs)) return
                          k (Expr l' $ Let [("_", e)] body)
        go (Expr l (If cond cons alt)) k =
          goFloat cond $ \cond_ -> do cons_ <- (go cons return)
                                      alt_ <- (go alt return)
                                      k (Expr l $ If cond_ cons_ alt_)
        go (Expr l (Let [(name,expr)] bod)) k =
          go expr $ \expr_ -> do body_ <- go bod return
                                 k (Expr l $ Let [(name, expr_)] body_)
        go (Expr l (LetRec bnds bod)) k = 
          do bnds_ <- mapM (_2 (flip go return)) bnds
             bod_ <- go bod return
             k (Expr l $ LetRec bnds_ bod_)
        go (Expr l (Appl f args)) k =
          goFloat f $ \f_ ->
            goF args [] $ \args_ ->
              do var <- next "tmp-"
                 labLet <- nextSeq
                 labRef <- nextSeq
                 rest <- k (Expr labRef $ Ref var)
                 return $ Expr labLet $ Let [(var, (Expr l $ Appl f_ args_))] rest

        goFloat :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        goFloat expr k =
          case expr of 
            Expr l (If _ _ _) ->
              float expr k
            Expr l (Begin _) ->
              float expr k
            Expr l (Lambda _ _) ->
              float expr k
            Expr l (Let _ _) ->
              float expr k
            Expr l (LetRec _ _) ->
              float expr k
            Expr l (Appl _ _) ->
              float expr k
            otherwise ->
              go expr k
        
        float :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        float expr k =
          do var <- next "tmp-"
             labRef <- nextSeq
             labLet <- nextSeq
             expr_ <- go expr return
             rest <- k (Expr labRef $ Ref var)
             return $ Expr labLet $ Let [(var, expr_)] rest

        goF [] args k = k (reverse args)
        goF (x:xs) args k = goFloat x $ \x_ -> goF xs (x_:args) k

removeSimpleLets = return . transformBi f
  where f :: Expr Label -> Expr Label
        f (Expr l (Let [(var, e)]
                       (Expr _ (Let [("_", (Expr _ (Ref var')))]
                                    bod)))) | var == var' = Expr l (Let [("_", e)] bod)
        f x = x

makeExpr :: InExpr (Expr Label) -> State Label (Expr Label)
makeExpr expr = nextSeq >>= \s -> return $ Expr s expr

expandMacros expr@(Expr start _) = return $ evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f expr@(Expr l (Appl (Expr _ (Ref r)) args)) =
          case (r, args) of
               ("and", []) -> return $ Expr l (Lit (LitBool True))
               ("and", _ ) -> foldM (g (flip . If)) (last args) (reverse $ init args)
               ("or",  []) -> return $ Expr l (Lit (LitBool False))
               ("or",  _ ) -> foldM (g If) (last args) (reverse $ init args)
               ("with-input-from-file", [_, thunk]) ->
                 return $ Expr l (Appl thunk [])
               ("with-output-to-file", [_, thunk]) ->
                 return $ Expr l (Appl thunk [])
               (_   , [l]) | carLike r ->
                 foldM addCarStep l (reverse $ carSteps r)
               _ -> return expr
        f x = return x
        g fun bod test = do nam <- next "tmp-"
                            ifExpr <- makeExpr =<< liftM3 fun (makeExpr $ Ref nam) (makeExpr $ Ref nam) (return bod)
                            letExpr <- makeExpr $ Let [(nam, test)] ifExpr
                            return letExpr
        addCarStep bod 'a' = makeExpr (Ref "car") >>= \r -> makeExpr (Appl r [bod]) 
        addCarStep bod 'd' = makeExpr (Ref "cdr") >>= \r -> makeExpr (Appl r [bod]) 
                        
carLike [] = False
carLike n  = head n == 'c' && last n == 'r' && all (`elem` "ad") (carSteps n)

carSteps = init . tail

updateRootLabel :: Expr Label -> State Label (Expr Label)
updateRootLabel (Expr _ e) = nextSeq >>= return . flip Expr e 

flattenLets expr@(Expr start _) = return $ evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f (Expr l (Let [] bod)) = return bod
        f (Expr l (Let bnds bod)) | length bnds > 1 =
          do labels <- mapM (const nextSeq) bnds
             let body_ = foldr (\(lab, bnd) body -> Expr lab (Let [bnd] body)) bod $ zip labels bnds
             return body_
        f x = return x

type Idents = S.Set Ident

splitLetRecs expr@(Expr start _) = return $ evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f (Expr _ (LetRec bnds bod)) | length bnds > 1 = float fv names
          where names = S.fromList $ map fst bnds
                fv = M.fromList $ map (second (\e -> names `S.intersection` S.fromList (freeVars e))) bnds
                float :: M.Map Ident Idents -> Idents -> State Label (Expr Label)
                float fv names | S.null names = return bod
                               | otherwise = do lab <- nextSeq
                                                let fv' = M.map (`S.difference` gone) fv
                                                bod <- float fv' (names `S.difference` gone)
                                                let bnds' = filter (flip S.member gone . fst) bnds
                                                if null zeroDeps
                                                   then return $ Expr lab (LetRec bnds' bod)
                                                   else return $ Expr lab (Let bnds' bod)
                  where minStar = minimumBy (compare `on` S.size) stars
                        zeroDeps = [ n | n <- S.toList names, Just s <- return $ M.lookup n fv, S.null s ]
                        gone = if null zeroDeps then minStar else S.fromList zeroDeps
                        stars = map (star fv . S.singleton) $ S.toList names
        f x = return x

star :: M.Map Ident Idents -> Idents -> Idents
star fv names = if names == names' then names' else star fv names'
  where names' = names `S.union` S.unions [ s | n <- S.elems names, Just s <- return $ M.lookup n fv ]
