{-# LANGUAGE PatternGuards #-}
module Crystal.Transform (transformC) where

import Control.Arrow
import Control.Monad
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import Data.List
import Data.Maybe
import qualified Data.Set as S
import Data.Generics.Biplate
import Debug.Trace

import Crystal.AST
import Crystal.Seq
import Crystal.Pretty

transformC :: Expr Label -> Expr Label
transformC ast = removeSimpleLets . toANF . flattenLets $ ast

spy ast = trace (pretty ast ++ "\n=============\n") ast

isSimple (Expr _ Lit{}) = True
isSimple (Expr _ Ref{}) = True
isSimple (Expr _ Lambda{}) = True
isSimple _ = False

toANF expr@(Expr start _) = evalState (go expr return >>= updateRootLabel) (succ start)
  where go :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        go e@(Expr l (Lit x)) k = k e
        go e@(Expr l (Ref r)) k = k e
        go (Expr l (Lambda ids bod)) k = do body_ <- go bod return
                                            k (Expr l (Lambda ids body_))
        go (Expr l (Begin [])) k  = error "Empty begin"
        go (Expr l (Begin [x]) ) k = go x k
        go (Expr l (Begin (x:xs))) k = go x $ \_ -> go (Expr l (Begin xs)) k
        go (Expr l (If cond cons alt)) k =
          go cond $ \cond_ -> do cons_ <- (go cons return)
                                 alt_ <- (go alt return)
                                 k (Expr l $ If cond_ cons_ alt_)
        go (Expr l (Let [(name,expr)] bod)) k =
          go expr $ \expr_ -> do body_ <- go bod return
                                 k (Expr l $ Let [(name, expr_)] body_)
        go (Expr l (LetRec bnds bod)) k = k . Expr l . LetRec bnds =<< go bod return
        go (Expr l (Appl f args)) k =
          go f $ \f_ ->
            goF args [] $ \args_ ->
              do var <- next "tmp-"
                 labLet <- nextSeq
                 labRef <- nextSeq
                 rest <- k (Expr labRef $ Ref var)
                 return $ Expr labLet $ Let [(var, (Expr l $ Appl f_ args_))] rest

        goF [] args k = k (reverse args)
        goF (x:xs) args k | isSimple x = goF xs (x:args) k
                          | otherwise  = go x $ \x_ -> goF xs (x_:args) k

removeSimpleLets :: Expr Label -> Expr Label
removeSimpleLets = transformBi f
  where f :: Expr Label -> Expr Label
        f (Expr _ (Let [(bnd, app)] (Expr _ (Ref bnd')))) | bnd == bnd' = app
        f x = x

updateRootLabel :: Expr Label -> State Label (Expr Label)
updateRootLabel (Expr _ e) = nextSeq >>= return . flip Expr e 

flattenLets expr@(Expr start _) = evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f (Expr l (Let [] bod)) = return bod
        f (Expr l (Let bnds bod)) | length bnds > 1 =
          do labels <- mapM (const nextSeq) bnds
             let body_ = foldr (\(lab, bnd) body -> Expr lab (Let [bnd] body)) bod $ zip labels bnds
             return body_
        f x = return x
