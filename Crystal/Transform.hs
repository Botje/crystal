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

transformC :: Expr -> Expr
transformC ast = flattenLets . removeSimpleLets . toANF $ ast

spy ast = trace (pretty ast ++ "\n=============\n") ast

isSimple Lit{} = True
isSimple Ref{} = True
isSimple Lambda{} = True
isSimple _ = False

toANF expr = evalState (go expr return) 1000
  where go :: Expr -> (Expr -> State Int Expr) -> State Int Expr
        go (Lit x) k = k (Lit x)
        go (Ref r) k = k (Ref r)
        go (Lambda ids bod) k = do body_ <- go bod return
                                   k $ Lambda ids body_
        go (Begin []) k  = error "Empty begin"
        go (Begin [x])  k = go x k
        go (Begin (x:xs)) k = go x $ \_ -> go (Begin xs) k
        go (If cond cons alt) k =
          go cond $ \cond_ -> do cons_ <- (go cons return)
                                 alt_ <- (go alt return)
                                 k $ If cond_ cons_ alt_
        go (Let [] bod) k = go bod k
        go (Let ((name,expr):bnds) bod) k = go expr $ \expr_ -> k . Let [(name, expr_)] =<< go (Let bnds bod) return
        go (LetRec bnds bod) k = k . LetRec bnds =<< go bod return
        go (Appl f args) k = go f $ \f_ ->
                                goF args [] $ \args_ ->
                                  do var <- next "tmp-"
                                     rest <- k (Ref var)
                                     return $ Let [(var, Appl f_ args_)] rest

        goF [] args k = k (reverse args)
        goF (x:xs) args k | isSimple x = goF xs (x:args) k
                          | otherwise  = go x $ \x_ -> goF xs (x_:args) k

removeSimpleLets = transform f
  where f (Let [(bnd, app)] bod) | bod == Ref bnd = app
        f x = x

flattenLets = transform f
  where f (Let bnds bod) | length bnds > 1 = foldr (\bnd bod -> Let [bnd] bod) bod bnds
        f x = x
