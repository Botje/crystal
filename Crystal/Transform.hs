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
transformC ast = toANF $ ast

spy ast = trace (pretty ast ++ "\n=============\n") ast

isSimple Lit{} = True
isSimple Ref{} = True
isSimple Lambda{} = True
isSimple _ = False

toANF expr = evalState (go expr return) 1000
  where go :: Expr -> (Expr -> State Int Expr) -> State Int Expr
        go (Lit x) k = k (Lit x)
        go (Ref r) k = k (Ref r)
        go (Lambda ids bod) k = k . Lambda ids =<< go bod return
        go (Begin []) k  = error "Empty begin"
        go (Begin [x])  k = go x k
        go (Begin (x:xs)) k = go x $ \_ -> go (Begin xs) k
        go (If cond cons alt) k = go cond $ \cond_ -> k =<< liftM2 (If cond_) (go cons return) (go alt return)
        go (Let [] bod) k = go bod k
        go (Let ((name,expr):bnds) bod) k = go expr $ \expr_ -> k . Let [(name, expr_)] =<< go (Let bnds bod) return
        go (LetRec bnds bod) k = k . LetRec bnds =<< go bod return
        go (Appl f args) k = go f $ \f_ -> goF args [] $ \args_ -> k (Appl f_ args_)
        goF [] args k = k (reverse args)
        goF (x:xs) args k | isSimple x = goF xs (x:args) k
                          | (Appl _ _) <- x = next "tmp-" >>= \var -> go x $ \x_ -> return . Let [(var, x_)] =<< goF xs (Ref var:args) k
                          | otherwise  = go x $ \x_ -> goF xs (x_:args) k
