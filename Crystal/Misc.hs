module Crystal.Misc where

import Control.Monad.Reader
import Debug.Trace

import Crystal.AST
import Crystal.Pretty
import Crystal.Config

type Step a = Reader Config a

spy :: Show a => Expr a -> Step (Expr a)
spy expr = trace (show expr) $ return expr

spyP :: Show a => Expr a -> Step (Expr a)
spyP expr = trace (show (pretty expr)) $ return expr
