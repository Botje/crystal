{-# LANGUAGE DeriveDataTypeable #-}
module Crystal.AST where

import Data.Generics
import Data.Generics.PlateData

import qualified Data.Set as S
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Data.List

type Ident = String -- [a-z][a-zA-Z0-9]*
type TName = String -- [A-Z][a-zA-Z0-9]*

data LitVal = LitChar   Char
            | LitString String
            | LitInt    Integer
            | LitFloat  Double
            | LitBool   Bool
              deriving (Show, Read, Ord, Eq, Data, Typeable)

data Expr = Lit    LitVal
          | Ref    Ident
          | Appl   Expr [Expr]
          | If     Expr Expr Expr
          | Let    [(Ident, Expr)] Expr
          | LetRec [(Ident, Expr)] Expr
          | Lambda [Ident] Expr
          | Begin  [Expr]
            deriving (Show, Read, Ord, Eq, Data, Typeable)

freeVars :: Expr -> [Ident]
freeVars ast = nub $ snd $ execRWS (fv ast) [] ()
  where fv (Lit _)            = return ()
        fv (Ref r)            = check r
        fv (Appl _ args)      = forM_ args fv
        fv (Lambda ids bod)   = localWith ids $ fv bod
        fv (Begin exp)        = forM_ exp fv
        fv (If cond cons alt) = mapM_ fv [cond, cons, alt]
        fv (Let bnds bod)     = do forM_ bnds (fv . snd)
                                   localWith (map fst bnds) $ fv bod
        fv (LetRec bnds bod)  = do forM_ bnds (fv . snd)
                                   localWith (map fst bnds) $ fv bod

        localWith ds = local (union ds)
        check r = do c <- asks $ elem r
                     let g = all (=='*') [head r, last r] -- *global* variables are ignored
                     when (not c && not g) $ tell [r]

