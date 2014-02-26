{-# LANGUAGE DeriveDataTypeable #-}
module Crystal.AST where

import Control.Lens

import Data.Generics
import Data.Generics.PlateData

import qualified Data.Set as S
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Data.List

type Ident = String -- [a-z][a-zA-Z0-9]*
type TName = String -- [A-Z][a-zA-Z0-9]*
type Label = Int

data LitVal = LitChar   Char
            | LitString String
            | LitInt    Integer
            | LitFloat  Double
            | LitBool   Bool
            | LitSymbol String
            | LitVoid
            | LitList [LitVal]
              deriving (Show, Read, Ord, Eq, Data, Typeable)

data Expr a = Expr a (InExpr (Expr a)) deriving (Show, Read, Ord, Eq, Data, Typeable)
data InExpr e = Lit    LitVal
              | Ref    Ident
              | Appl   e [e]
              | If     e e e
              | Let    [(Ident, e)] e
              | LetRec [(Ident, e)] e
              | Lambda [Ident] e
              | Begin  [e]
                deriving (Show, Read, Ord, Eq, Data, Typeable)

freeVars :: Expr a -> [Ident]
freeVars ast = nub $ snd $ execRWS (fv ast) [] ()
  where fv (Expr _ (Lit _))            = return ()
        fv (Expr _ (Ref r))            = check r
        fv (Expr _ (Appl f args))      = fv f >> forM_ args fv
        fv (Expr _ (Lambda ids bod))   = localWith ids $ fv bod
        fv (Expr _ (Begin exp))        = forM_ exp fv
        fv (Expr _ (If cond cons alt)) = mapM_ fv [cond, cons, alt]
        fv (Expr _ (Let bnds bod))     = do forM_ bnds (fv . snd)
                                            localWith (map fst bnds) $ fv bod
        fv (Expr _ (LetRec bnds bod))  = do forM_ bnds (fv . snd)
                                            localWith (map fst bnds) $ fv bod

        localWith ds = local (union ds)
        check r = do c <- asks $ elem r
                     let g = all (=='*') [head r, last r] -- *global* variables are ignored
                     when (not c && not g) $ tell [r]

ann :: Simple Lens (Expr a) a
ann op (Expr a e) = fmap (\a' -> Expr a' e) (op a)

isRefTo :: Ident -> Expr a -> Bool
isRefTo id (Expr _ (Ref r)) = id == r
isRefTo id       _          = False
