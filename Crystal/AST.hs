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
            | LitPair LitVal LitVal
              deriving (Show, Read, Ord, Eq, Data, Typeable)

data Expr a = Expr !a (InExpr (Expr a)) deriving (Show, Read, Ord, Eq, Data, Typeable)
data InExpr e = Lit    LitVal
              | Ref    Ident
              | Appl   e [e]
              | If     e e e
              | Let    [(Ident, e)] e
              | LetRec [(Ident, e)] e
              | Lambda [Ident] (Maybe Ident) e
              | Begin  [e]
                deriving (Show, Read, Ord, Eq, Data, Typeable)

freeVars :: Expr a -> S.Set Ident
freeVars ast = snd $ execRWS (fv ast) S.empty ()
  where fv (Expr _ (Lit _))            = return ()
        fv (Expr _ (Ref r))            = do c <- asks $ S.member r
                                            when (not c) $ tell (S.singleton r)
        fv (Expr _ (Appl f args))      = fv f >> forM_ args fv
        fv (Expr _ (Lambda ids r bod)) = localWith (S.fromList $ params ids r) $ fv bod
        fv (Expr _ (Begin exp))        = forM_ exp fv
        fv (Expr _ (If cond cons alt)) = mapM_ fv [cond, cons, alt]
        fv (Expr _ (Let bnds bod))     = do forM_ bnds (fv . snd)
                                            localWith (S.fromList $ map fst bnds) $ fv bod
        fv (Expr _ (LetRec bnds bod))  = localWith (S.fromList $ map fst bnds) $
                                          do forM_ bnds (fv . snd)
                                             fv bod

        localWith ds = local (S.union ds)

ann :: Simple Lens (Expr a) a
ann op (Expr a e) = fmap (\a' -> Expr a' e) (op a)

isRefTo :: Ident -> Expr a -> Bool
isRefTo id (Expr _ (Ref r)) = id == r
isRefTo id       _          = False

isCallTo :: Ident -> Expr a -> Bool
isCallTo id (Expr _ (Appl c _)) | isRefTo id c = True
isCallTo id       _                            = False

params :: [Ident] -> Maybe Ident -> [Ident]
params ids r = ids ++ maybe [] return r
