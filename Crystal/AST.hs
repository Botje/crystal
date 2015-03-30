{-# LANGUAGE DeriveDataTypeable, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
module Crystal.AST where

import Control.Lens hiding (plate)

import Data.Generics
import Data.Generics.Uniplate.Direct

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

instance Uniplate LitVal where
  uniplate (LitChar   c)     = plate (LitChar   c)
  uniplate (LitString s)     = plate (LitString s)
  uniplate (LitInt    i)     = plate (LitInt    i)
  uniplate (LitFloat  d)     = plate (LitFloat  d)
  uniplate (LitBool   b)     = plate (LitBool   b)
  uniplate (LitSymbol s)     = plate (LitSymbol s)
  uniplate (LitVoid)         = plate (LitVoid)
  uniplate (LitList lvs)     = plate LitList ||* lvs
  uniplate (LitPair one two) = plate LitPair |* one |* two

instance Biplate LitVal LitVal where
  biplate = plateSelf

instance Uniplate (Expr a) where
  uniplate (Expr a ie) = plate Expr |- a |+ ie

instance Biplate (Expr a) (Expr a) where
  biplate = plateSelf

instance Uniplate (InExpr (Expr a)) where
  uniplate (Lit    lv)            = plate (Lit    lv)
  uniplate (Ref    r)             = plate (Ref    r)
  uniplate (Appl   op args)       = plate Appl   |+ op ||+ args
  uniplate (If     cond cons alt) = plate If     |+ cond |+ cons |+ alt
  uniplate (Let    bnds bod)      = plate Let    ||+ bnds |+ bod
  uniplate (LetRec bnds bod)      = plate LetRec ||+ bnds |+ bod
  uniplate (Lambda ids r bod)     = plate Lambda |- ids |- r |+ bod
  uniplate (Begin  es)            = plate Begin  ||+ es

instance Biplate (InExpr (Expr a)) (InExpr (Expr a)) where
  biplate = plateSelf

instance Biplate (Expr a) (InExpr (Expr a)) where
  biplate (Expr a ie) = plate Expr |- a |* ie

instance Biplate (InExpr (Expr a)) (Expr a) where
  biplate (Lit    lv)            = plate (Lit    lv)
  biplate (Ref    r)             = plate (Ref    r)
  biplate (Appl   op args)       = plate Appl   |* op ||* args
  biplate (If     cond cons alt) = plate If     |* cond |* cons |* alt
  biplate (Let    bnds bod)      = plate Let    ||+ bnds |* bod
  biplate (LetRec bnds bod)      = plate LetRec ||+ bnds |* bod
  biplate (Lambda ids r bod)     = plate Lambda |- ids |- r |* bod
  biplate (Begin  es)            = plate Begin  ||* es

instance Biplate (Ident, Expr a) (InExpr (Expr a)) where
  biplate (i, e) = plate (,) |- i |+ e

instance Biplate (Ident, Expr a) (Expr a) where
  biplate (i, e) = plate (,) |- i |* e

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
