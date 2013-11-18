{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Type  where

import Control.Lens hiding (transform)
import Control.Monad
import Data.Function
import Data.Generics
import Data.Generics.Biplate
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M

import Crystal.AST
import Crystal.Seq
import Crystal.Tuple

type TVar = Int

freshTVar :: (MonadState TVar m) => m TVar
freshTVar = nextSeq

data TLabel = LSource Int
            | LPrim String
            | LVar TVar
            | LSyn
              deriving (Show, Eq, Data, Typeable)

type TypedLabel = TLabel :*: Type

getType :: Expr TypedLabel -> Type
getType (Expr (_ :*: t) _) = t

getLabel :: Expr TypedLabel -> TLabel
getLabel (Expr (l :*: _) _) = l

getTypeAndLabel :: Expr TypedLabel -> TypedLabel
getTypeAndLabel (Expr tl _) = tl

data Type = TInt | TString | TBool | TSymbol | TVoid | TVec | TPair | TNull | TChar
          | Tor [Type]
          | TVar TVar
          | TFun [TVar] Type
          | TVarFun VarFun
          | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
          | TAppl Type [TypedLabel]
          | TError
          | TAny
            deriving (Show, Eq, Data, Typeable)

data VarFun = VarFun { vfName  :: Ident,
                       vfLabel :: TLabel,
                       vfFun   :: [TypedLabel] -> TLabel -> Type }
                 deriving (Data, Typeable)


instance Eq VarFun where
  (==) = (==) `on` vfName

instance Show VarFun where
  showsPrec _ vf s = "<function " ++ (show $ vfLabel vf) ++ ">" ++ s
