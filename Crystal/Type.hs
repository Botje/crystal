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
import qualified Data.Set as S

import Crystal.AST
import Crystal.Seq
import Crystal.Tuple

type TVar = Int

freshTVar :: (MonadState TVar m) => m TVar
freshTVar = nextSeq

data TLabel = LSource Label
            | LPrim Ident
            | LVar TVar
            | LSyn
              deriving (Show, Eq, Ord, Data, Typeable)

type Effect = S.Set Ident

emptyEffect :: Effect
emptyEffect = S.empty

varInEffect :: Ident -> Effect -> Bool
varInEffect = S.member

effectSingleton :: Ident -> Effect
effectSingleton = S.singleton

effectFromList :: [Ident] -> Effect
effectFromList = S.fromList

type TypedLabel = TLabel :*: (Type :*: Effect)
type TypeNLabel = TLabel :*: Type

getLabel :: Expr TypedLabel -> TLabel
getLabel (Expr (l :*: _) _) = l

getType :: Expr TypedLabel -> Type
getType (Expr (_ :*: t :*: _) _) = t

getEffect :: Expr TypedLabel -> Effect
getEffect (Expr (_ :*: _ :*: ef) _) = ef

getTypeAndLabel :: Expr TypedLabel -> TypeNLabel
getTypeAndLabel (Expr (t :*: l :*: _) _) = t :*: l

data Type = TInt | TString | TBool | TSymbol | TVoid | TVec | TPair | TNull | TChar
          | Tor [Type]
          | TVar TVar
          | TFun [TVar] Effect Type
          | TVarFun VarFun
          | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
          | TAppl Type [TypeNLabel]
          | TUnfold Type [TypeNLabel]
          | TError
          | TAny
            deriving (Show, Eq, Ord, Data, Typeable)

data VarFun = VarFun { vfName  :: Ident,
                       vfLabel :: TLabel,
                       vfFun   :: [TypeNLabel] -> TLabel -> Type }
                 deriving (Data, Typeable)

isTVar (TVar _) = True
isTVar ________ = False

isApply (TAppl _ _) = True
isApply ____________ = False


instance Eq VarFun where
  (==) = (==) `on` vfName

instance Ord VarFun where
  compare = compare `on` vfName

instance Show VarFun where
  showsPrec _ vf s = "<function " ++ (show $ vfLabel vf) ++ ">" ++ s

concreteTypes :: [Type]
concreteTypes = [TInt, TString, TBool, TSymbol, TVoid, TVec, TPair, TNull, TChar]
