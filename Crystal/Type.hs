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

effectToList :: Effect -> [Ident]
effectToList = S.toList

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

data Type = TInt | TString | TBool | TSymbol | TVoid | TVec | TPair | TList | TNull | TChar | TPort
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
isApply ___________ = False


instance Eq VarFun where
  (==) = (==) `on` vfName

instance Ord VarFun where
  compare = compare `on` vfName

instance Show VarFun where
  showsPrec _ vf s = "<function " ++ (show $ vfLabel vf) ++ ">" ++ s

concreteTypes :: [Type]
concreteTypes = [TInt, TString, TBool, TSymbol, TVoid, TVec, TPair, TList, TNull, TChar, TPort]

simplify :: Type -> Type
simplify tor@(Tor ts) | length ts' == 1 = head ts'
                      | ts == ts'       = tor -- preserve sharing
                      | otherwise       = Tor ts'
  where ts' = nub $ concatMap (expandOr . simplify) ts
simplify tf@(TFun args ef body) | body == simplified = tf -- preserve sharing
                                | otherwise          = TFun args ef simplified
  where simplified = simplify body
simplify tif@(TIf l t_1 t_2 t) | trivialIf tif     = t'
                               | tif == simplified = tif -- preserve sharing
                               | otherwise         = simplified
  where (t_1', t_2', t') = (simplify t_1, simplify t_2, simplify t)
        simplified = TIf l t_1 t_2' t'
simplify t = t

expandOr :: Type -> [Type]
expandOr (Tor xs) = xs
expandOr t = [t]

trivialIf :: Type -> Bool
trivialIf (TIf _ (TFun args_1 _ TAny) (TFun args_2 _ _) _) = length args_1 == length args_2
trivialIf (TIf _ (TFun _ _ _) (TVarFun _) _) = True
trivialIf (TIf _ TPair TList _) = True
trivialIf (TIf _ x y _) | x == y = True
trivialIf _ = False
