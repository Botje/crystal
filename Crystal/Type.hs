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

data Type = TAny
          | TError
          | TVar TVar
          | TInt | TString | TBool | TSymbol | TVoid | TVec | TPair | TList | TNull | TChar | TPort | THash
          | Tor [Type]
          | TFun [TVar] Effect Type
          | TVarFun VarFun
          | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
          | TAppl Type [TypeNLabel]
          | TChain Type TVar TLabel Type
            deriving (Show, Eq, Ord, Data, Typeable)

data VarFun = VarFun { vfName  :: Ident,
                       vfLabel :: TLabel,
                       vfFun   :: [TypeNLabel] -> TLabel -> Type }
                 deriving (Data, Typeable)

isTFun (TFun _ _ _) = True
isTFun ____________ = False

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
concreteTypes = [TInt, TString, TBool, TSymbol, TVoid, TVec, TPair, TList, TNull, TChar, TPort, THash]

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
simplify tc@(TChain appl var lab rest) | rest' == rest = tc
                                       | otherwise     = TChain appl var lab rest'
  where rest' = simplify rest
simplify ta@(TAppl f args) =
  case f' of
    TFun _  _  _           -> apply f' args
    _            | f == f' -> ta -- preserve sharing
    _                      -> TAppl f' args
  where f' = simplify f
simplify t = t

apply :: Type -> [TypeNLabel] -> Type
apply (Tor ts) a_args                   = Tor $ map (flip apply a_args) ts
apply (TIf l t_t t_a t) a_args          = TIf l t_t t_a (apply t a_args)
apply vf@(TVarFun _) a_args             = expand (TAppl vf a_args)
apply t_f@(TFun t_args ef t_bod) a_args = expand (TAppl t_f a_args)
apply (TVar v) a_args                   = TAppl (TVar v) a_args
apply _ a_args                          = TError

applies :: Type -> [TypeNLabel] -> Bool
applies (TFun t_args _ t_bod) a_args = length t_args == length a_args  
applies _ _ = False


replace :: M.Map TVar TypeNLabel -> Type -> Type
replace env (TVar var) | Just (l :*: t) <- M.lookup var env = t
replace env (Tor ts) = Tor $ map (replace env) ts
replace env (TFun args ef bod) = TFun args ef $ replace (extendMany args (map (\v -> LVar v :*: TVar v) args) env) bod
replace env (TIf (l1,l2) t_1 t_2 t_3) = TIf (l1,l2') (replace env t_1) (replace env t_2) (replace env t_3)
  where l2' = case l2 of LVar tv | Just (l :*: t) <- M.lookup tv env -> l
                         x -> x
replace env (TAppl fun args) = apply (replace env fun) $ map inst args
  where inst (l :*: TVar tv) | Just (l' :*: t') <- M.lookup tv env = (l' :*: t')
        inst (l :*: t) = l :*: t
replace env (TChain t1 var lab t2) = expand (TChain (replace env t1) var lab (replace env t2))
replace env x = x
expand :: Type -> Type
expand = transform expand'
  where
    expand' (TAppl t_f@(TFun t_args _ t_bod) a_args) 
     | applies t_f a_args = expand $ replace (M.fromList $ zip t_args a_args) t_bod
     | otherwise          = TError
    expand' (TAppl (TVarFun (VarFun _ lab vf)) a_args) = vf a_args lab
    expand' typ@(TChain appl var lab body) =
      case appl of
           TIf labs tst tgt appl' -> TIf labs tst tgt $ expand' (TChain appl' var lab body)
           TAppl (TVar _) _       -> typ
           _                      -> chainWith (\t -> replace (M.singleton var (lab :*: t)) body) appl
     where applied = simplify appl
           tl = lab :*: applied
    expand' typ = typ

expandOr :: Type -> [Type]
expandOr (Tor xs) = xs
expandOr t = [t]

trivialIf :: Type -> Bool
trivialIf (TIf _ (TFun args_1 _ TAny) (TFun args_2 _ _) _) = length args_1 == length args_2
trivialIf (TIf _ (TFun _ _ _) (TVarFun _) _) = True
trivialIf (TIf _ TPair TList _) = True
trivialIf (TIf _ x y _) | x == y = True
trivialIf _ = False

chain :: Type -> Type -> Type
chain t1 t2 = chainWith (const t2) t1

chainWith :: (Type -> Type) -> Type -> Type
chainWith f t1 = go t1
  where go (Tor ts) = Tor $ map go ts
        go (TIf (blame, cause) t_t t_1 t) 
          = TIf (blame, cause) t_t t_1 $ go t
        go (TChain t var lab t2) = TChain t var lab $ chainWith f t2
        go t = f t

extendMany :: Ord k => [k] -> [v] -> M.Map k v -> M.Map k v
extendMany keys vals env = M.fromList (zip keys vals) `M.union` env
