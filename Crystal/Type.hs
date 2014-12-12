{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Type  where

import Control.Applicative
import Control.Lens hiding (transform)
import Control.Monad
import Data.Function
import Data.Generics
import Data.Generics.Biplate
import Data.List
import Data.Maybe
import Data.Monoid
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

isTor (Tor _) = True
isTor _______ = False

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

plus :: Maybe Type -> Type -> Maybe Type
plus mt t = mt `mplus` Just t

simplify :: Type -> Type
simplify = simplifyPlus False

simplifyWithBot :: Type -> Type
simplifyWithBot = simplifyPlus True

simplifyPlus :: Bool -> Type -> Type
simplifyPlus doBot t = maybe t id $ simp M.empty t
  where botAndJTE x = doBot && x == Just TError
        simp tested (Tor ts) =
          if changed
             then if 1 == length ts'
                     then Just $ head ts'
                     else Just $ Tor ts'
             else Nothing
          where (changed :*: _ :*: ts') = foldr f (False :*: seen1 :*: []) ts
                seen1 = if doBot then S.singleton TError else S.empty
                f t (changed :*: seen :*: ts) =
                  case simp tested t of
                    Nothing -> case t of
                                    Tor ts'                -> foldr f (True :*: seen :*: ts) ts'
                                    _  | t `S.member` seen -> (True :*: seen :*: ts)
                                    _                      -> (changed :*: (S.insert t seen) :*: (t:ts))
                    Just t' -> case t' of
                                    Tor ts'                 -> foldr f (True :*: seen :*: ts) ts'
                                    _  | t' `S.member` seen -> (True :*: seen :*: ts)
                                    _                       -> (True :*: (S.insert t' seen) :*: (t':ts))
        simp tested tf@(TFun args ef body) | isNothing body' = Nothing
                                           | otherwise       = liftA (TFun args ef) body'
          where body' = simp tested body
        simp tested (TIf l t_1 t_2 t) | botAndJTE t_2z = Just TError
                                      | trivialIf t_1 (fromJust t_2z) = simp tested t `plus` t
                                      | doBot && not (isTVar (fromJust t_2z)) = Just TError
                                      | botAndJTE t_z = Just TError
                                      | isNothing all = Nothing
                                      | otherwise     = liftA2 (TIf l t_1) t_2z t_z
          where (t_2', t') = (simp tested t_2, simp tested' t)
                (t_2z, t_z) = (t_2' `plus` t_2, t' `plus` t)
                all = t_2' `mplus` t'
                tested' = M.insert t_2 t_1 tested
        simp tested tc@(TChain appl var lab rest) | botAndJTE applz = Just TError
                                                  | isNothing all = Nothing
                                                  | otherwise     = liftA2 (\a r -> TChain a var lab r) applz restz
          where (appl', rest') = (simp tested appl, simp tested rest)
                all = appl' `mplus` rest'
                (applz, restz) = (appl' `plus` appl, rest' `plus` rest)
        simp tested ta@(TAppl f args) =
          case fz of
            TError | doBot    -> Just TError
            (TFun _ _ _)      -> Just $ apply fz argsz
            (TVarFun vf)      -> Just $ apply fz argsz
            _ | isNothing all -> Nothing
            _                 -> Just $ TAppl fz argsz
          where (f', args') = (simp tested f, map (simp tested . view _2) args)
                all = foldl' mplus f' args'
                (fz, argsz) = (maybe f id f', zipWith g args' args)
                g Nothing  tl = tl
                g (Just t) tl = tl & _2 .~ t
        simp tested t@(TVar tv) | doBot = M.lookup t tested
        simp tested t = Nothing

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
expand t = expand' t
  where
    expand' (TAppl t_f@(TFun t_args _ t_bod) a_args) 
     | applies t_f a_args = transform expand' $ replace (M.fromList $ zip t_args a_args) t_bod
     | otherwise          = TError
    expand' (TAppl (TVarFun (VarFun _ lab vf)) a_args) = vf a_args lab
    expand' typ@(TChain appl var lab body) =
      case appl of
           TIf labs tst tgt appl' -> TIf labs tst tgt $ expand' (TChain appl' var lab body)
           TAppl (TVar _) _       -> typ
           _                      -> chainWith (\t -> transform expand' $ replace (M.singleton var (lab :*: t)) body) $ expand' appl
     where applied = simplify appl
           tl = lab :*: applied
    expand' typ = typ

trivialIf :: Type -> Type -> Bool
trivialIf (TFun args_1 _ TAny) (TFun args_2 _ _) = length args_1 == length args_2
trivialIf (TFun _ _ _) (TVarFun _) = True
trivialIf TPair TList = True
trivialIf x y | x == y = True
trivialIf _ _ = False

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
