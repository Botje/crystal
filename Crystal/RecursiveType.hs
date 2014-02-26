{-#LANGUAGE DeriveDataTypeable #-}
module Crystal.RecursiveType (solveLetrec) where

import Control.Arrow (second)
import Control.Lens (_2, (^.))
import Data.List
import Data.Function
import Debug.Trace
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics
import Data.Generics.Uniplate.Data

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Test.QuickCheck
import Text.Show

import Crystal.Tuple
import Crystal.Type

-- TODO: remove
type T = Type

-- data T = TInt | TString
--        | Tor T T
--        | TIf T T T
--        | TAppl Int [T]
--        | Tvar Int
--        | TFun [Int] T
--        | TError
--        | TUnfold Int [T]
--          deriving (Data, Typeable, Eq, Ord)

-- data Type = TInt | TString | TBool | TSymbol | TVoid | TVec | TPair | TNull | TChar
--           | Tor [Type]
--           | TVar TVar
--           | TFun [TVar] Type
--           | TVarFun VarFun
--           | TIf (TLabel,TLabel) Type Type Type -- labels: blame & cause
--           | TAppl Type [TypedLabel]
--           | TUnfold Type [TypedLabel]
--           | TError
--           | TAny
--             deriving (Show, Eq, Data, Typeable)

type Env = M.Map Int T
type Head = (Int, [T])
type HeadsMap = M.Map Head (Maybe T)

doit [(id, fun@(TFun vars t))] = [(id, solved)]
  where start = fun
        solved = solve $ iterate (visit env args) start !! 10
        env = M.singleton id fun
        args = map TVar $ zipWith const [1..] vars

solve :: T -> T
solve fun = truncated
  where truncated = paths $ bottoms fun
        bottoms fun = transform f fun
          where f (TUnfold _ _) = TError
                f (TAppl  _ _) = TError
                f t             = t
        paths (TFun vars t) = if null result
                                    then TFun vars TError
                                    else TFun vars $ Tor result 
          where result = nub $ go t
                go (TFun vars t) = [TFun vars t]
                go (Tor ts)      = concatMap go ts
                go (TIf ls t1 t2 t)  = map (TIf ls t1 t2) $ go t
                go TError          = []
                go t                = [t]





tag :: Head -> State HeadsMap ()
tag id' = do present <- gets (M.lookup id)
             when (isNothing present) $
               modify (M.insert id Nothing)
  where id = second canonHead id'

complete :: Head -> T -> State HeadsMap ()
complete id tree = modify $ M.insert (second canonHead id) (Just tree)

canonHead :: [T] -> [T]
canonHead vs = go vs 1
  where go [] _           = []
        go (TVar _:vs) id = TVar id : go vs (id+1)
        go (v:vs) id      = v : go vs id

visit :: Env -> [T] -> T -> T
visit env args fun@(TFun vars t) =
  runReader (TFun vars <$> go t) $ (env `M.union` M.fromList (zip vars args))
  where go :: T -> Reader Env T
        go TError = return TError
        go t | t `elem` concreteTypes = return t
        go (Tor ts) = Tor <$> mapM go ts
        go (TVar tv) = fromJust <$> asks (M.lookup tv)
        go (TAppl f vals) = do vals' <- mapM (go . (^. _2)) vals
                               return $ TUnfold f $ zipWith (:*:) (repeat LSyn) vals' -- FIXME
        go (TUnfold f vals) = do vals' <- mapM (go . (^. _2)) vals
                                 fun' <- go f
                                 go $ apply (zip vars vals') fun'
        go (TIf ls t1 t2' t) = go t2' >>= \t2 ->
          case (t1, t2) of
            _  | t1 == t2   -> go t
            _  | all (`elem` concreteTypes) [t1, t2] -> return TError
            (_, TVar tv) -> do tx <- asks (M.lookup tv)
                               case tx of
                                    Nothing -> do t' <- local (M.insert tv t1) $ go t
                                                  return $ TIf ls t1 t2 t'
                                    Just ty | ty == t1  -> go t
                                            | isTVar ty -> TIf ls t1 t2 <$> go t
                                            | otherwise -> return TError

braid :: [Int] -> S.Set T -> T
braid vars result = if S.null result
                       then TFun vars TError
                       else TFun vars $ Tor $ S.elems result 

unbraid :: T -> S.Set T
unbraid (Tor ts) = S.unions $ map unbraid ts
unbraid (TIf ls t1 t2 t) | t1 == t2  = unbraid t
                           | isTVar t2 = S.map (TIf ls t1 t2) $ unbraid t
                           | otherwise = S.empty
unbraid t = S.singleton t

unLambda (TFun _ bod) = bod

canon :: T -> T
canon t = descend [] t
  where descend env (TIf ls t1 t2 t)
          | t1 == t2 = descend env t
          | all (`elem` [TInt, TString]) [t1, t2] = TError
          | otherwise = let TVar tv = t2 in descend ((t1,ls,t2):env) $ subst [(tv, t1)] t
        descend env t = foldr (\(t1,ls,t2) rest -> TIf ls t1 t2 rest) t $ sortBy (compare `on` (^. _2)) env
          
          

splitThread :: T -> (T -> T, T)
splitThread (TIf ls t1 t2 t) = (TIf ls t1 t2 . prefix', apply)
  where (prefix', apply) = splitThread t
splitThread t = (id, t)

data Mutual = Mutual Int [(TVar, T)] deriving (Data, Typeable, Eq, Show)

solveLetrec :: [TVar] -> [Type] -> [Type]
solveLetrec vars types = map snd solved
  where mut = Mutual (length types) $ zip vars types
        Mutual _ solved = solveMutual mut


solveMutual :: Mutual -> Mutual
solveMutual (Mutual n funs) = Mutual n $ map solve' funs
  where unbraidedFuns = M.fromList $ map (second (unbraid . unLambda)) funs
        solve' :: (Int, T) -> (Int, T)
        solve' (id, fun@(TFun args body)) = (id, finalType)
          where finalType = braid args $ evalState (loop $ S.singleton $ TAppl (TVar id) (map var args)) S.empty
                var l = LVar l :*: TVar l
                walk thread = do modify (S.insert thread)
                                 let (prefix, TAppl (TVar id) args) = splitThread thread
                                 case M.lookup id unbraidedFuns of
                                      Nothing      -> return $ S.singleton thread
                                      Just threads -> return $ S.map (canon . prefix . subst (zip [1..] (map (^. _2) args))) threads
                loop :: S.Set T -> State (S.Set T) (S.Set T)
                loop s = do seen <- get
                            let (applies, concrete) = S.partition (isApply . head . typeLeafs) s
                            let (seenApplies, todoApplies) = S.partition (`S.member` seen) applies
                            if S.null todoApplies
                               then return $ concrete
                               else do expanded <- S.unions <$> mapM walk (S.elems todoApplies)
                                       loop (expanded `S.union` concrete)

apply :: [(Int, T)] -> T -> T
apply m fun@(TFun _ body) = subst m body 

subst :: [(Int, T)] -> T -> T
subst m body = transform (apply' m) body
  where apply' m (TVar x) = maybe (TVar x) id $ lookup x m
        apply' m t = t

simplify = transform f
  where f orig@(TIf ls t1 t2 t) =
          case (t1, t2) of
            _  | t1 == t2   -> t
            (TInt, TString) -> TError
            (TString, TInt) -> TError
            _               -> orig
        f orig = orig


typeLeafs :: T -> [T]
typeLeafs (Tor ts) = concatMap typeLeafs ts
typeLeafs (TIf _ _ _ t) = typeLeafs t
typeLeafs (TFun _ t) = typeLeafs t
typeLeafs t = [t]
