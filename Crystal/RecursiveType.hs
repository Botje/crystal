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

type Env = M.Map Int T
type Head = (Int, [T])
type HeadsMap = M.Map Head (Maybe T)


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
