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


braid :: [Int] -> Effect -> S.Set T -> T
braid vars ef result = if S.null result
                          then TFun vars ef TError
                          else TFun vars ef $ Tor $ S.elems result 

unbraid :: T -> S.Set T
unbraid (Tor ts) = S.unions $ map unbraid ts
unbraid (TIf ls t1 t2 t) | t1 == t2  = unbraid t
                           | isTVar t2 = S.map (TIf ls t1 t2) $ unbraid t
                           | otherwise = S.empty
unbraid t = S.singleton t

getTFunEffect :: Type -> Effect
getTFunEffect (TFun _ ef _) = ef

getTFunBody :: Type -> Type
getTFunBody (TFun _ _ bod) = bod

canon :: T -> T
canon t = descend [] t
  where descend env (TIf ls t1 t2 t)
          | t1 == t2 = descend env t
          | all (`elem` [TInt, TString]) [t1, t2] = TError
          | otherwise = let TVar tv = t2 in descend ((t1,ls,t2):env) $ subst [(tv, t1)] t
        descend env t = foldr (\(t1,ls,t2) rest -> TIf ls t1 t2 rest) t $ sortBy (compare `on` (^. _2)) env
          
          

splitThread :: T -> (T -> T, T)
splitThread (TIf ls t1 t2 t) = (TIf ls t1 t2 . prefix', tip)
  where (prefix', tip) = splitThread t
splitThread t = (id, t)

data Mutual = Mutual [(TVar, T)] deriving (Data, Typeable, Eq, Show)

solveLetrec :: [TVar] -> [Type] -> [Type]
solveLetrec vars types = map snd solved
  where mut = Mutual $ zip vars types
        Mutual solved = solveMutual mut


solveMutual :: Mutual -> Mutual
solveMutual (Mutual funs) = Mutual $ map solve' funs
  where unbraidedFuns = M.fromList $ map (second (unbraid . getTFunBody)) funs
        funEffects    = M.fromList $ map (second getTFunEffect) funs
        solve' :: (Int, T) -> (Int, T)
        solve' (i, fun@(TFun args _ body)) = (i, finalType)
          where (finalPaths, finalEffect) = evalState (runWriterT $ loop $ S.singleton $ TAppl (TVar i) (map var args)) S.empty
                finalType = braid args finalEffect finalPaths
                var l = LVar l :*: TVar l
                walk thread = do modify (S.insert thread)
                                 let (prefix, tip) = splitThread thread
                                 case tip of 
                                      TAppl (TVar v) args ->
                                        do tell $ maybe emptyEffect id (M.lookup v funEffects)
                                           case M.lookup v unbraidedFuns of
                                                Nothing      -> return $ S.singleton thread
                                                Just threads ->
                                                  let threads' = S.map (subst (zip [1..] (map (^. _2) args))) threads
                                                  in return $ S.map (canon . prefix) threads'
                                      TAppl (TFun formals ef body) args ->
                                        do tell ef
                                           let body' = subst (zip formals $ map (^. _2) args) body
                                           return $ S.map (canon . prefix) $ unbraid body'
                loop :: S.Set T -> WriterT Effect (State (S.Set T)) (S.Set T)
                loop s = do seen <- get
                            let (applies, concrete) = S.partition (isApply . head . typeLeafs) s
                            let (seenApplies, todoApplies) = S.partition (`S.member` seen) applies
                            if S.null todoApplies
                               then return $ concrete
                               else do expanded <- S.unions <$> mapM walk (S.elems todoApplies)
                                       loop (expanded `S.union` concrete)

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
typeLeafs (TFun _ _ t) = typeLeafs t
typeLeafs t = [t]
