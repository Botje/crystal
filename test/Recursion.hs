{-#LANGUAGE DeriveDataTypeable #-}
module Main where

import Control.Arrow (second)
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

data T = Tint | Tstring
       | Tor T T
       | Ttest T T T
       | Tapply Int [T]
       | Tvar Int
       | Tlambda [Int] T
       | Tbottom
       | Tunfold Int [T]
         deriving (Data, Typeable, Eq, Ord)

isTvar (Tvar _) = True
isTvar ________ = False

cases = [case1, case2, case3, case4, case5]

case1 = Mutual 1 [(-1, Tlambda [1,2] $ Tor Tint $ Tapply (-1) [Tint,Tint])]
case2 = Mutual 1 [(-1, Tlambda [1,2] $ Tapply (-1) [Tvar 1, Tvar 2])]
case3 = Mutual 1 [(-1, Tlambda [1,2,3] $ Tor (Tvar 1) (Tapply (-1) [Tvar 2, Tvar 3, Tvar 1]))]
case4 = Mutual 1 [(-1, Tlambda [1] $ Tor (Ttest Tstring (Tvar 1) Tstring) (Tor (Tapply (-1) [Tvar 1]) (Ttest Tint (Tvar 1) Tint)))]
case5 = Mutual 1 [(-1, Tlambda [1] $ Tor Tint (Ttest Tint (Tvar 1) (Tapply (-1) [Tint])))]

type Env = M.Map Int T
type Head = (Int, [T])
type HeadsMap = M.Map Head (Maybe T)

doit [(id, fun@(Tlambda vars t))] = [(id, solved)]
  where start = fun
        solved = solve $ iterate (visit env args) start !! 10
        env = M.singleton id fun
        args = map Tvar $ zipWith const [1..] vars

solve :: T -> T
solve fun = truncated
  where truncated = paths $ bottoms fun
        bottoms fun = transform f fun
          where f (Tunfold _ _) = Tbottom
                f (Tapply  _ _) = Tbottom
                f t             = t
        paths (Tlambda vars t) = if null result
                                    then Tlambda vars Tbottom
                                    else Tlambda vars $ foldr1 Tor result 
          where result = nub $ go t
                go (Tlambda vars t) = [Tlambda vars t]
                go (Tor t1 t2)      = go t1 ++ go t2
                go (Ttest t1 t2 t)  = map (Ttest t1 t2) $ go t
                go Tbottom          = []
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
        go (Tvar _:vs) id = Tvar id : go vs (id+1)
        go (v:vs) id      = v : go vs id

visit :: Env -> [T] -> T -> T
visit env args fun@(Tlambda vars t) =
  runReader (Tlambda vars <$> go t) $ (env `M.union` M.fromList (zip vars args))
  where go :: T -> Reader Env T
        go Tbottom = return Tbottom
        go Tint = return Tint
        go Tstring = return Tstring
        go (Tor t1 t2) = Tor <$> go t1 <*> go t2
        go (Tvar tv) = fromJust <$> asks (M.lookup tv)
        go (Tapply f vals) = do vals' <- mapM go vals
                                return $ Tunfold f vals'
        go (Tunfold f vals) = do vals' <- mapM go vals
                                 fun' <- go (Tvar f)
                                 go $ apply (zip vars vals') fun'
        go (Ttest t1 t2' t) = go t2' >>= \t2 ->
          case (t1, t2) of
            _  | t1 == t2   -> go t
            (Tint, Tstring) -> return Tbottom
            (Tstring, Tint) -> return Tbottom
            (_, Tvar tv) -> do tx <- asks (M.lookup tv)
                               case tx of
                                    Nothing -> do t' <- local (M.insert tv t1) $ go t
                                                  return $ Ttest t1 t2 t'
                                    Just ty | ty == t1  -> go t
                                            | isTvar ty -> Ttest t1 t2 <$> go t
                                            | otherwise -> return Tbottom

testTypes = iterate (\l -> map (Tint:) l ++ map (Tstring:) l) [[]]


prop_single_rec mut@(Mutual n ~[fun]) = n == 1 ==> all (\vs -> resSet vs [fun] == resSet vs [fun']) (testTypes !! length args)
  where Mutual _ [fun'] = solveMutual mut
        Tlambda args _ = snd fun


resSet vals [(id, fun@(Tlambda vars _))] = S.delete Tbottom results
  where results = evalState (go $ Tapply id vals) S.empty
        env = M.singleton id fun
        go :: T -> State (S.Set (Int, [T])) (S.Set T)
        go (Tor t1 t2) = liftM2 S.union (go t1) (go t2)
        go (Ttest t1 t2 t) | t1 == t2  = go t
                           | otherwise = return $ S.singleton Tbottom
        go (Tapply f vals) = do present <- gets (S.member (f, vals))
                                if present
                                   then return S.empty
                                   else do modify (S.insert (f, vals))
                                           let Just fun@(Tlambda vars _) = M.lookup f env
                                           go $ apply (zip vars vals) fun
        go (t) = return $ S.singleton t

braid :: [Int] -> S.Set T -> T
braid vars result = if S.null result
                       then Tlambda vars Tbottom
                       else Tlambda vars $ foldr1 Tor $ S.elems result 

unbraid :: T -> S.Set T
unbraid (Tor t1 t2) = S.union (unbraid t1) (unbraid t2)
unbraid (Ttest t1 t2 t) | t1 == t2  = unbraid t
                        | isTvar t2 = S.map (Ttest t1 t2) $ unbraid t
                        | otherwise = S.empty
unbraid t = S.singleton t

unLambda (Tlambda _ bod) = bod

canon :: T -> T
canon t = descend [] t
  where descend env (Ttest t1 t2 t)
          | t1 == t2 = descend env t
          | all (`elem` [Tint, Tstring]) [t1, t2] = Tbottom
          | otherwise = let Tvar tv = t2 in descend ((t1,t2):env) $ subst [(tv, t1)] t
        descend env t = foldr (\(t1,t2) rest -> Ttest t1 t2 rest) t $ sortBy (compare `on` snd) env
          
          

splitThread :: T -> (T -> T, T)
splitThread (Ttest t1 t2 t) = (Ttest t1 t2 . prefix', apply)
  where (prefix', apply) = splitThread t
splitThread t = (id, t)

solveMutual (Mutual n funs) = Mutual n $ map solve' funs
  where unbraidedFuns = M.fromList $ map (second (unbraid . unLambda)) funs
        solve' (id, fun@(Tlambda args body)) = (id, finalType)
          where finalType = braid args $ evalState (loop $ S.singleton $ Tapply id (map Tvar args)) S.empty
                walk thread = do modify (S.insert thread)
                                 let (prefix, Tapply id args) = splitThread thread
                                 case M.lookup id unbraidedFuns of
                                      Nothing      -> return $ S.singleton thread
                                      Just threads -> return $ S.map (canon . prefix . subst (zip [1..] args)) threads
                loop :: S.Set T -> State (S.Set T) (S.Set T)
                loop s = do seen <- get
                            let (applies, concrete) = S.partition (isApply . head . leaves) s
                            let (seenApplies, todoApplies) = S.partition (`S.member` seen) applies
                            if S.null todoApplies
                               then return $ concrete
                               else do expanded <- S.unions <$> mapM walk (S.elems todoApplies)
                                       loop (expanded `S.union` concrete)

isApply (Tapply _ _) = True
isApply ____________ = False

apply :: [(Int, T)] -> T -> T
apply m fun@(Tlambda _ body) = subst m body 

subst :: [(Int, T)] -> T -> T
subst m body = transform (apply' m) body
  where apply' m (Tvar x) = maybe (Tvar x) id $ lookup x m
        apply' m t = t

simplify = transform f
  where f orig@(Ttest t1 t2 t) =
          case (t1, t2) of
            _  | t1 == t2   -> t
            (Tint, Tstring) -> Tbottom
            (Tstring, Tint) -> Tbottom
            _               -> orig
        f orig = orig


instance Show T where
  showsPrec d Tint = showString "int"
  showsPrec d Tstring = showString "string"
  showsPrec d (Tvar i) | i > 0 = showString (return (['a'..'z'] !! (i-1)))
  showsPrec d Tbottom = showString "⊥"
  showsPrec d (Tor t1 t2) =
    showParen True $
      showString "or " .
      showsPrec (d+1) t1 .
      showString " " .
      showsPrec (d+1) t2
  showsPrec d (Ttest t1 t2 t) =
    showParen (d > 0) $
      showParen True ( showsPrec (d+1) t1 
                     . showString " ~ "
                     . showsPrec (d+1) t2) .
      showString ". " . 
      showsPrec (d+1) t
  showsPrec d (Tunfold f ts) = showsPrec d (Tapply f ts)
  showsPrec d (Tapply f ts) = 
    showParen True $
      (['A'..'Z'] !! abs (f+1) :) .
      showString " " .
      foldr1 (\a rest -> a . showString " " . rest) (map (showsPrec (d+1)) ts)
  showsPrec d (Tlambda vars t) =
    showParen (d > 0) $
      showString "Pi " . 
      showParen True (foldr1 (\a rest -> a . showString " " . rest) (map (shows . Tvar) vars)) .
      showString " " . 
      showsPrec (d+1) t

data Mutual = Mutual Int [(Int, T)] deriving (Data, Typeable, Eq, Ord, Show)

instance Arbitrary Mutual where
  arbitrary = sized mutualGenT
  shrink = const []

mutualGenT n = do numFuncs <- choose (1,3)
                  let names = map negate [1..numFuncs]
                  funcs <- replicateM numFuncs (genFunc n names) `suchThat` allCalled names
                  return $ Mutual numFuncs (zip names funcs)

allCalled names funcs = sort names == sort (nub [ n | Tapply n _ <- concatMap leaves funcs ])

genFunc n names = choose (1,3) >>= \args -> Tlambda [1..args] <$> genT names args n

leaves :: T -> [T]
leaves (Tor a b) = leaves a ++ leaves b
leaves (Ttest _ _ t) = leaves t
leaves (Tlambda _ t) = leaves t
leaves t = [t]

genT names args n = case n of
                   0 -> leaf
                   _ -> node n 
  where tvar = Tvar <$> choose (1,args)
        ground = elements [Tint, Tstring]
        node n = oneof nodes
          where n_1 = n - 1
                nodes = [leaf,
                         liftM2 Tor (genT names args n_1) (genT names args n_1),
                         Ttest <$> ground <*> tvar <*> genT names args n_1]
        leaf = frequency leaves
          where leaves = leaves' ++ [(2, Tapply <$> elements names <*> replicateM args (frequency leaves'))]
                leaves' = [
                  (2, ground),
                  (2, tvar)
                  ]

main = do quickCheckWith stdArgs{maxSize=5, maxSuccess=100000} prop_single_rec
          --quickCheckWith stdArgs{maxSize=5, maxSuccess=1000} prop_mutual_rec
