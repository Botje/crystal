{-#LANGUAGE DeriveDataTypeable #-}
module Main where

import Control.Arrow (second)
import Data.List
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

case1 = Tlambda [1,2] $ Tor Tint $ Tapply 6 [Tint,Tint]
case2 = Tlambda [1,2] $ Tapply 6 [Tvar 1, Tvar 2]
case3 = Tlambda [1,2,3] $ Tor (Tvar 1) (Tapply 6 [Tvar 2, Tvar 3, Tvar 1])
case4 = Tlambda [1] $ Tor (Ttest Tstring (Tvar 1) Tstring) (Tor (Tapply 6 [Tvar 1]) (Ttest Tint (Tvar 1) Tint))
case5 = Tlambda [1] $ Tor Tint (Ttest Tint (Tvar 1) (Tapply 6 [Tint]))

type Env = M.Map Int T
type Head = (Int, [T])
type HeadsMap = M.Map Head (Maybe T)

doit fun@(Tlambda vars t) = solved
  where start = fun
        solved = solve $ iterate (visit env args) start !! 10
        env = M.singleton 6 fun
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



prop_foo (SelfAppT t) = 
  all (\vs -> resSet vs t == resSet vs t') $
    [ [Tint, Tint], 
      [Tint, Tstring],
      [Tstring, Tint],
      [Tstring, Tstring] ]
  where t' = doit t

resSet vals fun@(Tlambda vars _) = S.delete Tbottom results
  where results = evalState (go $ Tapply 6 vals) S.empty
        env = M.singleton 6 fun
        go :: T -> State (S.Set (Int, [T])) (S.Set T)
        go (Tor t1 t2) = liftM2 S.union (go t1) (go t2)
        go (Ttest t1 t2 t) | t1 == t2  = go t
                           | otherwise = return $ S.singleton Tbottom
        go (Tapply f vals) = do present <- gets (S.member (f, vals))
                                if present
                                   then return S.empty
                                   else do modify (S.insert (f,vals))
                                           let Just fun@(Tlambda vars _) = M.lookup f env
                                           go $ apply (zip vars vals) fun
        go (t) = return $ S.singleton t

apply :: [(Int, T)] -> T -> T
apply m fun@(Tlambda vars body) = transform (apply' m) body
  where apply' m (Tvar x) = fromJust $ lookup x m
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
  showsPrec d (Tvar i) = showString (return (['a'..'z'] !! (i-1)))
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
      showsPrec (d+1) (Tvar f) .
      showString " " .
      foldr1 (\a rest -> a . showString " " . rest) (map (showsPrec (d+1)) ts)
  showsPrec d (Tlambda vars t) =
    showParen (d > 0) $
      showString "Pi " . 
      showParen True (foldr1 (\a rest -> a . showString " " . rest) (map (shows . Tvar) vars)) .
      showString " " . 
      showsPrec (d+1) t

instance Arbitrary T where
  arbitrary = Tlambda [1,2] <$> sized genT
  shrink = shrinkT

newtype SelfAppT = SelfAppT { unSelfApp :: T } deriving (Data, Typeable, Eq, Ord, Show)

instance Arbitrary SelfAppT where
  arbitrary = SelfAppT <$> arbitrary
  shrink = map SelfAppT . shrink . unSelfApp

selfAppT = arbitrary `suchThat` (any isSelfApp . leaves)

leaves :: T -> [T]
leaves (Tor a b) = leaves a ++ leaves b
leaves (Ttest _ _ t) = leaves t
leaves (Tlambda _ t) = leaves t
leaves t = [t]

isSelfApp :: T -> Bool
isSelfApp (Tapply 6 _) = True
isSelfApp _            = False

shrinkT (Tor a b) = [a,b]
shrinkT (Ttest _ _ t) = [t]
shrinkT (Tlambda vs t) = [ Tlambda vs t' | t' <- shrink t]
shrinkT _ = []

genT 0 = leaf
genT n = node n 

node n = oneof nodes
  where n_1 = n - 1
        nodes = [leaf,
                 liftM2 Tor (genT n_1) (genT n_1),
                 Ttest <$> oneof [return Tint, return Tstring] <*> oneof [return (Tvar 1), return (Tvar 2)] <*> genT n_1]


leaf = frequency leaves
  where leaves = leaves' ++ [(2, Tapply 6 <$> mapM (\_ -> frequency leaves') [1,2])]
        leaves' = [
          (2, return Tint),
          (2, return Tstring),
          (2, Tvar <$> elements [1,2])
          ]

main = quickCheckWith stdArgs{maxSize=5, maxSuccess=100000} prop_foo
