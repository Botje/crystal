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

import Crystal.AST
import Crystal.Tuple
import Crystal.Type

cases = [case1, case2, case3, case4, case5]
  where
    case1 = Mutual 1 [(-1, TFun [1,2] $ Tor [TInt, TAppl (TVar (-1)) [LSyn :*: TInt, LSyn :*: TInt]])]
    case2 = Mutual 1 [(-1, TFun [1,2] $ TAppl (TVar (-1)) [var 1, var 2])]
    case3 = Mutual 1 [(-1, TFun [1,2,3] $ Tor [TVar 1, TAppl (TVar (-1)) [var 2, var 3, var 1]])]
    case4 = Mutual 1 [(-1, TFun [1] $ Tor [TIf (LSyn, LSyn) TString (TVar 1) TString, TAppl (TVar (-1)) [var 1], TIf (LSyn, LSyn) TInt (TVar 1) TInt])]
    case5 = Mutual 1 [(-1, TFun [1] $ Tor [TInt, TIf (LSyn, LSyn) TInt (TVar 1) (TAppl (TVar (-1)) [LSyn :*: TInt])])]
    var l = LVar l :*: TVar l


genT names args n = case n of
                   0 -> leaf
                   _ -> node n 
  where tvar = TVar <$> choose (1,args)
        ground = elements [TInt, TString]
        node n = oneof nodes
          where n_1 = n - 1
                nodes = [leaf,
                         liftM2 Tor (genT names args n_1) (genT names args n_1),
                         TIf (LSyn, LSyn) <$> ground <*> tvar <*> genT names args n_1]
        leaf = frequency leaves
          where leaves = leaves' ++ [(2, TAppl <$> elements names <*> replicateM args (frequency leaves'))]
                leaves' = [
                  (2, ground),
                  (2, tvar)
                  ]

main = do quickCheckWith stdArgs{maxSize=5, maxSuccess=100000} prop_single_rec

prop_single_rec mut@(Mutual n ~[fun]) = n == 1 ==> all (\vs -> resSet vs [fun] == resSet vs [fun']) (testTypes !! length args)
  where Mutual _ [fun'] = solveMutual mut
        TFun args _ = snd fun

testTypes = iterate (\l -> map (TInt:) l ++ map (TString:) l) [[]]

resSet vals [(id, fun@(TFun vars _))] = S.delete TError results
  where results = evalState (go $ TAppl id vals) S.empty
        env = M.singleton id fun
        go :: T -> State (S.Set (Int, [T])) (S.Set T)
        go (Tor ts) = S.unions <$> mapM go ts
        go (TIf ls t1 t2 t) | t1 == t2  = go t
                              | otherwise = return $ S.singleton TError
        go (TAppl f' vals) = do let types = map (^. _2) vals
                                let TVar f = f'
                                present <- gets (S.member (f, types))
                                if present
                                   then return S.empty
                                   else do modify (S.insert (f, types))
                                           let Just fun@(TFun vars _) = M.lookup f env
                                           go $ apply (zip vars types) fun
        go (t) = return $ S.singleton t


instance Arbitrary Mutual where
  arbitrary = sized mutualGenT
  shrink = const []

mutualGenT n = do numFuncs <- choose (1,3)
                  let names = map negate [1..numFuncs]
                  funcs <- replicateM numFuncs (genFunc n names) `suchThat` allCalled names
                  return $ Mutual numFuncs (zip names funcs)

allCalled names funcs = sort names == sort (nub [ n | TAppl n _ <- concatMap leaves funcs ])

genFunc n names = choose (1,3) >>= \args -> TFun [1..args] <$> genT names args n

-- instance Show T where
--   showsPrec d TInt = showString "int"
--   showsPrec d TString = showString "string"
--   showsPrec d (TVar i) | i > 0 = showString (return (['a'..'z'] !! (i-1)))
--   showsPrec d TError = showString "⊥"
--   showsPrec d (Tor t1 t2) =
--     showParen True $
--       showString "or " .
--       showsPrec (d+1) t1 .
--       showString " " .
--       showsPrec (d+1) t2
--   showsPrec d (TIf ls t1 t2 t) =
--     showParen (d > 0) $
--       showParen True ( showsPrec (d+1) t1 
--                      . showString " ~ "
--                      . showsPrec (d+1) t2) .
--       showString ". " . 
--       showsPrec (d+1) t
--   showsPrec d (TUnfold f ts) = showsPrec d (TAppl f ts)
--   showsPrec d (TAppl f ts) = 
--     showParen True $
--       (['A'..'Z'] !! abs (f+1) :) .
--       showString " " .
--       foldr1 (\a rest -> a . showString " " . rest) (map (showsPrec (d+1)) ts)
--   showsPrec d (TFun vars t) =
--     showParen (d > 0) $
--       showString "Pi " . 
--       showParen True (foldr1 (\a rest -> a . showString " " . rest) (map (shows . TVar) vars)) .
--       showString " " . 
--       showsPrec (d+1) t
