{-#LANGUAGE DeriveDataTypeable #-}
module Crystal.RecursiveType 
(solveLetrec) where

import Control.Arrow (second)
import Control.Lens (_1, _2, _3, mapped, (^.), (.~), (&), view, to, (%~))
import Control.Lens.TH
import Data.List
import Data.Function
import Debug.Trace
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics
import Data.Generics.Uniplate.Operations

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Test.QuickCheck
import Text.Show
import Text.PrettyPrint

import Crystal.Tuple
import Crystal.Type

debugging = False

traced f x | debugging = trace (f x) x
traced f x | otherwise = x

solveLetrec :: [(TVar, Type)] -> [(TVar, Type)]
solveLetrec tts' = traced (\_ -> "Input: " ++ show tts) $
                     traced (\out -> "Output: " ++ show out) $ 
                       go 0 [ (tv, TFun vars ef TError) | (tv, TFun vars ef _) <- tts ]
  where tts = map (second (simplifyPlus True . approximate allowed)) tts'
        allowed = S.fromList $ map fst tts
        go n expns = let expns' = [ (tv, simplifyPlus True ex')
                                  | (tv, tt) <- tts
                                  , let ex' = fillIn tt expns]
                     in if expns == expns'
                           then expns'
                           else go (n+1) $ traced (\out -> "Iter " ++ show n ++ ": " ++ show out) expns'
        fillIn tt expns = replace (M.fromList [ (v, LSyn :*: t) | (v,t) <- expns]) tt

approximate :: S.Set TVar -> Type -> Type
approximate allowed = transform f
  where f (TChain (TAppl (TVar tv) args) res lab body)
          | tv `S.notMember` allowed = expand (TChain TAny res lab body)
        f x                          = x
