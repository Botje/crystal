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
import Data.Generics.Uniplate.Data

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Test.QuickCheck
import Text.Show
import Text.PrettyPrint

import Crystal.Trace
import Crystal.Tuple
import Crystal.Type

debugging = True

traced f x | debugging = trace (f x) x
traced f x | otherwise = x

solveLetrec :: [(TVar, Type)] -> [(TVar, Type)]
solveLetrec tts = traced (\_ -> "Input: " ++ show tts) $
                    traced (\out -> "Output: " ++ show out) $ return
  where go n expns = let expns' = [ (tv, simplifyPlus True ex')
                                  | (tv, tt) <- tts
                                  , let ex' = fillIn tt expns]
                     in if expns == expns'
                           then expns'
                           else go (n+1) $ traced (\out -> "Iter " ++ show n ++ ": " ++ show out) expns'
        fillIn tt expns = replace (M.fromList [ (v, LSyn :*: t) | (v,t) <- expns]) tt
        return = go 0 [ (tv, TFun vars ef TError) | (tv, TFun vars ef _) <- tts ]
