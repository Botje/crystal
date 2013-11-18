{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable #-}
{-#LANGUAGE PatternGuards, FlexibleInstances, MultiParamTypeClasses #-}
module Crystal.Tuple where

import Control.Lens
import Data.Generics

data a :*: b = a :*: b deriving (Show, Eq, Ord, Data, Typeable)
infix 8 :*:

instance Field1 (a :*: b) (a' :*: b) a a' where
  _1 k (a :*: b) = indexed k (0 :: Int) a <&> \a' -> (a' :*: b)

instance Field2 (a :*: b) (a :*: b') b b' where
  _2 k (a :*: b) = indexed k (1 :: Int) b <&> \b' -> (a :*: b')
