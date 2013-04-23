module Crystal.Seq where

import Control.Monad.State

data Seq = Seq String Int

instance Show Seq where
  show (Seq s i) = s ++ show i

instance Enum Seq where
  succ (Seq s i) = Seq s $ succ i
  pred (Seq s i) = Seq s $ pred i
  toEnum i = Seq "" i
  fromEnum (Seq s i) = i

nextSeq :: (Show s, Enum s, MonadState s m) => m String
nextSeq = do s <- get
             put (succ s)
             return $ show s

next :: (Show s, Enum s, MonadState s m) => String -> m String
next pre = do s <- get
              put (succ s)
              return (pre ++ show s)
