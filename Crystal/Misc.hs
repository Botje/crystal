module Crystal.Misc where

import Control.Monad.Reader
import Control.Monad.Writer
import Debug.Trace
import Data.Text.Lazy

import Crystal.AST
import Crystal.Pretty
import Crystal.Config

type StepResult = (String,Text)
type Step a = WriterT [StepResult] (Reader Config) a

spy :: Show a => Expr a -> Step (Expr a)
spy expr = trace (show expr) $ return expr

spyP :: Show a => Expr a -> Step (Expr a)
spyP expr = trace (pretty expr) $ return expr

report :: String -> Text -> Step ()
report header contents = tell [(header,contents)]
