{-#LANGUAGE TemplateHaskell #-}
module Crystal.Misc where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Writer
import Debug.Trace
import Data.Text.Lazy
import Data.Text.Format
import qualified Data.Map as M
import System.IO

import Crystal.AST
import Crystal.Pretty
import Crystal.Config

type StepResult = (String,Text)
type Step a = WriterT [StepResult] (ReaderT Config IO) a

spy :: Show a => Expr a -> Step (Expr a)
spy expr = trace (show expr) $ return expr

spyP :: Show a => Expr a -> Step (Expr a)
spyP expr = trace (pretty expr) $ return expr

report :: String -> Text -> Step ()
report header contents = tell [(header,contents)]

type Depth = Int
data MobilityInfo = MI {
  _bindDepths :: M.Map Ident Depth,
  _checkDepths :: M.Map Int (M.Map Ident Depth)
}

$(makeLenses ''MobilityInfo)
