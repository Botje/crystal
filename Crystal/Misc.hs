module Crystal.Misc where

import Control.Monad.Reader
import Crystal.Config

type Step a = Reader Config a
