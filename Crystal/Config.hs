{-#LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Crystal.Config where

import Control.Lens hiding (enum)
import Control.Lens.TH
import Data.Generics
import System.Console.CmdArgs.Implicit

data TSType = Dumb | Smart deriving (Show, Eq, Data, Typeable)

data Config =
  Config { _cfgTypeSys   :: TSType,
           _cfgInputFile :: String
         } deriving (Show, Eq, Data, Typeable)

$(makeLenses ''Config)

defaultArgs = Config { _cfgTypeSys   = enum [ Smart &= help "Smart type system", Dumb &= help "Dynamic type system" ],
                       _cfgInputFile = def &= args        &= typFile}
