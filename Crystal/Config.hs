{-#LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Crystal.Config where

import Control.Lens
import Control.Lens.TH
import Data.Generics
import System.Console.CmdArgs.Implicit

data Config =
  Config { _cfgTypeSys   :: String,
           _cfgInputFile :: String
         } deriving (Show, Eq, Data, Typeable)

$(makeLenses ''Config)

defaultArgs = Config { _cfgTypeSys   = def &= name "type" &= help "Type system (smart or dumb)" &= opt "smart",
                       _cfgInputFile = def &= args        &= typFile}
