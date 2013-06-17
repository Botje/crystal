{-#LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Crystal.Config where

import Control.Lens hiding (enum)
import Control.Lens.TH
import Data.Generics
import System.Console.CmdArgs.Implicit

data TSType = Dumb | Smart deriving (Show, Eq, Data, Typeable)

data Config =
  Config { _cfgTypeSys   :: TSType,
           _cfgInputFile :: String,
           _cfgCheckMobility :: Bool,
           _cfgMobilityStats :: Bool
         } deriving (Show, Eq, Data, Typeable)

$(makeLenses ''Config)

defaultArgs = Config { _cfgTypeSys   = enum [ Smart &= help "Smart type system" &= name "s", Dumb &= help "Dynamic type system" &= name "d" ]
                     , _cfgInputFile = def &= args &= typFile
                     , _cfgCheckMobility = enum [ True &= help "Test mobility (default)" &= name "mobility" &= explicit,
                                                  False &= help "Disable mobility" &= name "no-mobility" &= explicit ]
                     , _cfgMobilityStats = enum [ True &= help "Generate mobility stats (default)" &= name "stats" &= explicit,
                                                  False &= help "Disable stats generation" &= name "no-stats" &= explicit]
                     }
