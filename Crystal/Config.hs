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
           _cfgCheckSimplification :: Bool,
           _cfgMobilityStats :: Bool,
           _cfgDumpTypes :: Bool,
           _cfgDumpTree  :: Bool,
           _cfgDumpImmediately :: Bool,
           _cfgAnnotateLabels :: Bool
         } deriving (Show, Eq, Data, Typeable)

$(makeLenses ''Config)

defaultArgs = Config { _cfgTypeSys   = enum [ Smart &= help "Smart type system" &= name "S", Dumb &= help "Dynamic type system" &= name "D" ]
                     , _cfgInputFile = def &= args &= typFile
                     , _cfgCheckMobility = enum [ True &= help "Test mobility (default)" &= name "mobility" &= explicit,
                                                  False &= help "Disable mobility" &= name "no-mobility" &= explicit ]
                     , _cfgCheckSimplification = enum [ True &= help "Test simplification (default)" &= name "simplification" &= explicit,
                                                        False &= help "Disable simplification" &= name "no-simplification" &= explicit ]
                     , _cfgMobilityStats = enum [ False &= help "Don't generate mobility stats (default)" &= name "no-stats" &= explicit,
                                                  True &= help "Generate mobility stats" &= name "stats" &= explicit ]
                     , _cfgDumpTypes = enum [ False &= help "Don't dump top-level types (default)" &= name "no-types" &= explicit,
                                              True  &= help "Dump top-level types" &= name "types" &= explicit ]
                     , _cfgDumpTree = enum [ False &= name "no-tree" &= ignore,
                                             True  &= help "Dump results of intermediate steps" &= name "tree" &= explicit ]
                     , _cfgDumpImmediately = enum [ False &= ignore,
                                             True  &= help "Dump results immediately" &= name "i" &= explicit ]
                     , _cfgAnnotateLabels = enum [ False &= ignore,
                                                   True &= help "Annotate expressions with labels" &= name "@" &= explicit ]
                     }
