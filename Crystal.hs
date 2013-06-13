module Main where

import Control.Lens
import Control.Monad
import Control.Monad.Reader
import System.Environment
import System.Exit
import System.IO
import System.Console.CmdArgs.Implicit

import Crystal.AST
import Crystal.Check
import Crystal.Config
import Crystal.Misc
import Crystal.Parser
import Crystal.Post
import Crystal.Pretty
import Crystal.Transform
import Crystal.Type

pipeline :: Expr Label -> Step DeclExpr
pipeline = transformC >=> infer >=> addChecks >=> postprocess 

process config fname cts =
  case parseCrystal fname cts of
       Left err  -> hPrint stderr err >> exitFailure
       Right ast -> do let ast' = runReader (pipeline ast) config 
                       putStrLn $ prettyD $ ast'
                       return ()

main = do config <- cmdArgs defaultArgs
          case config^.cfgInputFile of
            ""   -> process config "-"  =<< force `liftM` getContents
            file -> process config file =<< readFile file

force x = length x `seq` x
