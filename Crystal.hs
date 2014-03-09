{-#LANGUAGE OverloadedStrings #-}
module Main where

import Control.Lens
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Text.Format
import System.Environment
import System.Exit
import System.IO
import System.Console.CmdArgs.Implicit

import Crystal.AST
import Crystal.Check
import Crystal.Config
import Crystal.Infer
import Crystal.Misc
import Crystal.Parser
import Crystal.Post
import Crystal.Pretty
import Crystal.Transform
import Crystal.Type

type Pipeline = Expr Label -> Step DeclExpr

pipeline :: Pipeline
pipeline = transformC >=> infer >=> addChecks >=> postprocess 

runPipeline :: Pipeline -> Expr Label -> Config -> (DeclExpr, [StepResult])
runPipeline pipe ast cfg = runReader (runWriterT (pipe ast)) cfg

process config fname cts =
  case parseCrystal fname cts of
       Left err  -> hPrint stderr err >> exitFailure
       Right ast -> do let (ast', results) = runPipeline pipeline ast config
                       putStrLn $ prettyD $ ast'
                       when (not (null results)) $ do
                         putStr "\n<extra-information>\n"
                         forM_ results $ \(header,cts) ->
                           Data.Text.Format.print "<{}>\n<![CDATA[{}]]>\n</{}>\n" (header, cts, header)
                         putStr "\n</extra-information>\n"

main = do config <- cmdArgs defaultArgs
          case config^.cfgInputFile of
            ""   -> process config "-"  =<< force `liftM` getContents
            file -> process config file =<< readFile file

force x = length x `seq` x
