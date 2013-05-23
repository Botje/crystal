module Main where

import System.Environment
import System.Exit
import System.IO
import Control.Monad

import Crystal.AST
import Crystal.Check
import Crystal.Parser
import Crystal.Post
import Crystal.Pretty
import Crystal.Transform
import Crystal.Type

process fname cts =
  case parseCrystal fname cts of
       Left err  -> hPrint stderr err >> exitFailure
       Right ast -> do let ast' = transformC ast
--                        putStrLn $ show ast'
                       putStrLn $ pretty ast'
                       putStrLn "==================="
                       putStrLn $ prettyD $ postprocess $ addChecks $ infer ast'
                       return ()

main = do args <- getArgs
          case args of
            [file] -> process file =<< readFile file
            _      -> process "-"  =<< force `liftM` getContents

force x = length x `seq` x
