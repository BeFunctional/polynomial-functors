module Main where

import LambdaPi.Init (repLP, runInteractive)

import System.Environment
import Data.Text (pack)

main :: IO ()
main = do
  (_ : args) <- getArgs
  case args of
    [stdlib] -> runInteractive (pack stdlib)
    _ -> repLP
