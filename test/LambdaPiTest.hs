{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import REPL
import Common
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity

import Data.Text

import LambdaPi.AST
import LambdaPi.Main hiding (main)

newtype TestM a = TestM { runTest :: StateT PolyEngine (Writer [Text]) a }
  deriving newtype (Functor, Applicative, Monad)

-- the return type is the state of the compiler after running the series of commands in `TestM`
-- `a` is the return type expected, usally Unit
-- `PolyEngine` is the state of the context after running the commands
-- `[Text]` is the list of logs emmited by the compiler. We use this to check what is the output
-- of the repl for a normal user (as opposed to a test user).
runTest' :: PolyEngine -> TestM a -> ((a, PolyEngine), [Text])
runTest' st = runWriter . flip runStateT st . runTest

runCommands :: [Stmt ITerm CTerm] -> TestM ()
runCommands cmds = undefined

-- initialises the context with the standard library
initPoly :: IO PolyEngine
initPoly = undefined

runRepl :: Text -> State PolyEngine ()
runRepl input = undefined

makeIdStmt :: Stmt ITerm CTerm
makeIdStmt =
  Let "id" (Ann (Inf (Pi (Inf Star) (Inf Star))) (Lam (Inf (Bound 0))))

stringIdStmt :: Text
stringIdStmt = "let id : forall a :: * . a -> a = \\_ -> \\x -> x"

isEq`

syntaxTests :: TestTree
syntaxTests = testCase "add identity"
  do

  `isEq`
  ([], ["ok"])

stmtTests :: TestTree
stmtTests = undefined

tests :: TestTree
tests = testGroup "REPL tests"
  [ syntaxTests
  , stmtTests
  ]

main :: IO ()
main =  defaultMain tests
