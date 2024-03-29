{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
module Utils where


import Capability.Sink
import Capability.Source
import Capability.State
import Capability.Reader

import Control.Monad.Reader (ReaderT(..))
import Control.Monad.IO.Class (MonadIO)

import Data.Text (Text)
import Data.IORef
import Data.Coerce
import Data.Graph.Conversion

import Effect.Logger

import GHC.Generics

import Test.Tasty
import Test.Tasty.HUnit

import LambdaPi.AST
import LambdaPi.Common
import LambdaPi.Init hiding (main)
import LambdaPi.Quote
import LambdaPi.REPL

-- bespoke Eq instance for Values in tests
instance Eq Value where
  a == b = quote0 a == quote0 b

data TestCtx = TestCtx
  { logCtx :: LogCtx
  , poly :: IORef PolyState
  } deriving Generic

newtype TestM a = TestM (ReaderT TestCtx IO a)
  deriving (Functor, Applicative, Monad, MonadIO)
  deriving (HasSource "poly" PolyState, HasSink "poly" PolyState, HasState "poly" PolyState) via
    ReaderIORef (Rename "poly"(Field "poly" ()
    (MonadReader (ReaderT TestCtx IO))))
  deriving Logger via
    TheLoggerReader (Field "logger" "logCtx" (Field "logCtx" "logCtx" (MonadReader (ReaderT TestCtx IO))))

-- the return type is the state of the compiler after running the series of commands in `TestM`
-- `a` is the return type expected, usally Unit
-- `PolyEngine` is the state of the context after running the commands
-- `[Text]` is the list of logs emmited by the compiler. We use this to check what is the output
-- of the repl for a normal user (as opposed to a test user). The second `[Text]` is the list
-- log errors emmited by the compiler.
runTest' :: PolyEngine -> TestM a -> IO (a, PolyEngine, [Text], [Text])
runTest' st (TestM r) = do
  logRef <- newIORef []
  errRef <- newIORef []
  polyRef <- newIORef st
  result <- runReaderT r (TestCtx (print2ListErr logRef errRef) (coerce polyRef))
  finalLogs <- readIORef logRef
  finalErrors <- readIORef errRef
  finalState <- readIORef polyRef
  pure (result, finalState, reverse finalLogs, reverse finalErrors)

-- a simple statement written manually
makeIdStmt :: Stmt ITerm CTerm
makeIdStmt =
  Let "id" (Ann (Lam $ Lam (Inf (Bound 0)))
           (Inf (Pi (Inf Star) (Inf $ Pi (Inf $ Bound 0) (Inf $ Bound 1)))))

-- compile and run multple commands sequentially
commandStrs :: (MonadIO m, HasState "poly" PolyState m, Logger m)
            => [Text] -> m ()
commandStrs = mapM_ commandStr

-- compile a command given as a string
commandStr :: (MonadIO m, HasState "poly" PolyState m, Logger m)
           => Text -> m ()
commandStr cmd = do
  parsedCommand <- interpretCommand cmd
  result <- handleCommand @MLTT' (coerce $ uncurry convertPolyGraph) parsedCommand
  return ()

-- check if the final state and the std output are the ones expected
isEq :: TestM () -> (PolyState, [Text]) -> Assertion
isEq op endState = do
  (_, finalState, printed, _) <- runTest' initialContext op
  (finalState, printed) @?= coerce endState

-- check if the std output is the one expected
eqOutput :: TestM () -> [Text] -> Assertion
eqOutput op printedExpected = do
  (_, _, printedActual, errors) <- runTest' initialContext op
  printedActual @?= printedExpected

eqLastOutput :: TestM () -> Text -> Assertion
eqLastOutput op printedExpected = do
  (_, _, printedActual, errors) <- runTest' initialContext op
  last printedActual @?= printedExpected

eqOutErr :: TestM () -> [Text] -> [Text] -> Assertion
eqOutErr op printedExpected errorsExpected = do
  (_, _, printedActual, errors) <- runTest' initialContext op
  printedActual @?= printedExpected
  errors @?= errorsExpected

-- check the error output is the one expected
eqErrOutput :: TestM () -> [Text] -> Assertion
eqErrOutput op expectedErrors = do
  (_, _, _, errors) <- runTest' initialContext op
  errors @?= expectedErrors

eqContext :: TestM () -> ([(Name, Value)], [(Name, Value)]) -> Assertion
eqContext op (expectedValues, expectedTypes) = do
  (_, (LangState _ values types), _, _) <- runTest' initialContext op
  reverse (drop (length lpve) (reverse values)) @?= expectedValues
  reverse (drop (length lpte) (reverse types)) @?= expectedTypes
