{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Control.Monad (void)

import Data.Coerce (coerce)

import LambdaPi.REPL (handleCommand, handleStmt, Command(..), CompileForm(..))
import LambdaPi.Init hiding (main)
import LambdaPi.Common (Stmt(..))

import Test.Tasty
import Test.Tasty.HUnit

import Utils

syntaxTests :: TestTree
syntaxTests = testGroup "syntax tests"
  [ testCase "identity" $
    commandStr "let id = (\\y x -> x) :: forall (a :: Type). a -> a"
    `eqOutput`
    ["id :: forall (x :: *) (y :: x) . x"]
  , testCase "if true" $
    commandStr "if (\\x -> Nat) 3 4 True"
    `eqOutput`
    ["3 :: Nat"]
  , testCase "if False" $
    commandStr "if (\\x -> Nat) 3 4 False"
    `eqOutput`
    ["4 :: Nat"]
  , testCase "Decl Pair" $
    commandStr "let Pair = (\\x y -> Sigma x (\\_ -> y)) :: forall (x :: Type) (y :: Type). Type"
    `eqOutput`
    ["Pair :: forall (x :: *) (y :: *) . *"]
  ]

polyTests :: TestTree
polyTests = testGroup "poly tests"
  [
  ]

errorTests :: TestTree
errorTests = testGroup "error tests"
  [ testCase "unexpected nat application" $
    commandStr "if (\\_ -> Nat) 3 2 1"
    `eqErrOutput`
    ["type mismatch:\n\
     \type inferred:  Nat\n\
     \type expected:  Bool\n\
     \for expression: 1 :: Nat"
    ]
  ]

cmdTests :: TestTree
cmdTests = testGroup "command tests" $
  [ testCase "Type Nat" $
    void (handleCommand @MLTT' (TypeOf "Nat"))
    `eqOutput`
    ["*"]
  , testCase "browse" $
    void (handleCommand @MLTT' Browse)
    `eqOutput`
    ["finElim\nFin\nFSucc\nFZero\nif\nFalse\nTrue\nBool\neqElim\nEq\nRefl\nvecElim\nVec\nCons\nNil\nsigElim\nMkSigma\nSigma\npolyElim\nMkPoly\nPoly\nType\nnatElim\nNat\nSucc\nZero\n"]
  , testCase "stdlib import" $
    void (handleCommand @MLTT' (Compile (CompileFile "stdlib.lp")))
    `eqErrOutput`
    []
  ]

stmtTests :: TestTree
stmtTests = testGroup "statement tests" $
  [ testCase "test let id" $
    void (handleStmt @MLTT' (coerce makeIdStmt))
    `eqOutput`
    ["id :: forall (x :: *) (y :: x) . x"]
  , testCase "test data decl Bool" $
    void (handleStmt @MLTT' (DataDecl "Bool" ["True", "False"]))
    `eqOutput`
    ["Bool = True | False"]
  ]

tests :: TestTree
tests = testGroup "REPL tests"
  [ syntaxTests
  , stmtTests
  , cmdTests
  , errorTests
  , polyTests
  ]

main :: IO ()
main =  defaultMain tests
