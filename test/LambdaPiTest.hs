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
import LambdaPi.Common (Name(..), Stmt(..))
import LambdaPi.AST
import LambdaPi.Eval (cEval)

import Test.Tasty
import Test.Tasty.HUnit

import Utils
import JSON

-- test from top-level syntax
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

  , testCase "let id" $
    commandStrs ["let id = (\\x y -> y) :: (forall (a :: Type). a -> a)"
                , "id Nat 3"]
    `eqOutput`
    ["id :: forall (x :: *) (y :: x) . x"
    ,"3 :: Nat"]
  , testCase "data declaration" $
    commandStrs ["data K3 = Yes | No | Unknown"
                , "K3"
                , "Yes"
                ]
    `eqOutput`
    [ "K3 :: *"
    , "K3 :: *"
    , "Yes :: K3"
    ]

  , testCase "enum eliminator" $
    commandStrs [ "data Three = Yes | No | Unknown"
                , "let count = (\\x -> match x as (\\_ -> Nat) { Yes -> 0 ; No -> 1 ; Unknown -> 2 }) :: Three -> Nat"
                , "count No"
                ]
    `eqErrOutput`
    []

  , testCase "elim Bool 1" $
    commandStr "match True as (\\_ -> Nat) { False -> 10; True -> 2 }"
    `eqOutput`
    ["2 :: Nat"]
  , testCase "elim Bool 2" $
    commandStr "match True as (\\_ -> Nat) { True -> 10; False -> 2 }"
    `eqOutput`
    ["10 :: Nat"]
  , testCase "idBool" $
    commandStr "let idBool = (\\x -> match x as (\\_ -> Bool) { True -> True ; False -> False }) :: Bool -> Bool"
    `eqOutput`
    ["idBool :: forall x :: Bool . Bool"]
  ]

-- tests about polynomial functors
polyTests :: TestTree
polyTests = testGroup "poly tests"
  [ testCase "Nat Fin Poly" $
    commandStr "let natFin = MkPoly Nat Fin"
    `eqErrOutput` []
  , testCase "Custom types Poly" $
    commandStrs [
      "data Three = Yes | No | Unknown",
      "let polyThree = MkPoly Bool (\\_ -> Three)"]

    `eqErrOutput` []
  , testCase "parallel composition Poly" $
    commandStrs [
      "data Three = Yes | No | Unknown",
      "let polyThree = MkPoly Bool (\\_ -> Three)",
      ":load stdlib.lp",
      "parallel polyThree polyThree"]
    `eqErrOutput` []
  ]

-- test that should give and error
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

  , testCase "Non-exhaustive pattern match" $
    commandStr "match True as (\\_ -> Nat) { False -> 0 }"
    `eqErrOutput`
    ["Non-exhaustive pattern match, missing:\n - True\n"]

  , testCase "Mixed types in patterns" $
    commandStrs [ "data U = U1"
                , "match True as (\\_ -> Nat) { False -> 0 ; U1 -> 1 }"]
    `eqErrOutput`
    ["constructor False does not match expected type U"]
  ]

-- test from commands
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

-- tests from Statements
stmtTests :: TestTree
stmtTests = testGroup "statement tests" $

  [ testCase "test let id" $
    void (handleStmt @MLTT' (coerce makeIdStmt))
    `eqOutput`
    ["id :: forall (x :: *) (y :: x) . x"]

  , testCase "test let id ctx" $
    void (handleStmt @MLTT' (coerce makeIdStmt))
    `eqContext`
    ( [(Global "id", VLam (\x -> VLam (\y -> y)))]
    , [(Global "id", VPi VStar (\x -> VPi x (\_ -> x)))])

  , testCase "test data decl Bool" $
    void (handleStmt @MLTT' (DataDecl "Bool" ["True", "False"]))
    `eqContext`
    ( [ (Global "False", VNamedCon "False" 1)
      , (Global "True", VNamedCon "True" 0)
      , (Global "Bool", VNamedTy "Bool")
      ]
    , [ (Global "False", VNamedTy "Bool")
      , (Global "True", VNamedTy "Bool")
      , (Global "Bool", VStar)])

  , testCase "test data decl K3" $
    void (handleStmt @MLTT' (DataDecl "K3" ["Yes", "No", "Maybe"]))
    `eqContext`
    ( [ (Global "Maybe", VNamedCon "Maybe" 2)
      , (Global "No", VNamedCon "No" 1)
      , (Global "Yes", VNamedCon "Yes" 0)
      , (Global "K3", VNamedTy "K3")
      ]
    , [ (Global "Maybe", VNamedTy "K3")
      , (Global "No", VNamedTy "K3")
      , (Global "Yes", VNamedTy "K3")
      , (Global "K3", VStar)])
  ]

tests :: TestTree
tests = testGroup "REPL tests"
  [ syntaxTests
  , stmtTests
  , cmdTests
  , errorTests
  , polyTests
  , jsonTests
  ]

main :: IO ()
main =  defaultMain tests
