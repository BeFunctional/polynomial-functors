module JSON where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Graph.JSON
import Data.Graph.Conversion
import LambdaPi.AST
import Utils

jsonTests :: TestTree
jsonTests = testGroup "test json serialisation"
  [ testCase "simple poly" $
    convertPolyGraph "test" (VMkPoly VNat (VLam (const VNat)))
    @?=
    Graphical [Node "test" ["Nat"] ["Nat"]] []
  , testCase "parallel composition" $
    commandStrs [ "data Unit = MkUnit"
                , ":ctx"
                ]
    `eqOutput`
    ["Unit :: *"
    , "[]"
    ]
  ]

dataTest :: TestTree
dataTest = testGroup "test json serialization with custom data"
  [ testCase "parallel composition" $
    commandStrs [ "data Unit = MkUnit"
                , ":ctx"
                ]
    `eqOutput`
    undefined
  ]

