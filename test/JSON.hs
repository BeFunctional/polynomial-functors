module JSON where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Aeson (encode)
import Data.Text (pack)
import Data.Graph.JSON
import Data.Graph.Conversion
import LambdaPi.AST
import Utils

jsonTests :: TestTree
jsonTests = testGroup "test json serialisation"
  [ testCase "simple poly" $
    convertPolyGraph "test" (VMkPoly VNat (VLam (const VNat)))
    @?=
    Graphical [Node "test" [Arity "Nat"] [Arity "Nat"]] []
  , testCase "get empty context" $
    commandStrs [ "data Unit = MkUnit"
                , ":ctx"
                ]
    `eqOutput`
    ["Unit :: *"
    , "\"[]\""
    ]
  , testCase "non-empty context" $
    commandStrs [":l stdlib.lp"
                , ":ctx"
                ]
    `eqLastOutput`
    pack (show (encode [Graphical [Node "poly2" [Arity "Nat"] [Arity "\\ x -> Vec Nat x"]] [],
                        Graphical [Node "poly1" [Arity "Nat"] [Arity "\\ x -> Fin x"]][]]))
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

