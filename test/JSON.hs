module JSON where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Graph.JSON
import Data.Graph.Conversion
import LambdaPi.AST

jsonTests :: TestTree
jsonTests = testGroup "test json serialisation"
  [ testCase "simple poly" $
    convertPolyGraph "test" (VMkPoly VNat (VLam (const VNat)))
    @?=
    Graphical [Node "test" ["Nat"] ["Nat"]] []
  ]

