module Data.Graph.Conversion where

import Data.Graph.JSON
import Data.Text
import Data.Maybe
import LambdaPi.AST
import LambdaPi.Quote
import LambdaPi.Printer

-- right now we print nodes naively without
-- splitting products or composition
-- Converting composition into multiple nodes with edges is probably the way to go
-- splitting products could be interesting as well. There might be an argument for
-- splitting coproducts but we would need an extra piece of information in the graph
-- data to indicate it's a different kind of split than product.
convertPolyNode :: Text -> Value -> Maybe Node
convertPolyNode termName (VMkPoly pos dir) =
      Just $ Node
          termName
          [Arity $ pack $ show $ cPrint 0 0 (quote0 pos)]
          [Arity $ pack $ show $ cPrint 0 0 (quote0 dir)]
convertPolyNode _ _ = Nothing

convertPolyGraph :: Text -> Value -> Graphical
convertPolyGraph termName poly = Graphical (maybeToList $ convertPolyNode termName poly) []

convertListNode :: [(Text, Value)] -> [Node]
convertListNode = catMaybes . fmap (uncurry convertPolyNode )

convertListGraph :: [(Text, Value)] -> Graphical
convertListGraph = flip Graphical [] . convertListNode
