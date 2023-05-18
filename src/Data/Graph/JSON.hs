{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DerivingStrategies #-}

-- A graph data structure serialisable from/to JSON
module Data.Graph.JSON where

import Data.Aeson
import Data.Text
import GHC.Generics

data Graphical = Graphical
  { _nodes :: [Node],
    _strings :: [Edge]
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Node = Node
  { _name :: Text,
    _arity :: [Text],
    _coarity :: [Text]
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Edge = Edge
  { _name :: Text,
    _source :: EdgeRef,
    _target :: EdgeRef
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data EdgeRef = EdgeRef
  { _node :: Text,
    _port :: Int
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)
