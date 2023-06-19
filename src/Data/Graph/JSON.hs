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
  { nodes :: [Node],
    strings :: [Edge]
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data LevelInfo = LevelInfo
  { x :: Double,
    y :: Double
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Node = Node
  { name :: Text,
    arity :: [Arity],
    coarity :: [Arity],
    level :: Maybe LevelInfo
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Arity = Arity
  { name :: Text }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Edge = Edge
  { name :: Text,
    source :: EdgeRef,
    target :: EdgeRef
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data EdgeRef = EdgeRef
  { node :: Text,
    port :: Text
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)
