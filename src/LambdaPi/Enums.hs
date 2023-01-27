module LambdaPi.Enums where

import Data.Text
import LambdaPi.AST

data Enum = Enum
  { name :: Text
  , fields :: [Text]
  }

synthesizeTypeConstructor :: Text -> CTerm
synthesizeTypeConstructor typeName =
    undefined

synthesizeValueConstructors :: [Text] -> [CTerm]
synthesizeValueConstructors = undefined

synthesizeConstructorTypes :: Text -> [Text] -> [CTerm]
synthesizeConstructorTypes = undefined
