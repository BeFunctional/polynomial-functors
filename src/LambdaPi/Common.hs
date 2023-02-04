module LambdaPi.Common where

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Text

data Name
   = Global Text
   | Local  Int
   | Quote  Int
  deriving (Show, Eq, Ord)

data Ty
   = TFree  Name
   | Fun    Ty Ty
  deriving (Show, Eq)

type Result a = Either Text a
type NameEnv v = [(Name, v)]

data Stmt i tinf
   = Let Text i           --  let x = t
   | Assume [(Text,tinf)] --  assume x :: t, assume x :: *
   | Eval i
   | PutStrLn Text        --  lhs2TeX hacking, allow to print "magic" string
   | Out Text             --  more lhs2TeX hacking, allow to print to files
  deriving (Show)

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

vars :: [Text]
vars = [ pack (c : n) | n <- "" : fmap show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]

render :: Doc -> Text
render = pack . PP.render

text :: Text -> Doc
text = PP.text . unpack

tshow :: Show a => a -> Text
tshow = pack . show
