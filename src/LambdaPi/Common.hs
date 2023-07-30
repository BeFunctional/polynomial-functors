{-# LANGUAGE LambdaCase #-}
module LambdaPi.Common where

import Text.PrettyPrint.HughesPJ (Doc)
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Text
import qualified Data.Map as Map
import Data.Bifunctor

data Name
   = Global Text
   | Local  Int
   | Quote  Int
  deriving (Show, Eq, Ord)

data ContextRow val inf
  = Assumption { assumedTy :: val }
  | UserDef { definedTy :: val
            , definedCon :: inf
            }
  deriving (Show, Eq)

getType :: ContextRow v i -> v
getType (Assumption a) = a
getType (UserDef a _) = a

data Ty
   = TFree  Name
   | Fun    Ty Ty
  deriving (Show, Eq)

type Result a = Either Text a
type Ctx val inf = Map.Map Name (ContextRow val inf)

values :: Ctx val inf -> [(Name, inf)]
values ctx = [(nm, val) | (nm, UserDef _ val) <- Map.toList ctx]

types :: Ctx val inf -> [(Name, val)]
types = fmap (fmap getType) . Map.toList

data Stmt i tinf
   = Let Text i           --  let x = t
   | Assume [(Text,tinf)] --  assume x :: t, assume x :: *
   | Eval i
   | PutStrLn Text        --  lhs2TeX hacking, allow to print "magic" string
   | Out Text             --  more lhs2TeX hacking, allow to print to files
   | DataDecl {name :: Text, constructors :: [Text] }
   | TypeAlias {name :: Text, body :: i }
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

lookupCtx :: Show a => Eq a => [(a, b)] -> a -> Result b
lookupCtx ctx nm = maybe
    (Left $ "could not find '" <> tshow nm <> "' in context:\n"
         <> Data.Text.unlines (fmap (tshow . fst) ctx))
    Right (lookup nm ctx)

collectErrors :: [Result a] -> Result [a]
collectErrors results =
  let collected = collectErrors' results
  in first (\case { [x] -> x
                  ; x  -> "multiple errors:\n" <> Data.Text.unlines (fmap (" - " <> ) x)}) collected

  where
  collectErrors' :: [Result a] -> Either [Text] [a]
  collectErrors' [x] = bimap pure pure x
  collectErrors' (Left err : xs) = case collectErrors' xs of
    Left moreErrors -> Left (err : moreErrors)
    Right ok -> Left [err]
  collectErrors' (Right v : xs) = fmap (v :) (collectErrors' xs)
