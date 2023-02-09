module LambdaPi.Parser where

import Data.List as L
import Data.Text as T (Text, pack)
import Data.Functor.Identity (Identity)
import Text.ParserCombinators.Parsec hiding (parse, try, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.Parsec (Parsec, try)
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

import Common
import LambdaPi.AST

haskellP :: GenLanguageDef Text () Identity
haskellP = LanguageDef
         { commentStart   = "{-"
         , commentEnd     = "-}"
         , commentLine    = "--"
         , nestedComments = True
         , identStart     = letter
         , identLetter    = alphaNum <|> oneOf "_'"
         , opStart        = opLetter haskellP
         , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
         , reservedOpNames= []
         , reservedNames  = ["forall", "let", "assume", "putStrLn", "out"]
         , caseSensitive  = True
         }

lambdaPi :: GenTokenParser Text () Identity
lambdaPi = makeTokenParser haskellP

type TextParser st = Parsec Text st

parseLet :: [Text] -> TextParser () (Text, ITerm)
parseLet e =  do
  reserved lambdaPi "let"
  x <- identifier'
  reserved lambdaPi "="
  t <- parseITerm 0 e
  return (x, t)

stringLiteral' :: TextParser () Text
stringLiteral' = fmap pack (stringLiteral lambdaPi)
identifier' :: TextParser () Text
identifier' = fmap pack (identifier lambdaPi)

parseStmt :: [Text] -> TextParser () (Stmt ITerm CTerm)
parseStmt e =
      fmap (uncurry Let) (parseLet e)
  <|> do
        reserved lambdaPi "assume"
        (xs, ts) <- parseBindings False []
        return (Assume (reverse (zip xs ts)))
  <|> do
        reserved lambdaPi "putStrLn"
        x <- stringLiteral'
        return (PutStrLn x)
  <|> do
        reserved lambdaPi "out"
        x <- option "" stringLiteral'
        return (Out x)
  <|> fmap Eval (parseITerm 0 e)
parseBindings :: Bool -> [Text] -> TextParser () ([Text], [CTerm])
parseBindings b e =
                   (let rec :: [Text] -> [CTerm] -> TextParser () ([Text], [CTerm])
                        rec e ts =
                          do
                           (x,t) <- parens lambdaPi
                                      (do
                                         x <- identifier'
                                         reserved lambdaPi "::"
                                         t <- parseCTerm 0 (if b then e else [])
                                         return (x,t))
                           (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                    in rec e [])
                   <|>
                   do  x <- identifier'
                       reserved lambdaPi "::"
                       t <- parseCTerm 0 e
                       return (x : e, [t])
parseITerm :: Int -> [Text] -> TextParser () ITerm
parseITerm 0 e =
      do
        reserved lambdaPi "forall"
        (fe,t:ts) <- parseBindings True e
        reserved lambdaPi "."
        t' <- parseCTerm 0 fe
        return (foldl (\ p t -> Pi t (Inf p)) (Pi t t') ts)
  <|>
  try
     (do
        t <- parseITerm 1 e
        rest (Inf t) <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam e)
        rest t
  where
    rest t = do
        reserved lambdaPi "->"
        t' <- parseCTerm 0 (mempty : e)
        return (Pi t t')
parseITerm 1 e =
  try
     (do
        t <- parseITerm 2 e
        rest (Inf t) <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam e)
        rest t
  where
    rest t =
      do
        reserved lambdaPi "::"
        t' <- parseCTerm 0 e
        return (Ann t t')
parseITerm 2 e =
      do
        t <- parseITerm 3 e
        ts <- many (parseCTerm 3 e)
        return (foldl (:$:) t ts)
parseITerm 3 e =
      do
        reserved lambdaPi "*"
        return Star
  <|> do
        reserved lambdaPi "Poly"
        return Poly
  <|> do
        n <- natural lambdaPi
        return (toNat n)
  <|> do
        x <- identifier'
        case findIndex (== x) e of
          Just n  -> return (Bound n)
          Nothing -> return (Free (Global x))
  <|> parens lambdaPi (parseITerm 0 e)

parseCTerm :: Int -> [Text] -> TextParser () CTerm
parseCTerm 0 e =
      parseLam e
  <|> fmap Inf (parseITerm 0 e)
parseCTerm p e =
      try (parens lambdaPi (parseLam e))
  <|> fmap Inf (parseITerm p e)

parseLam :: [Text] -> TextParser () CTerm
parseLam e =
      do reservedOp lambdaPi ("\\" :: String)
         xs <- many1 identifier'
         reservedOp lambdaPi "->"
         t <- parseCTerm 0 (L.reverse xs ++ e)
         --  reserved lambdaPi "."
         return (iterate Lam t !! length xs)
toNat :: Integer -> ITerm
toNat n = Ann (toNat' n) (Inf Nat)
toNat' :: Integer -> CTerm
toNat' 0  =  Zero
toNat' n  =  Succ (toNat' (n - 1))
