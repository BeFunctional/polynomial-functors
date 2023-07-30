{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module LambdaPi.REPL where

import Prelude hiding (print, writeFile, putStrLn, readFile, putStr, getLine, show)

import Capability.Constraints
import Capability.State
import Capability.Reader
import Effect.Logger

import Control.Monad.Except
--import Control.Monad.Writer.Class

import Data.Aeson (encode)
import Data.List as LS
import Data.Char
import Data.Functor.Identity
import Data.Generics.Product
import Data.Text as T
import Data.Text.IO as T
import Data.Kind (Type)
import Data.Graph.Conversion
import Data.Graph.JSON
import qualified Data.Map as Map

import Text.PrettyPrint.HughesPJ hiding (parens, render, text, (<>), char)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.Parsec.Prim (Parsec)
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import System.IO (hFlush, stdout)
import System.IO.Error

import GHC.Generics (Generic)

import LambdaPi.Common

data Command
   = TypeOf Text
   | Compile CompileForm
   | Browse
   | PolyCtx
   | Quit
   | Help
   | Noop

data CompileForm
   = CompileInteractive Text
   | CompileFile        Text

data InteractiveCommand = Cmd [Text] Text (Text -> Command) Text

data LangState v inf = LangState
  { out :: Text
  , ctx :: Ctx v inf
  }
  deriving (Show, Eq, Generic)

-- convert from an operation on HasState "poly" to an operation on
-- HasReader "values". It extracts the value context from the state.
-- stateValuesRead
--     :: (HasState "poly" (LangState vals tys) m)
--     => (forall m'. HasReader "values" [(Name, vals)] m' => m' a) -> m a
-- stateValuesRead x
--     = zoom @"values" @(Rename "valCtx" :.: Field "valCtx" "poly") @'[]
--       (magnify @"values" @ReadStatePure @'[] x)

readContext
    :: forall m f a. (HasState "poly" (LangState (f Val) (f Val)) m)
    => Logger m
    => (forall m'. Logger m' => HasReader "poly" (LangState (f Val) (f Val)) m' => m' a) -> m a
readContext op = magnify @"poly" @ReadStatePure @'[Logger] @(LangState (f Val) (f Val)) op

data LangTerm
   = Inferrable
   | Checkable
   | Val

class Interpreter (c :: LangTerm -> *) where
  iname    :: Text
  iprompt  :: Text
  iitype   :: HasReader "poly" (LangState (c Val) (c Val)) m
           => (c Inferrable) -> m (Result (c Val))
  iquote   :: (c Val) -> (c Checkable)
  ieval    :: [(Name, (c Val))]
           -> c Inferrable -> (c Val)
  ihastype :: c Val -> c Val
  icprint  :: c Checkable -> Doc
  itprint  :: c Val -> Doc
  iiparse  :: Parsec Text () (c Inferrable)
  isparse  :: Parsec Text () (Stmt (c Inferrable) (c Checkable))
  iassume  :: Logger m => HasState "poly" (LangState (c Val) (c Val)) m
           => (Text, (c Checkable)) -> m ()
  iaddData :: Logger m => HasState "poly" (LangState (c Val) (c Val)) m
           => Text -> [Text] -> m ()
  iaddAlias :: Logger m => HasState "poly" (LangState (c Val) (c Val)) m
            => Text -> c Inferrable -> m ()
  -- Returns all the poly in context with their first and second component as well as their name
  ipolyCtx :: HasState "poly" (LangState (c Val) (c Val)) m
           => m [(Text, c Val)]

helpTxt :: [InteractiveCommand] -> Text
helpTxt cs
  =  "List of commands:  Any command may be abbreviated to :c where\n" <>
     "c is the first character in the full name.\n\n" <>
     "<expr>                  evaluate expression\n" <>
     "let <var> = <expr>      define variable\n" <>
     "assume <var> :: <expr>  assume variable\n\n"
     <>
     T.unlines (fmap (\ (Cmd cs' a _ d) ->
         let ct = T.concat (LS.intersperse ", " (fmap (<> if T.null a then "" else " " <> a) cs'))
         in  ct <> T.replicate ((24 - T.length ct) `max` 2) " " <> d)
         cs)

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
       Cmd [":browse"]      ""        (const Browse) "browse names in scope",
       Cmd [":ctx"]         ""        (const PolyCtx) "convert the polynomials into their graphical representation in JSON",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "load program from file",
       Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
       Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]

-- An empty language def in order to use whitespace
languageDef :: GenLanguageDef Text () Identity
languageDef = LanguageDef
               { commentStart   = ""
               , commentEnd     = ""
               , commentLine    = ""
               , nestedComments = True
               , identStart     = letter <|> char '_'
               , identLetter    = alphaNum <|> oneOf "_'"
               , opStart        = opLetter languageDef
               , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
               , reservedOpNames= []
               , reservedNames  = []
               , caseSensitive  = True
               }

dummy = makeTokenParser languageDef

parsePure :: Text
          -> Parsec Text () a
          -> Text -> Either Text a
parsePure filename parser content =
  case P.parse
               (whiteSpace dummy >> parser >>= \x -> eof >> return x)
               (unpack filename) content of
    Left err -> Left (tshow err)
    Right val -> Right val

parseM :: Logger m => Text -> Parsec Text () a -> Text -> m (Maybe a)
parseM filename parser content =
  case parsePure filename parser content of
    Left e  -> logErr e >> return Nothing
    Right r -> return (Just r)


readevalprint :: forall f m. Logger  m
              => HasState "poly" (LangState (f Val) (f Val)) m
              => MonadIO m
              => Interpreter f
              => ((Text, f 'Val) -> Graphical) -> Maybe Text -> m ()
readevalprint encodeData stdlib =
  let rec :: m ()
      rec =
        do
          state <- get @"poly"
          logIn (iprompt @f)
          liftIO $ hFlush stdout
          x <- liftIO $ catchIOError (fmap Just getLine) (const $ return Nothing)
          case x of
            Nothing -> return ()
            Just "" -> rec
            Just x  -> do
                c <- interpretCommand x
                state' <- handleCommand encodeData c
                case state' of
                  Abort -> return ()
                  Continue -> rec
  in
    do
      --  welcome
      logStr ("Interpreter for "
             <> iname @f <> ".\n"
             <> "Type :? for help.")
      case stdlib of
           Nothing -> rec
           Just lib -> do
             state <- get @"poly"
             state' <- handleCommand encodeData (Compile $ CompileFile lib)
             case state' of
               Abort -> return ()
               Continue -> rec

interpretCommand :: Logger m => Text -> m Command
interpretCommand x
  =  if T.isPrefixOf ":" x then
       do  let  (cmd,t')  =  T.break isSpace x
                t         =  T.dropWhile isSpace t'
           --  find matching commands
           let  matching  =  LS.filter (\ (Cmd cs _ _ _) -> LS.any (T.isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  logStr ("Unknown command `" <> cmd <> "'. Type :? for help.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             x   ->  do  logStr ("Ambiguous command, could be " <> T.concat (LS.intersperse ", " [ LS.head cs | Cmd cs _ _ _ <- matching ]) <> ".")
                         return Noop
     else
       return (Compile (CompileInteractive x))

data Feedback = Continue | Abort

handleCommand
    :: forall f m. (Logger m, MonadIO m)
    => HasState "poly" (LangState (f Val) (f Val)) m
    => Interpreter f
    => ((Text, f Val) -> Graphical)
    -> Command -> m Feedback
handleCommand encodeData cmd = do
    case cmd of
       Quit   ->  (logStr "!@#$^&*") >> return Abort
       Noop   ->  return Continue
       Help   ->  logStr (helpTxt commands)
              >> return Continue
       TypeOf x -> do
           x <- parseM "<interactive>" (iiparse @f) x
           t :: Maybe (f Val) <- case x of
                                   Nothing -> pure Nothing
                                   Just x -> readContext (iinfer x)
           maybe (return ())
                 (\u -> logStr (render (itprint u)))
                 t
           return Continue
       PolyCtx -> do ctx <- ipolyCtx
                     logStr (tshow $ encode (fmap encodeData ctx))
                     return Continue
       Browse ->  do
                     (LangState out ctx) <- get @"poly"
                     logIn (T.unlines [s | Global s <- Map.keys ctx])
                     return Continue
       Compile c -> do
            case c of
                CompileInteractive s -> compilePhrase s
                CompileFile f        -> compileFile f
            return Continue

compileFile
    :: Logger m
    => HasState "poly" (LangState (f Val) (f Val)) m
    => MonadIO m
    => Interpreter f
    => Text
    -> m ()
compileFile f =
  do
    x <- liftIO $ readFile (unpack f)
    stmts <- parseM f (many isparse) x
    maybe (return ()) (mapM_ handleStmt) stmts

compilePhrase
    :: Logger m
    => HasState "poly" (LangState (f Val) (f Val)) m
    => Interpreter f
    => Text -> m ()
compilePhrase input = do
    parsedInput <- parseM "<interactive>" isparse input
    maybe (return ()) handleStmt parsedInput

iinfer
    :: Logger m
    => Interpreter f
    => HasReader "poly" (LangState (f Val) (f Val)) m
    => (f Inferrable)
    -> m (Maybe (f Val))
iinfer t = do
  ty <- iitype t
  case ty of
    Left e -> logErr e >> return Nothing
    Right v -> return (Just v)

-- How to add a declaration to the context
checkEval :: Logger m
          => HasState "poly" (LangState (f Val) (f Val)) m
          => Interpreter f
          => Text -> f Inferrable -> m ()
checkEval i t = do
  (LangState out ctx) <- get @"poly"
  check t
    (\ (y, v) -> do
      let outtext = if i == it
          then render (icprint (iquote v) PP.<> text " :: " PP.<> itprint y)
          else render (text i PP.<> text " :: " PP.<> itprint y)
      logStr outtext)
    (\ (y, v) (LangState out ctx) -> (LangState ""
        (Map.insert (Global i) (UserDef (ihastype y) v) ctx))
        -- ((Global i, v) : ve)
        -- ((Global i, ihastype y) : te))
    )

handleStmt :: forall f m. Logger m
           => HasState "poly" (LangState (f Val) (f Val)) m
           => Interpreter f
           => Stmt (f Inferrable) (f Checkable)
           -> m ()
handleStmt stmt = do
    (LangState out ctx) <- get @"poly"
    case stmt of
        Assume ass -> mapM_ iassume ass
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> logStr x >> return ()
        Out f      -> put @"poly" (LangState f ctx)
        DataDecl nm cs -> iaddData nm cs
        TypeAlias nm cs -> iaddAlias nm cs
  where

newtype ValuesFromCtx (m :: Type -> Type) (a :: Type) = ValuesFromCtx (m a)
  deriving (Functor, Applicative, Monad)


check :: forall f m. Logger m
      => Interpreter f
      -- the state in which we typecheck
      => HasState "poly" (LangState (f Val) (f Val)) m
      -- the term to check
      => f Inferrable
      -- a way to print the result
      -> ((f Val, f Val) -> m ())
      -- a way to update the state
      -> ((f Val, f Val) -> LangState (f Val) (f Val) -> LangState (f Val) (f Val))
      -> m ()
check t print upd = do
  --  typecheck and evaluate
  x <- readContext (iinfer t)
  case x of
    Nothing -> pure ()
    Just ty -> do
      ctx <- values . ctx <$> get @"poly"
      let val = ieval ctx t
      print (ty, val)
      modify @"poly" (upd (ty, val))



it :: Text
it = "it"

process :: Text -> Text
process = T.unlines . fmap (\x -> "< " <> x) . T.lines
