{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module LambdaPi.REPL where

import Prelude hiding (print, writeFile, putStrLn, readFile, putStr, getLine, show)

import Capability.State
import Effect.Logger

import Control.Monad.Except
--import Control.Monad.Writer.Class

import Data.List as LS
import Data.Char
import Data.Functor.Identity
import Data.Text as T
import Data.Text.IO as T
import Text.PrettyPrint.HughesPJ hiding (parens, render, text, (<>), char)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.Parsec.Prim (Parsec)
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import System.IO (hFlush, stdout)
import System.IO.Error

import LambdaPi.Common

data Command
   = TypeOf Text
   | Compile CompileForm
   | Browse
   | Quit
   | Help
   | Noop

data CompileForm
   = CompileInteractive Text
   | CompileFile        Text

data InteractiveCommand = Cmd [Text] Text (Text -> Command) Text

type Ctx inf = [(Name, inf)]
type LangState v inf = (Text, NameEnv v, Ctx inf)

data LangTerm
   = Inferrable
   | Checkable
   | Val


class Interpreter (c :: LangTerm -> *) where
  iname    :: Text
  iprompt  :: Text
  iitype   :: NameEnv (c Val) -> Ctx (c Val) -> (c Inferrable) -> Result (c Val)
  iquote   :: (c Val) -> (c Checkable)
  ieval    :: NameEnv (c Val) -> (c Inferrable) -> (c Val)
  ihastype :: c Val -> c Val
  icprint  :: c Checkable -> Doc
  itprint  :: c Val -> Doc
  iiparse  :: Parsec Text () (c Inferrable)
  isparse  :: Parsec Text () (Stmt (c Inferrable) (c Checkable))
  iassume  :: Logger m => LangState (c Val) (c Val) -> (Text, (c Checkable)) -> m (LangState (c Val) (c Val))

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
              => Maybe Text -> m ()
readevalprint stdlib =
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
                state' <- handleCommand c
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
             state' <- handleCommand (Compile $ CompileFile lib)
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

handleCommand :: forall f m. (Logger m, MonadIO m, HasState "poly" (LangState (f Val) (f Val)) m)
              => Interpreter f
              => Command -> m Feedback
handleCommand cmd = do
    (out, ve, te) <- get @"poly"
    case cmd of
       Quit   ->  (logStr "!@#$^&*") >> return Abort
       Noop   ->  return Continue
       Help   ->  logStr (helpTxt commands)
              >> return Continue
       TypeOf x ->
         do  x <- parseM "<interactive>" iiparse x
             t <- maybe (return Nothing) (iinfer ve te) x
             maybe (return ())
                   (\u -> logStr (render (itprint u)))
                   t
             return Continue
       Browse ->  do logIn (T.unlines [ s | Global s <- LS.reverse (nub (fmap fst te)) ])
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
    => MonadIO m
    => Interpreter f
    => Text -> m ()
compilePhrase input = do
    parsedInput <- parseM "<interactive>" isparse input
    maybe (return ()) handleStmt parsedInput

iinfer :: Logger m
    => Interpreter f
    => NameEnv (f Val) -> Ctx (f Val) -> (f Inferrable)
    -> m (Maybe (f Val))
iinfer d g t =
  case iitype d g t of
    Left e -> logErr e >> return Nothing
    Right v -> return (Just v)

handleStmt :: forall f m. Logger m
           => HasState "poly" (LangState (f Val) (f Val)) m
           => MonadIO m
           => Interpreter f
           => Stmt (f Inferrable) (f Checkable)
           -> m ()
handleStmt stmt = do
    (out, ve, te) <- get @"poly"
    case stmt of
        Assume ass -> foldM iassume (out, ve, te) ass >>= put @"poly"
        Let x e    -> checkEval x e >>= put @"poly"
        Eval e     -> checkEval it e >>= put @"poly"
        PutStrLn x -> logStr x >> return ()
        Out f      -> put @"poly" (f, ve, te)
        DataDecl nm cs -> undefined
  where
    checkEval :: Text -> f Inferrable ->
        m (LangState (f Val) (f Val))
    checkEval i t = do
      (out, ve, te) <- get @"poly"
      check (tshow . itprint) (out, ve, te) t
        (\ (y, v) -> do
          --  ugly, but we have limited space in the paper
          --  usually, you'd want to have the bound identifier *and*
          --  the result of evaluation
          let outtext = if i == it
              then render (icprint (iquote v) PP.<> text " :: " PP.<> itprint y)
              else render (text i PP.<> text " :: " PP.<> itprint y)
          logStr outtext
          unless (T.null out) (liftIO $ writeFile (unpack out) (process outtext)))
        (\ (y, v) -> ("",
            (Global i, v) : ve,
            (Global i, ihastype y) : te))

check :: forall f m. Logger m
      => Interpreter f
      -- how to print
      => (f Val -> Text)
      -- the state in which we typecheck
      -> LangState (f Val) (f Val)
      -- the term to check
      -> f Inferrable
      -- a way to print the result
      -> ((f Val, f Val) -> m ())
      -- a way to update the state
      -> ((f Val, f Val) -> LangState (f Val) (f Val))
      -> m (LangState (f Val) (f Val))
check showt state@(out, ve, te) t print k = do
  --  typecheck and evaluate
  x <- iinfer ve te t
  case x of
    Nothing ->
      return state
    Just y -> do
      let v = ieval ve t
      print (y, v)
      return (k (y, v))


it :: Text
it = "it"

process :: Text -> Text
process = T.unlines . fmap (\x -> "< " <> x) . T.lines
