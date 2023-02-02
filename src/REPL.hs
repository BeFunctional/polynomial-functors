{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module REPL where

import Prelude hiding (print, writeFile, putStrLn, readFile, putStr, getLine, show)
import Control.Monad.Except
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

import Common

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

class Interpreter iterm cterm value where
  iname    :: Text
  iprompt  :: Text
  iitype   :: NameEnv value -> Ctx value -> iterm -> Result value
  iquote   :: value -> cterm
  ieval    :: NameEnv value -> iterm -> value
  ihastype :: value -> value
  icprint  :: cterm -> Doc
  itprint  :: value -> Doc
  iiparse  :: Parsec Text () iterm
  isparse  :: Parsec Text () (Stmt iterm cterm)
  iassume  :: LangState value value -> (Text, cterm) -> IO (LangState value value)

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

parseIO :: Text -> Parsec Text () a -> Text -> IO (Maybe a)
parseIO filename parser content =
  case parsePure filename parser content of
    Left e  -> putStrLn e >> return Nothing
    Right r -> return (Just r)


readevalprint :: forall i c v. Interpreter i c v
              => Maybe Text ->  LangState v v -> IO ()
readevalprint stdlib state@(out, ve, te) =
  let rec :: Interpreter i c v => LangState v v -> IO ()
      rec state =
        do
          putStr (iprompt @i @c @v)
          hFlush stdout
          x <- catchIOError (fmap Just getLine) (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->
              rec state
            Just x    ->
              do
                c  <- interpretCommand x
                state' <- handleCommand @i @c state c
                maybe (return ()) rec state'
  in
    do
      --  welcome
      putStrLn ("Interpreter for "
             <> iname @i @c @v <> ".\n"
             <> "Type :? for help.")
      case stdlib of
           Nothing -> rec state
           Just lib -> do
             state' <- handleCommand @i @c state
               (Compile $ CompileFile lib)
             maybe (return ()) rec state'

interpretCommand :: Text -> IO Command
interpretCommand x
  =  if T.isPrefixOf ":" x then
       do  let  (cmd,t')  =  T.break isSpace x
                t         =  T.dropWhile isSpace t'
           --  find matching commands
           let  matching  =  LS.filter (\ (Cmd cs _ _ _) -> LS.any (T.isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Unknown command `" <> cmd <> "'. Type :? for help.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             x   ->  do  putStrLn ("Ambiguous command, could be " <> T.concat (LS.intersperse ", " [ LS.head cs | Cmd cs _ _ _ <- matching ]) <> ".")
                         return Noop
     else
       return (Compile (CompileInteractive x))

handleCommand :: forall i c v. Interpreter i c v
              => LangState v v -> Command -> IO (Maybe (LangState v v))
handleCommand state@(out, ve, te) cmd
  =  case cmd of
       Quit   ->  (putStrLn "!@#$^&*") >> return Nothing
       Noop   ->  return (Just state)
       Help   ->  putStr (helpTxt commands)
              >> return (Just state)
       TypeOf x ->
         do  x <- parseIO "<interactive>" (iiparse @i @c @v) x
             t <- maybe (return Nothing) (iinfer @i @c ve te) x
             maybe (return ())
                   (\u -> putStrLn (render (itprint @i @c u))) t
             return (Just state)
       Browse ->  do  putStr (T.unlines [ s | Global s <- LS.reverse (nub (fmap fst te)) ])
                      return (Just state)
       Compile c ->
         do state <- case c of
              CompileInteractive s -> compilePhrase @i @c state s
              CompileFile f        -> compileFile @i @c state f
            return (Just state)

compileFile :: forall i c v. Interpreter i c v
            => LangState v v -> Text -> IO (LangState v v)
compileFile state@(out, ve, te) f =
  do
    x <- readFile (unpack f)
    stmts <- parseIO f (many (isparse @i @c @v)) x
    maybe (return state) (foldM (handleStmt @i @c) state) stmts

compilePhrase :: forall i c v. Interpreter i c v
              => LangState v v -> Text -> IO (LangState v v)
compilePhrase state@(out, ve, te) input =
  do
    parsedInput <- parseIO "<interactive>" (isparse @i @c @v) input
    maybe (return state) (handleStmt @i @c state) parsedInput

iinfer :: forall i c v. Interpreter i c v
    => NameEnv v -> Ctx v -> i
    -> IO (Maybe v)
iinfer d g t =
  case iitype @i @c d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)

handleStmt :: forall i c v. Interpreter i c v
           => LangState v v
           -> Stmt i c
           -> IO (LangState v v)
handleStmt state@(out, ve, te) stmt =
    case stmt of
        Assume ass -> foldM (iassume @i) state ass
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (f, ve, te)
  where
    checkEval :: Interpreter i c v => Text -> i -> IO (LangState v v)
    checkEval i t =
      check @i @c (tshow . itprint @i @c @v) state i t
        (\ (y, v) -> do
          --  ugly, but we have limited space in the paper
          --  usually, you'd want to have the bound identifier *and*
          --  the result of evaluation
          let outtext = if i == it
              then render (icprint @i @c @v (iquote @i @c @v v) PP.<> text " :: " PP.<> itprint @i @c @v y)
              else render (text i PP.<> text " :: " PP.<> itprint @i @c @v y)
          putStrLn outtext
          unless (T.null out) (writeFile (unpack out) (process outtext)))
        (\ (y, v) -> ("",
            (Global i, v) : ve,
            (Global i, ihastype @i @c @v y) : te))

check :: forall i c v. Interpreter i c v
      => (v -> Text)
      -> LangState v v
      -> Text
      -> i
      -> ((v, v) -> IO ())
      -> ((v, v) -> LangState v v)
      -> IO (LangState v v)
check showt state@(out, ve, te) i t print k =
                do
                  -- i: Text, t: Type
                  --  typecheck and evaluate
                  x <- iinfer @i @c @v ve te t
                  case x of
                    Nothing  ->
                      do
                        return state
                    Just y   ->
                      do
                        let v = ieval @i @c @v ve t
                        print (y, v)
                        return (k (y, v))


it :: Text
it = "it"

process :: Text -> Text
process = T.unlines . fmap (\x -> "< " <> x) . T.lines
