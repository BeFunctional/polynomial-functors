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

data Command = TypeOf Text
             | Compile CompileForm
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  Text
                 | CompileFile         Text

data InteractiveCommand = Cmd [Text] Text (Text -> Command) Text

type Ctx inf = [(Name, inf)]
type State v inf = (Text, NameEnv v, Ctx inf)

data Interpreter i c v t tinf inf =
  I { iname :: Text,
      iprompt :: Text,
      iitype :: NameEnv v -> Ctx inf -> i -> Result t,
      iquote :: v -> c,
      ieval  :: NameEnv v -> i -> v,
      ihastype :: t -> inf,
      icprint :: c -> Doc,
      itprint :: t -> Doc,
      iiparse :: Parsec Text () i,
      isparse :: Parsec Text () (Stmt i tinf),
      iassume :: State v inf -> (Text, tinf) -> IO (State v inf) }

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


readevalprint :: Maybe Text -> Interpreter i c v t tinf inf -> State v inf -> IO ()
readevalprint stdlib int state@(out, ve, te) =
  let rec int state =
        do
          putStr (iprompt int)
          hFlush stdout
          x <- catchIOError (fmap Just getLine) (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->
              rec int state
            Just x    ->
              do
                c  <- interpretCommand x
                state' <- handleCommand int state c
                maybe (return ()) (rec int) state'
  in
    do
      --  welcome
      putStrLn ("Interpreter for " <> iname int <> ".\n" <>
                             "Type :? for help.")
      case stdlib of
           Nothing -> rec int state
           Just lib -> do
             state' <- handleCommand int state (Compile $ CompileFile lib)
             maybe (return ()) (rec int) state'

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

handleCommand :: Interpreter i c v t tinf inf -> State v inf -> Command -> IO (Maybe (State v inf))
handleCommand int state@(out, ve, te) cmd
  =  case cmd of
       Quit   ->  (putStrLn "!@#$^&*") >> return Nothing
       Noop   ->  return (Just state)
       Help   ->  putStr (helpTxt commands) >> return (Just state)
       TypeOf x ->
                  do  x <- parseIO "<interactive>" (iiparse int) x
                      t <- maybe (return Nothing) (iinfer int ve te) x
                      maybe (return ()) (\u -> putStrLn (render (itprint int u))) t
                      return (Just state)
       Browse ->  do  putStr (T.unlines [ s | Global s <- LS.reverse (nub (fmap fst te)) ])
                      return (Just state)
       Compile c ->
                  do  state <- case c of
                                 CompileInteractive s -> compilePhrase int state s
                                 CompileFile f        -> compileFile int state f
                      return (Just state)

compileFile :: Interpreter i c v t tinf inf -> State v inf -> Text -> IO (State v inf)
compileFile int state@(out, ve, te) f =
  do
    x <- readFile (unpack f)
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts

compilePhrase :: Interpreter i c v t tinf inf -> State v inf -> Text -> IO (State v inf)
compilePhrase int state@(out, ve, te) x =
  do
    x <- parseIO "<interactive>" (isparse int) x
    maybe (return state) (handleStmt int state) x


iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)

handleStmt :: Interpreter i c v t tinf inf
           -> State v inf -> Stmt i tinf -> IO (State v inf)
handleStmt int state@(out, ve, te) stmt =
    case stmt of
        Assume ass -> foldM (iassume int) state ass
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (f, ve, te)
  where
    --  checkEval :: Text -> i -> IO (State v inf)
    checkEval i t =
      check int (tshow . itprint int) state i t
        (\ (y, v) -> do
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = if i == it then render (icprint int (iquote int v) PP.<> text " :: " PP.<> itprint int y)
                                                else render (text i PP.<> text " :: " PP.<> itprint int y)
                       putStrLn outtext
                       unless (T.null out) (writeFile (unpack out) (process outtext)))
        (\ (y, v) -> ("", (Global i, v) : ve, (Global i, ihastype int y) : te))

check :: Interpreter i c v t tinf inf -> (t -> Text) -> State v inf -> Text -> i
         -> ((t, v) -> IO ()) ->  ((t, v) -> State v inf) -> IO (State v inf)
check int showt state@(out, ve, te) i t print k =
                do
                  -- i: Text, t: Type
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        return state
                    Just y   ->
                      do
                        let v = ieval int ve t
                        print (y, v)
                        return (k (y, v))


it :: Text
it = "it"

process :: Text -> Text
process = T.unlines . fmap (\x -> "< " <> x) . T.lines
