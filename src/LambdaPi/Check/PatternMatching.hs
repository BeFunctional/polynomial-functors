module LambdaPi.Check.PatternMatching where

import Data.Bifunctor
import Data.Text (Text, unlines)
import Data.List

import LambdaPi.AST
import LambdaPi.Common
import LambdaPi.Quote
import LambdaPi.Printer

checkPatternMatching
     :: (CTerm -> Type -> Result ())
     -> (CTerm -> Value)
     -> ([(Name, Value)], Context)
     -> CTerm -> CTerm -> [(Text, CTerm)] -> Result Value
checkPatternMatching checkType eval context m s clauses = do
    let patterns = fmap fst clauses
    -- first we check that all patterns are the same type and we return it if successful
    sType <- checkAllPatterns context patterns
    checkPatternExhaustive context patterns sType

    -- This will give us enough information to check the type of the motive and the scrutinee
    checkType m (VPi sType (\_ -> VStar) )
    checkType s sType
    let mVal = eval m
    let sVal = eval s

    -- After that, we need to check all branches. For this we need to lookup the internal
    -- constructor associated with each identifier since they might not appear in the
    -- declaration order.
    mapM_ (\(con, branch) -> do
      constructorForId <- lookupCtx (fst context) con
      checkType branch (mVal `vapp` constructorForId)) (fmap (first Global) clauses)
    return (mVal `vapp` sVal)

checkPatternExhaustive :: ([(Name, Value)], Context) -> [Text] -> Value -> Result ()
checkPatternExhaustive ctx patterns scrutineeType = do
    constructors <- findAllConstructors
    case constructors \\ patterns of
      [] -> pure () -- if the difference between the constructors is empty, they are all here
      -- Otherwise, return the ones that are missing
      xs -> Left ("Non-exhaustive pattern match, missing:\n" <>
                  Data.Text.unlines (fmap (" - " <>) xs))
    where
    findAllConstructors :: Result [Text]
    findAllConstructors =
      let allConstructors = [n | (Global n, ty) <- snd ctx
                               , quote0 ty == quote0 scrutineeType ]
      in case allConstructors of
        [] -> Left ("No constructors founds for type " <> tshow scrutineeType)
        xs -> Right xs


-- Check that all patterns are the same type
checkAllPatterns :: ([(Name, Value)], Context) -> [Text] -> Result Value
checkAllPatterns (_, ctx) patterns = do
  types <- collectErrors $ fmap
             -- the patterns are just strings, we need to convert to global
             -- names but also pair the with what is the result of looking up
             -- their types in the context
             (\pat -> fmap (pat,) (lookupCtx ctx (Global pat)))
             patterns
  checkAllSame types
  where
      checkAllSame :: [(Text, Value)] -> Result Value
      checkAllSame [(_, tys)] = pure tys
      checkAllSame ((con, ty) : tys) = do
        getType <- checkAllSame tys
        if quote0 getType == quote0 ty
          then pure ty
          else Left ("constructor " <> con
            <> " does not match expected type "
            <> tshow (cPrint 0 0 (quote0 getType)))

