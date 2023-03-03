module LambdaPi.Check.PatternMatching where

import Data.Bifunctor
import Data.Text (Text)

import LambdaPi.AST
import LambdaPi.Common
import LambdaPi.Quote

checkPatternMatching
     :: (CTerm -> Type -> Result ())
     -> (CTerm -> Value)
     -> (NameEnv Value, Context)
     -> CTerm -> CTerm -> [(Text, CTerm)] -> Result Value
checkPatternMatching checkType eval context m s p = do
    -- first we check that all patterns are the same type and we return it if successful
    sType <- checkAllPatterns context (fmap fst p)

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
      checkType branch (mVal `vapp` constructorForId)) (fmap (first Global) p)
    return (mVal `vapp` sVal)


-- we also need to check patterns are exhaustive
checkAllPatterns :: (NameEnv Value, Context) -> [Text] -> Result Value
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
          else Left ("constuctor " <> con
            <> " does not match type "
            <> tshow (quote0 getType))

