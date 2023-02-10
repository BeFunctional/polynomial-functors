{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.Logger where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (..), runReaderT, ask)

import Capability.Reader hiding (ask)
import qualified Capability.Reader as C (ask)

import Prelude hiding (putStrLn, putStr)

import Data.Kind (Type)
import Data.Text
import Data.Text.IO
import Data.IORef
import Data.Coerce (coerce)

import GHC.Generics

class Monad m => Logger m where
  logStr :: Text -> m ()
  logIn  :: Text -> m ()

-- ReaderT instance --------------------------------------------------

data LogCtx = LogCtx { logger :: (Text -> IO () , Text -> IO ()) }
  deriving Generic

printStdOut :: LogCtx
printStdOut = LogCtx { logger = (putStrLn, putStr) }

print2List :: IORef [Text] -> LogCtx
print2List ref = LogCtx ( \x -> modifyIORef ref (x :)
                        , \x -> modifyIORef ref (x :) )


-- | Any @HasReader "logger" (String -> IO ())@ can be a @Logger@.
newtype TheLoggerReader m a = TheLoggerReader (m a)
  deriving (Functor, Applicative, Monad)
instance
  (HasReader "logger" (Text -> IO (), Text -> IO ()) m, MonadIO m)
  => Logger (TheLoggerReader m)
  where
    logStr msg =
      coerce (C.ask @"logger" >>= liftIO . ($ msg) . fst :: m ())
    logIn msg =
      coerce (C.ask @"logger" >>= liftIO . ($ msg) . snd :: m ())
--
-- | Deriving @HasReader@ from @MonadReader@.
newtype LogM m (a :: Type) = LogM (ReaderT LogCtx m a)
  deriving (Functor, Applicative, Monad, MonadIO)
  deriving Logger via
    TheLoggerReader (Field "logger" () (MonadReader (ReaderT LogCtx m)))

runLogM :: LogCtx -> LogM m a -> m a
runLogM ctx (LogM m) = runReaderT m ctx
