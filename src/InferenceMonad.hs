-- | A monad for type/effect inference with enhanced error reporting
--
-- This module provides the InferenceM monad which tracks source location context
-- and provides rich error reporting capabilities for type inference operations.
module InferenceMonad (
  -- * Types
  InferenceError(..),
  InferenceContext(..),
  InferenceM(..),
  askRIO,
  asksRIO,
  localRIO,

  -- * Running inference
  runInferenceWithContext,

  -- * Context management
  withSourceContext,

  -- * Logging
  logValue,
  logPretty,
  logInfoM,
  logDebugM,
) where

import RIO
import qualified RIO.Text as Text
import Import
import Control.Monad.Trans.Except (ExceptT (..), mapExceptT, runExceptT, throwE)
import Control.Monad.Trans.Reader (ReaderT (..), local, mapReaderT, runReaderT)
import qualified Control.Monad.Trans.Reader as ReaderT
import Prettyprinter

-- | Enhanced error type that includes source position information
data InferenceError = InferenceError
  { errorMessage :: Text,
    errorSource :: Maybe Span,
    errorContext :: Text
  }
  deriving (Show, Eq, Ord)

-- | Inference context that tracks current source location
data InferenceContext = InferenceContext
  { currentSourceInfo :: Maybe Span
  , currentExpression :: Text  -- String representation of current expression
  }

-- | Context-aware inference monad
--
-- This monad provides:
-- * Automatic source location tracking
-- * Rich error reporting with context
-- * MonadFail instance for pattern match failures
newtype InferenceM a = InferenceM
  { runInferenceM :: ExceptT InferenceError (ReaderT InferenceContext (RIO RIOApp)) a
  }

instance Functor InferenceM where
  fmap f (InferenceM m) = InferenceM (fmap f m)

instance Applicative InferenceM where
  pure a = InferenceM (pure a)
  InferenceM f <*> InferenceM a = InferenceM (f <*> a)

instance Monad InferenceM where
  InferenceM m >>= f = InferenceM (m >>= (runInferenceM . f))

instance MonadFail InferenceM where
  fail msg = InferenceM $ do
    ctx <- lift RIO.ask
    throwE $ InferenceError (Text.pack msg) (currentSourceInfo ctx) (currentExpression ctx)

instance MonadIO InferenceM where
  liftIO io = InferenceM $ liftIO io

instance MonadReader InferenceContext InferenceM where
  ask = InferenceM $ lift ReaderT.ask
  local f (InferenceM m) = InferenceM $ mapExceptT (ReaderT.local f) m

askRIO :: InferenceM RIOApp
askRIO = InferenceM $ lift $ lift RIO.ask
asksRIO :: (RIOApp -> b) -> InferenceM b
asksRIO f = fmap f askRIO
localRIO :: (RIOApp -> RIOApp) -> InferenceM a -> InferenceM a
localRIO f (InferenceM m) = InferenceM $ mapExceptT (mapReaderT (RIO.local f)) m

instance Exception InferenceError where

-- | Run inference with an initial context
runInferenceWithContext :: Maybe Span -> Text -> InferenceM a -> RIO RIOApp (Either InferenceError a)
runInferenceWithContext srcInfo exprText (InferenceM m) =
  runReaderT (runExceptT m) (InferenceContext srcInfo exprText)

-- | Update the current context with new source information
withSourceContext :: Maybe Span -> Text -> InferenceM a -> InferenceM a
withSourceContext Nothing _exprText (InferenceM m) = InferenceM m
withSourceContext srcInfo exprText (InferenceM m) =
  InferenceM $ ExceptT $ ReaderT.local (const (InferenceContext srcInfo exprText)) (runExceptT m)

-- | Log a value with the current source context
logValue :: (HasCallStack, Show a) => a -> InferenceM ()
logValue val = logInfoM $ fromString $ show val

logPretty :: (HasCallStack, Pretty a) => a -> InferenceM ()
logPretty val = logInfoM $ fromString $ show $ pretty val

logInfoM :: HasCallStack => Utf8Builder -> InferenceM ()
logInfoM msg = InferenceM $ lift $ lift $ logInfo msg

logDebugM :: HasCallStack => Utf8Builder -> InferenceM ()
logDebugM msg = InferenceM $ lift $ lift $ logDebug msg
