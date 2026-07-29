{-# OPTIONS_GHC -Wno-name-shadowing #-}

module ErrorDisplay (
  handleInferenceError,
  showErrorLocation
) where

import RIO
import qualified RIO.Text as Text
import Data.List ((!!))
import InferenceMonad (InferenceError(..))
import Import
import Prettyprinter
import Text.Megaparsec.Pos (unPos, sourceLine, sourceColumn)

-- | Handle structured inference errors with source location information
handleInferenceError :: Text -> InferenceError -> RIO RIOApp ()
handleInferenceError progStr inferErr = do
  logError $ fromString "\n====================\n Type/Effect Error \n===================="
  logError $ fromString $ Text.unpack (errorMessage inferErr)
  case errorSource inferErr of
    Just sp -> do
      showErrorLocation progStr sp
    Nothing -> logError "\nLocation: (no source location available)"
  let ctx = errorContext inferErr
  unless (Text.null ctx) $ do
    logError $ fromString "\nContext:"
    logError $ fromString $ "  " <> Text.unpack ctx

-- | Show error location in source code with context
showErrorLocation :: Text -> Span -> RIO RIOApp ()
showErrorLocation progStr span = do
  logError $ fromString $ "Location: " <> prettySpan span
  let sourceLines = Text.lines progStr
      lineNum = unPos $ sourceLine $ spanStart span
      colNum = unPos $ sourceColumn $ spanStart span
      startLine = max 1 (lineNum - 3)
      endLine = min (length sourceLines) (lineNum + 3)
      -- 1-based to 0-based for list indexing
      contextLines = zip [startLine..endLine] $ take (endLine - startLine + 1) $ drop (startLine - 1) sourceLines
  forM_ contextLines $ \(ln, line) ->
    if ln == lineNum
      then do
        logError $ fromString $ "> " <> show ln <> ": " <> Text.unpack line
        let pointer = replicate (colNum - 1 + 4 + 2) ' '
              <> replicate ((unPos (sourceColumn (spanEnd span)) - unPos (sourceColumn (spanStart span)) - 1) `max` 1) '^'
        logError $ fromString pointer
      else
        logError $ fromString $ "  " <> show ln <> ": " <> Text.unpack line
