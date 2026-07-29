{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant case" #-}
module Run (run) where

import Import
import Parse (pProgram)
import InferTyEffect (inferTyEffProgram)
import InferenceMonad (InferenceError(..))
import Control.Comonad.Cofree (Cofree(..))

import qualified RIO.Map as Map
import qualified RIO.Text as Text
import RIO.List (sort)
import qualified RIO.List as List
import Text.Megaparsec (runParser, errorBundlePretty, ParseErrorBundle)
import Text.Megaparsec.Pos (unPos, sourceLine, sourceColumn)
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import qualified System.Directory as Dir
import qualified System.FilePath as FP
import qualified Control.Exception as Ex
import ErrorDisplay (handleInferenceError, showErrorLocation)
import Analysis

-- | Emit one line of the report on stdout.
--
-- Willow keeps its two streams apart. The report proper — the usage listing,
-- the Σ table, the per-variable effects, and the @--first@/@--cleanup@
-- analyses — goes to stdout, so it can be redirected, diffed or piped.
-- Progress chatter, the @-v@ AST dump, and every diagnostic go to stderr
-- through the RIO log functions (see 'Main.main', which points the log func at
-- stderr). Discarding stderr therefore leaves exactly the report, and a
-- program that fails to check writes nothing to stdout at all.
--
-- The warning lines the analyses produce (@⚠️  never settles@, @⚠️  … handler
-- left behind@) are report content rather than diagnostics, so they stay on
-- stdout with the headings they belong under.
--
-- Bytes go out through 'hPutBuilder', which encodes as UTF-8 itself rather
-- than deferring to the handle — a second line of defence for the report's
-- glyphs alongside the 'System.IO.hSetEncoding' calls in 'Main.main'.
out :: MonadIO m => Text -> m ()
out t = hPutBuilder stdout (getUtf8Builder (display t <> "\n"))

-- | 'out' for a pretty-printable value, laid out for an 80-column terminal.
-- 'show' on a 'Doc' would use the library's default 0.4 ribbon fraction, which
-- makes it give up on anything already indented — the effect tables are.
outValue :: (MonadIO m, Pretty a) => a -> m ()
outValue = out . renderPretty

-- | 'outValue', but onto the diagnostic stream — used for the @-v@ AST dump.
logValue :: (MonadIO m, MonadReader env m, HasLogFunc env, Pretty a) => a -> m ()
logValue = logInfo . display . renderPretty

renderPretty :: Pretty a => a -> Text
renderPretty x =
  renderStrict $ layoutPretty (LayoutOptions (AvailablePerLine 80 1.0)) (pretty x)

run :: RIO RIOApp ()
run = do
  Options {optionsInputFile} <- appOptions <$> ask
  maybe printUsage processInputFile optionsInputFile

-- | Process a single input file specified by the user
processInputFile :: FilePath -> RIO RIOApp ()
processInputFile file = do
  logInfo "=== Willow: a type-and-effect checker for React timing ==="
  logInfo $ fromString $ "Analyzing file: " <> file
  fileExists <- liftIO $ Dir.doesFileExist file
  if fileExists
    then do
      content <- liftIO $ readFileUtf8 file
      analyzeProgram file content
    else do
      logError $ fromString $ "File not found: " <> file
      exitFailure

-- | With no input file, print usage and list the worked examples from the paper.
printUsage :: RIO RIOApp ()
printUsage = do
  out "Willow — a type-and-effect checker for React timing"
  out ""
  out "Usage: willow-hs-exe [-v|--verbose] [--first] [--cleanup] FILE"
  out ""
  out "  Analyze a Willow program and report the inferred type-and-effect of"
  out "  each component (state changes, render/network delays, cascades, loops)."
  out ""
  out "  --first    also show the initial-render analysis"
  out "  --cleanup  also check that every event handler is removed again"
  out "  -v         verbose (dumps the parsed AST)"
  out ""
  let paperDir = "examples" FP.</> "paper"
  exists <- liftIO $ Dir.doesDirectoryExist paperDir
  if exists
    then do
      files <- liftIO $ Dir.listDirectory paperDir
      let paperExamples = sort [ paperDir FP.</> f | f <- files, ".txt" `Text.isSuffixOf` Text.pack f ]
      out "Worked examples from the paper (run any of these):"
      forM_ paperExamples $ \p -> out $ Text.pack $ "  willow-hs-exe " <> p
    else out "  (run `willow-hs-exe examples/paper/MovingDot.txt` to try an example)"

analyzeProgram :: FilePath -> Text -> RIO RIOApp ()
analyzeProgram filename progStr = do
  logInfo "Parsing program with annotated AST..."
  case runParser pProgram filename progStr of
    Left err -> handleParseError err >> exitFailure
    Right prog -> handleSuccessfulParse progStr prog

-- | Handle parsing errors with detailed error reporting
handleParseError :: ParseErrorBundle Text Void -> RIO RIOApp ()
handleParseError err = do
  logError $ fromString "PARSE ERROR with source info:"
  logError $ fromString $ errorBundlePretty err

-- | Handle successful parsing and proceed with type checking
handleSuccessfulParse :: Text -> AnnotatedProgram -> RIO RIOApp ()
handleSuccessfulParse progStr prog = do
  Options{optionsVerbose} <- appOptions <$> ask
  when optionsVerbose $ logValue prog
  let comps = getComponents prog
  case comps of
    [] -> logInfo "Empty program"
    _ -> performTypeChecking progStr prog

-- | Perform type checking and effect inference with error handling
performTypeChecking :: Text -> AnnotatedProgram -> RIO RIOApp ()
performTypeChecking _progStr prog = do
  logInfo "Typechecking and inferring effects..."
  result <- tryAny $ inferTyEffProgram emptySigma prog
  case result of
    Left ex -> do
      -- An 'InferenceError' means the program does not check, and
      -- 'inferTyEffProgram' has already rendered it against the source — there
      -- is nothing to add. Any other exception is the checker itself falling
      -- over, which is worth saying out loud. Either way the run has failed.
      case Ex.fromException ex of
        Just (_ :: InferenceError) -> pure ()
        Nothing -> logError $ fromString $
          "Internal error (not a type/effect error): " <> displayException ex
      exitFailure
    Right (sigmaFinal, _typedComps) ->
      handleInferenceSuccess prog sigmaFinal

-- | Handle successful type inference and display results
handleInferenceSuccess :: Program -> Sigma -> RIO RIOApp ()
handleInferenceSuccess _prog sigmaFinal = do
  logInfo "\n✓ Type checking successful with annotated AST!"
  out "--- Component Summary (Sigma) ---"
  outValue sigmaFinal
  out ""
  Options
    { optionsInitialRenderAnalysis
    , optionsHandlerCleanupAnalysis } <- appOptions <$> ask
  displayMainComponentEffects sigmaFinal
  when optionsInitialRenderAnalysis $ displayInitialRenderEffects sigmaFinal
  when optionsHandlerCleanupAnalysis $ displayHandlerCleanup sigmaFinal

-- | Display effects for the main component's arguments
displayMainComponentEffects :: Sigma -> RIO RIOApp ()
displayMainComponentEffects sigmaFinal = do
  let (Sigma sigma) = sigmaFinal
  case Map.toList sigma of
    [] -> pure ()
    pairs -> forM_ pairs $ \(mainComp, SigmaEntry (_ :< ComponentF _ _ _ _ _ _) (Delta delta)) -> do
      out $ "--- Effects for " <> mainComp <> " ---"
      displayAllEffects delta

-- | Width the effect trees are wrapped to, before the leading indent below is
-- added. Kept a little under 80 so the indented result still fits a terminal.
effectWidth :: Int
effectWidth = 72

displayAllEffects :: Map Text DeltaEntry -> RIO RIOApp ()
displayAllEffects delta = do
  forM_ (filter (not . isCompilerVar) (Map.keys delta)) $ \x -> do
    let fullEff = simplifyEffect (fullEffectVar (Delta delta) x)
    let relevantEff = simplifyEffect (relevantEffect fullEff)
    unless (fullEff == EffNone) $ do
      out $ "  on " <> x <> ":"
      out $ indentBlock 6 (renderEffect effectWidth relevantEff)
      -- The full effect additionally names sub-component-internal state
      -- (`slowUsername.slow` and friends), which 'relevantEffect' drops.
      unless (fullEff == relevantEff) $ do
        out "    including sub-component state:"
        out $ indentBlock 6 (renderEffect effectWidth fullEff)
      out ""

-- | Report, per component and per bound variable, whether every event handler
-- the variable's full effect registers is matched by a @remove@ (paper §5.4).
displayHandlerCleanup :: Sigma -> RIO RIOApp ()
displayHandlerCleanup (Sigma sigma) = do
  out ""
  out "=== Event Handler Cleanup Analysis ==="
  forM_ (Map.toList sigma) $ \(compName, SigmaEntry _ delta) -> do
    out $ "comp " <> compName
    let reports = checkComponentCleanup delta
    if null reports
      then out "  no event handlers registered"
      else forM_ reports $ \(x, report) -> do
        out $ "  on " <> x <> ":"
        forM_ (crHandlers report) $ \h ->
          case List.find (matches h) (crStale report) of
            Nothing -> out $ "    ✓ " <> describeHandler h <> " — cleaned up"
            Just sh -> out $ "    ⚠️  " <> describeStaleHandler sh
  where
    matches (lbl, kind) sh = staleLabel sh == lbl && staleKind sh == kind

-- | Report, per component, what mounting does: the effects that settle, the
-- handlers left armed, and the events already scheduled when mount is over.
displayInitialRenderEffects :: Sigma -> RIO RIOApp ()
displayInitialRenderEffects (Sigma sigma) = do
  out ""
  out "=== Initial Render Analysis ==="
  forM_ (Map.toList sigma) $ \(compName, SigmaEntry comp delta) ->
    displayComponentInitialRender compName comp delta

-- | Display the mount analysis for a single component.
displayComponentInitialRender :: Text -> Component -> Delta -> RIO RIOApp ()
displayComponentInitialRender compName comp delta = do
  out $ "comp " <> compName
  let info = analyzeComponentInitialRender delta comp
      settling = simplifyEffect (relevantEffect (iriSettling info))
      loops = iriLoops info

  if settling == EffNone
    then out "  settles: nothing (no state changes on mount)"
    else do
      out "  settles:"
      out $ indentBlock 6 (renderEffect effectWidth settling)

  if null loops
    then unless (settling == EffNone) $
      out $ "  settle time: " <> describeSettleTime (iriSettleTime info)
    else
      out $
        (if iriAlwaysLoops info
           then "  ⚠️  never settles — loops through "
           else "  ⚠️  may not settle — loops through ")
          <> Text.intercalate ", " loops
          <> (if iriAlwaysLoops info then "" else " on some branches")

  forM_ (nonEmpty (iriArmed info)) $ \armed -> do
    out "  arms:"
    forM_ armed $ \h ->
      out $ "    " <> describeHandler h <> " — body waits for the event"

  forM_ (nonEmpty (iriScheduled info)) $ \scheduled -> do
    out "  schedules:"
    forM_ scheduled $ \(lbl, delays) ->
      out $
        "    " <> renderCompact lbl
          <> " after " <> Text.intercalate " or " (map describeSettleTime delays)
          <> " — fires with no user interaction"
  out ""
  where
    nonEmpty xs = if null xs then Nothing else Just xs
    renderCompact = renderStrict . layoutCompact . pretty

