{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Import
import Run
import RIO.Process
import Options.Applicative.Simple
import System.IO (hSetEncoding, utf8)
import qualified Paths_willow_hs

main :: IO ()
main = do
  (options, ()) <- simpleOptions
    $(simpleVersion Paths_willow_hs.version)
    "Willow — a type-and-effect checker for React timing"
    "Parse a Willow program and report the inferred type-and-effect of each component. Pass a FILE to analyze it; with no FILE, prints usage and the available examples."
    (Options
       <$> switch ( long "verbose"
                 <> short 'v'
                 <> help "Verbose output (dumps the parsed AST)"
                  )
       <*> switch ( long "first"
                 <> help "Show initial-render analysis"
                  )
       <*> switch ( long "cleanup"
                 <> help "Show event-handler cleanup analysis (stale listeners)"
                  )
       <*> optional (argument str (metavar "FILE" <> help "Willow program to analyze"))
    )
    empty
  -- Both streams carry non-ASCII — the report is full of ✓, ⚠️, ○ and —, and
  -- so is the progress chatter. Pin them to UTF-8 rather than trusting the
  -- ambient locale: with LANG unset or LANG=C the default encoding cannot
  -- represent those characters and the first one written kills the process
  -- with "hPutChar: invalid argument (cannot encode character)".
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  -- The report goes to stdout and the diagnostics to stderr (see 'Run.out').
  -- Line-buffering stdout keeps the two interleaved in the order they were
  -- written when both land on a terminal, or in the same redirected file.
  hSetBuffering stdout LineBuffering
  lo <- logOptionsHandle stderr (optionsVerbose options)
  pc <- mkDefaultProcessContext
  varCounter <- newIORef 0
  withLogFunc lo $ \lf ->
    let app = RIOApp
          { appLogFunc = lf
          , appProcessContext = pc
          , appOptions = options
          , appVarCounter = varCounter
          }
     in runRIO app run
