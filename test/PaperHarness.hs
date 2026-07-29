-- | Shared harness for the paper-conformance test suites
-- (PaperRulesSpec and PaperExamplesSpec).
--
-- Every test references the rule/example IDs the paper uses, so a failing (or
-- newly passing) test maps directly back to a line in the paper.
--
-- Convention
-- ==========
--
-- * Tests for rules and examples are ordinary 'it' tests and must stay green.
--   That includes the event layer (@bind\/once\/cancel\/remove@, the
--   @□ ◇ ⊘ ✗@ modalities, event effects, and @event@ declarations / Σ_E).
-- * Tests for the sub-effecting judgement @F ≤ F′@: the relation is
--   implemented as the pure decision procedure @Analysis.Common.subEffect@,
--   which the SE-* tests call directly on hand-built effect trees. Inference
--   uses the relation as the purity predicate for T-STATE-DECL / T-LET-DECL
--   (see 'InferTyEffect.enforcePureStateDefault'); the T-ON-DECL causes check
--   is discharged by accumulation in the inferred-Δ prototype, so there is no
--   rejection to test.
module PaperHarness
  ( -- * Running inference
    runInferenceTest
  , inferSource
  , inferSourceEither
  , emptySigma
  , expectJust
    -- * Inspecting results
  , deltaOf
  , cascadeOf
  , depsOf
  , findLetExpr
  , findOnBlock
  , typedDeclsOf
  , typedReturnOf
    -- * Building expected effects
  , at
  , after1r
  , seqE
  , branchE
  ) where

import Import
import InferenceMonad
import InferTyEffect (inferTyEffProgramWithEventsTEST, buildSigmaE)
import Parse (pProgram)
import Test.Hspec (Expectation, expectationFailure)
import Text.Megaparsec (runParser)
import qualified RIO.Map as Map
import qualified RIO.Text as Text
import RIO.Process (mkDefaultProcessContext)
import Control.Comonad.Cofree (Cofree(..))

-- | Run an 'InferenceM' action in a fresh test context.
runInferenceTest :: InferenceM a -> IO (Either InferenceError a)
runInferenceTest inferenceAction = do
  logOptions <- logOptionsHandle stderr False
  withLogFunc logOptions $ \logFunc -> do
    processContext <- mkDefaultProcessContext
    varCounter <- newIORef 0
    let app = RIOApp logFunc processContext testOptions varCounter
    runRIO app $ runInferenceWithContext Nothing "test" inferenceAction

-- | Parse and type/effect-check a whole program source, failing the test on
-- either a parse error or an inference error.
inferSource :: Text -> IO (Sigma, [([AnnotatedDeclaration], AnnotatedNode)])
inferSource progCode = do
  result <- inferSourceEither progCode
  case result of
    Left inferErr -> expectationFailure ("Type inference failed: " <> show inferErr) >> error "unreachable"
    Right r -> pure r

-- | Like 'inferSource', but returns the inference result so negative tests
-- can assert that a program is rejected.
inferSourceEither :: Text -> IO (Either InferenceError (Sigma, [([AnnotatedDeclaration], AnnotatedNode)]))
inferSourceEither progCode =
  case runParser pProgram "test" progCode of
    Left err -> expectationFailure ("Parse failed: " <> show err) >> error "unreachable"
    Right (_ann :< ProgramF eventDecls comps) -> runInferenceTest $ do
      sigmaE <- buildSigmaE eventDecls
      inferTyEffProgramWithEventsTEST emptySigma sigmaE comps

-- | Unwrap a 'Maybe' or fail the test.
expectJust :: String -> Maybe a -> IO a
expectJust msg = maybe (expectationFailure msg >> error "unreachable") pure

-- | The 'Delta' (effect environment) inferred for a component.
deltaOf :: Sigma -> Text -> Delta
deltaOf (Sigma sigma) compName =
  case Map.lookup compName sigma of
    Just (SigmaEntry _ d) -> d
    Nothing -> error $ "deltaOf: component not in sigma: " <> Text.unpack compName

-- | The cascade effect recorded for a variable in a component's 'Delta'.
cascadeOf :: Sigma -> Text -> Text -> Effect
cascadeOf sigma compName var =
  case Map.lookup var (unDelta (deltaOf sigma compName)) of
    Just (DeltaEntry _ eff) -> eff
    Nothing -> error $ "cascadeOf: " <> Text.unpack var <> " not in " <> Text.unpack compName <> "'s delta"

-- | The dependency list recorded for a variable in a component's 'Delta'.
depsOf :: Sigma -> Text -> Text -> [Text]
depsOf sigma compName var =
  case Map.lookup var (unDelta (deltaOf sigma compName)) of
    Just (DeltaEntry deps _) -> deps
    Nothing -> error $ "depsOf: " <> Text.unpack var <> " not in " <> Text.unpack compName <> "'s delta"

-- | Find the typed expression bound by @let x = <expr>;@ in a component's
-- typed declarations.
findLetExpr :: Text -> [AnnotatedDeclaration] -> Maybe AnnotatedNode
findLetExpr name decls =
  listToMaybe [e | (_ :< DeclLetF v _ e) <- decls, v == name]

-- | Find the typed statements of the first @on … do { … }@ block watching
-- exactly the given dependencies.
findOnBlock :: [Text] -> [AnnotatedDeclaration] -> Maybe [AnnotatedNode]
findOnBlock deps decls =
  listToMaybe [es | (_ :< DeclEffectF ds (Block es)) <- decls, ds == deps]

-- | The typed declarations of the nth component (in source order).
typedDeclsOf :: [([AnnotatedDeclaration], AnnotatedNode)] -> Int -> [AnnotatedDeclaration]
typedDeclsOf typedComps ix =
  case drop ix typedComps of
    (decls, _) : _ -> decls
    [] -> error "typedDeclsOf: component index out of range"

-- | The typed return expression of the nth component (in source order).
typedReturnOf :: [([AnnotatedDeclaration], AnnotatedNode)] -> Int -> AnnotatedNode
typedReturnOf typedComps ix =
  case drop ix typedComps of
    (_, ret) : _ -> ret
    [] -> error "typedReturnOf: component index out of range"

-- | Short alias for a state-change effect (@x@).
at :: Text -> Effect
at = EffStateChange

-- | Short alias for the "after 1 render" delay.
after1r :: Effect -> Effect
after1r = EffAfter (Time 1 Renders)

-- | Build a sequence effect from a list (via 'mkEffSeq', like the parser does:
-- idempotent trees dedup, event effects and effect variables are kept).
seqE :: [Effect] -> Effect
seqE = mkEffSeq

-- | Build a branch effect.
branchE :: Effect -> Effect -> Effect
branchE = EffBranch
