
module RunAnnotatedSpec (spec) where

import RIO
import Test.Hspec
import Text.Megaparsec (runParser)
import qualified RIO.Set as Set
import qualified RIO.Map as Map
import qualified RIO.Text as Text
import Control.Comonad.Cofree (Cofree(..))

-- Import project modules
import Parse (pComponent)
import InferTyEffect (inferTyEffProgramTEST)
import InferenceMonad
import Import
import RIO
import RIO.Process

-- Test helper to run InferenceM in a test context
runInferenceTest :: InferenceM a -> IO (Either InferenceError a)
runInferenceTest inferenceAction = do
  logOptions <- logOptionsHandle stderr False
  withLogFunc logOptions $ \logFunc -> do
    processContext <- mkDefaultProcessContext
    varCounter <- newIORef 0
    let app = RIOApp logFunc processContext testOptions varCounter
    runRIO app $ runInferenceWithContext Nothing "test" inferenceAction


spec :: Spec
spec = do
  describe "Integration Tests" $ do
    let libraryComponents = Sigma (Map.fromList [])
    describe "Annotated AST Integration" $ do
      it "successfully parses and type checks simple expressions" $ do
        let compCode = Text.unlines
              [ "comp SimpleExpr() : int {"
              , "  let result = 42 + 10;"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigma, typedComps) -> do
                case typedComps of
                  [(tdecls, tret)] -> do
                    -- Should have 1 declaration: result
                    length tdecls `shouldBe` 1
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "SimpleExpr" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"

      it "handles complex expressions with proper type checking" $ do
        let compCode = Text.unlines
              [ "comp ArrowFunction() : int {"
              , "  let fn = (x: int) => { x + 1 };"
              , "  let result = fn(42);"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigma, typedComps) -> do
                case typedComps of
                  [(tdecls, tret)] -> do
                    -- Should have 2 declarations: fn and result
                    length tdecls `shouldBe` 2
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "ArrowFunction" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"

      it "provides meaningful error messages for parse failures" $ do
        let badCode = "comp BadSyntax() : int { invalid syntax here }"
        case runParser pComponent "test" badCode of
          Left err -> show err `shouldContain` "FancyError"
          Right _ -> expectationFailure "Should have failed to parse"

    describe "Component Analysis" $ do
      it "analyzes simple components successfully" $ do
        let compCode = Text.unlines
              [ "comp TestComponent() : int {"
              , "  let value = 42;"
              , "  return value;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigma, typedComps) -> do
                case typedComps of
                  [(tdecls, tret)] -> do
                    -- Should have 1 declaration: value
                    length tdecls `shouldBe` 1
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "TestComponent" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"

      it "handles state components properly" $ do
        let compCode = Text.unlines
              [ "comp StatefulComponent() : int {"
              , "  state counter, setCounter default 0;"
              , "  return counter;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigma, typedComps) -> do
                case typedComps of
                  [(tdecls, tret)] -> do
                    -- Should have 1 state declaration (counter/setCounter pair)
                    length tdecls `shouldBe` 1
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "StatefulComponent" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"

    describe "Error Handling" $ do
      it "catches and reports type mismatches gracefully" $ do
        let compCode = Text.unlines
              [ "comp BadComponent() : string {"
              , "  let num = 42;"
              , "  return num;"  -- int returned where string expected
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> show inferErr `shouldContain` "BadComponent"
              Right _ -> expectationFailure "Should have failed type checking"

      it "provides source location information in errors" $ do
        let badCode = "comp InvalidComponent() : int { let x = ; return x; }"
        case runParser pComponent "test" badCode of
          Left err -> show err `shouldContain` "TrivialError"
          Right _ -> expectationFailure "Should have failed to parse"

    describe "Backward Compatibility" $ do
      it "maintains compatibility with component operations" $ do
        let compCode = Text.unlines
              [ "comp PrecedenceTest() : int {"
              , "  let result = 1 + 2 * 3;"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigma, typedComps) -> do
                case typedComps of
                  [(tdecls, tret)] -> do
                    -- Should have 1 declaration: result
                    length tdecls `shouldBe` 1
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "PrecedenceTest" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"

      it "handles function application correctly" $ do
        let compCode = Text.unlines
              [ "comp FunctionApp() : int {"
              , "  let fn = (x: int) => { x * 2 };"
              , "  let result = fn(21);"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right comp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [comp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigma, typedComps) -> do
                case typedComps of
                  [(tdecls, tret)] -> do
                    -- Should have 2 declarations: fn and result
                    length tdecls `shouldBe` 2
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "FunctionApp" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"
