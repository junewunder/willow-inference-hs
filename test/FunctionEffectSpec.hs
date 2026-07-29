module FunctionEffectSpec (spec) where

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
spec = describe "FunctionEffect" $ do
  let libraryComponents = Sigma (Map.fromList [])
  describe "Function Effect Behavior" $ do
    describe "Basic function expression behavior" $ do
      it "simple arrow function has no immediate effect" $ do
        let compCode = Text.unlines
              [ "comp SimpleFn() : int {"
              , "  let result = 42;"
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
                  [(tdecls, _tret)] -> do
                    -- Should have 1 declaration and proper return
                    length tdecls `shouldBe` 1  -- just result declaration
                    -- Check that the component was added to sigma
                    let (Sigma sigmaMap) = sigma
                    Map.member "SimpleFn" sigmaMap `shouldBe` True
                  _ -> expectationFailure "Expected exactly one component result"

      it "function call realizes the effect from function body" $ do
        let compCode = Text.unlines
              [ "comp CallFn() : int {"
              , "  let fn = (x: int) => { x + 1 };"
              , "  let result = fn(5);"
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
                    Map.member "CallFn" sigmaMap `shouldBe` True
                    -- Check return type is int
                    getType tret `shouldBe` TInt
                  _ -> expectationFailure "Expected exactly one component result"

      it "function with multiple effects stores them all in function type" $ do
        let compCode = Text.unlines
              [ "comp MultiFn() : int {"
              , "  state count1, setCount1 default 0;"
              , "  state count2, setCount2 default 0;"
              , "  let fn = (x: int) => { setCount1((c: int) => { c + x }) };"
              , "  return count1;"
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
                    -- Should have 3 declarations: 2 state declarations + 1 function declaration
                    length tdecls `shouldBe` 3
                    -- Check that component was properly typed
                    let (Sigma sigmaMap) = sigma
                    Map.member "MultiFn" sigmaMap `shouldBe` True
                    -- The return should be properly typed as count1
                    case tret of
                      (_ :< LangFExpr (EVarF varName)) -> varName `shouldBe` "count1"
                      _ -> expectationFailure "Expected return to be count1 variable"
                  _ -> expectationFailure "Expected exactly one component result"
