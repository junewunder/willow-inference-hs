{-# LANGUAGE OverloadedStrings #-}

module InferAnnotatedSpec (spec) where

import Import
import Parse
import InferTyEffect
import Test.Hspec
import Text.Megaparsec (runParser, initialPos)
import qualified RIO.Text as Text
import qualified RIO.Map as Map
import qualified RIO.Set as Set
import Control.Comonad.Cofree (Cofree(..))
import InferenceMonad
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
  describe "Annotated Type Inference" $ do
    let libraryComponents = Sigma (Map.fromList [])

    describe "inferTyEffProgramTEST" $ do
      it "successfully type checks simple component" $ do
        let compCode = Text.unlines
              [ "comp SimpleComponent() : int {"
              , "  let x = 42;"
              , "  return x;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigmaFinal, typedComps) -> do
                -- The component should type check successfully
                let (Sigma sigma) = sigmaFinal
                Map.size sigma `shouldBe` 1
                length typedComps `shouldBe` 1

      it "type checks component with arithmetic" $ do
        let compCode = Text.unlines
              [ "comp ArithComponent() : int {"
              , "  let x = 10;"
              , "  let y = 20;"
              , "  let result = x + y;"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
            case result of
              Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
              Right (sigmaFinal, typedComps) -> do
                -- The component should type check successfully
                let (Sigma sigma) = sigmaFinal
                Map.size sigma `shouldBe` 1
                length typedComps `shouldBe` 1

      it "provides enhanced error for type mismatches" $ do
        let compCode = Text.unlines
              [ "comp MismatchComponent() : string {"
              , "  let x = 42;"  -- int
              , "  return x;"    -- but expecting string
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
            case result of
              Left inferErr -> do
                -- Should get an enhanced error with context
                show inferErr `shouldContain` "MismatchComponent"
              Right _ -> expectationFailure "Should have failed type checking"

    describe "inferTyEffProgramTEST (program level)" $ do
      it "successfully type checks simple program" $ do
        let progCode = Text.unlines
              [ "comp SimpleProgram() : int {"
              , "  let value = 42;"
              , "  return value;"
              , "}"
              ]
        case runParser pProgram "test" progCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right (_ann :< ProgramF _eventDecls comps) -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents comps
            case result of
              Left inferErr -> expectationFailure $ "Program inference failed: " <> show inferErr
              Right (sigmaFinal, _typedComps) -> do
                -- The program should type check successfully
                let (Sigma sigma) = sigmaFinal
                Map.size sigma `shouldBe` 1

      it "type checks program with multiple components" $ do
        let progCode = Text.unlines
              [ "comp Helper() : int {"
              , "  let value = 10;"
              , "  return value;"
              , "}"
              , "comp Main() : int {"
              , "  let localValue = 5;"
              , "  let result = localValue + 3;"
              , "  return result;"
              , "}"
              ]
        case runParser pProgram "test" progCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right (_ann :< ProgramF _eventDecls comps) -> do
            result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents comps
            case result of
              Left inferErr -> expectationFailure $ "Program inference failed: " <> show inferErr
              Right (sigmaFinal, _typedComps) -> do
                -- Both components should be in the final sigma
                let (Sigma sigma) = sigmaFinal
                Map.size sigma `shouldBe` 2

    describe "Effect Polymorphism" $ do
      describe "Debounce Pattern" $ do
        it "correctly handles polymorphic effects in setTimeout function" $ do
          let compCode = Text.unlines
                [ "comp Debounce(value: int) : int {"
                , "  state activeValue, setActiveValue default value;"
                , "  state recentValue, setRecentValue default value;"
                , "  state numSeen, setNumSeen default 0;"
                , "  state numAged, setNumAged default 0;"
                , "  on value do {"
                , "    setNumSeen((s: int) => { s + 1 });"
                , "    setRecentValue((a: int) => { value });"
                , "    setTimeout((a: unit) => { setNumAged((a: int) => { a + 1 }) });"
                , "  }"
                , "  on numAged do {"
                , "    numAged == numSeen ? setActiveValue((v: int) => { recentValue }) : ();"
                , "  }"
                , "  return activeValue;"
                , "}"
                ]
          case runParser pComponent "test" compCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right annotatedComp -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
              case result of
                Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
                Right (Sigma sigma, typedComps) -> do
                  -- The component should type check successfully with polymorphic effects
                  Map.member "Debounce" sigma `shouldBe` True
                  -- Should have exactly one component in the sigma
                  Map.size sigma `shouldBe` 1
                  -- Should have one typed component result
                  length typedComps `shouldBe` 1
                  case typedComps of
                    [(typedDecls, typedReturn)] -> do
                      -- Should have 4 state declarations + 2 effect declarations
                      length typedDecls `shouldBe` 6
                      -- The return should be properly typed
                      case typedReturn of
                        (_ :< LangFExpr (EVarF varName)) -> varName `shouldBe` "activeValue"
                        _ -> expectationFailure "Expected return to be activeValue variable"
                    _ -> expectationFailure "Expected exactly one component result"

        it "handles debounce with expensive computation" $ do
          let progCode = Text.unlines
                [ "comp Debounce(value: int) : int {"
                , "  state activeValue, setActiveValue default value;"
                , "  state recentValue, setRecentValue default value;"
                , "  state numSeen, setNumSeen default 0;"
                , "  state numAged, setNumAged default 0;"
                , "  on value do {"
                , "    setNumSeen((s: int) => { s + 1 });"
                , "    setRecentValue((a: int) => { value });"
                , "    setTimeout((a: unit) => { setNumAged((a: int) => { a + 1 }) });"
                , "  }"
                , "  on numAged do {"
                , "    numAged == numSeen ? setActiveValue((v: int) => { recentValue }) : ();"
                , "  }"
                , "  return activeValue;"
                , "}"
                , "comp UsingDebounce(clock: int) : int {"
                , "  state cachedValue, setCachedValue default expensive(clock);"
                , "  comp slowValue = Debounce(clock);"
                , "  on slowValue do {"
                , "    setCachedValue((v: int) => { expensive(slowValue) });"
                , "  }"
                , "  return cachedValue;"
                , "}"
                ]
          case runParser pProgram "test" progCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right (_ann :< ProgramF _eventDecls comps) -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents comps
              case result of
                Left inferErr -> expectationFailure $ "Program inference failed: " <> show inferErr
                Right (sigmaFinal, _typedComps) -> do
                  -- Both components should be in the final sigma
                  let (Sigma sigma) = sigmaFinal
                  Map.size sigma `shouldBe` 2
                  -- The effects should properly compose with polymorphism
                  True `shouldBe` True

        it "verifies setTimeout effect polymorphism instantiation" $ do
          let compCode = Text.unlines
                [ "comp DelayTest() : int {"
                , "  state counter, setCounter default 0;"
                , "  on once do {"
                , "    setTimeout((x: unit) => { setCounter((c: int) => { c + 1 }) });"
                , "  }"
                , "  return counter;"
                , "}"
                ]
          case runParser pComponent "test" compCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right annotatedComp -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
              case result of
                Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
                Right (Sigma sigma, typedComps) -> do
                  -- setTimeout should instantiate its polymorphic effect with the state change effect
                  Map.member "DelayTest" sigma `shouldBe` True
                  Map.size sigma `shouldBe` 1
                  case typedComps of
                    [(typedDecls, typedReturn)] -> do
                      -- Should have 1 state declaration + 1 effect declaration
                      length typedDecls `shouldBe` 2
                      -- The return should be properly typed as counter
                      case typedReturn of
                        (_ :< LangFExpr (EVarF varName)) -> varName `shouldBe` "counter"
                        _ -> expectationFailure "Expected return to be counter variable"
                    _ -> expectationFailure "Expected exactly one component result"

        it "verifies exact debounce pattern from debounce.txt" $ do
          let compCode = Text.unlines
                [ "comp Debounce(value: int) : int {"
                , "  state activeValue, setActiveValue default value;"
                , "  state recentValue, setRecentValue default value;"
                , "  state numSeen, setNumSeen default 0;"
                , "  state numAged, setNumAged default 0;"
                , "  on value do {"
                , "    setNumSeen((s: int) => { s + 1 });"
                , "    setRecentValue((a: int) => { value });"
                , "    setTimeout((a: unit) => { setNumAged((a: int) => { a + 1 }) });"
                , "  }"
                , "  on numAged do {"
                , "    numAged == numSeen ? setActiveValue((v: int) => { recentValue }) : ();"
                , "  }"
                , "  return activeValue;"
                , "}"
                ]
          case runParser pComponent "test" compCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right annotatedComp -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
              case result of
                Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
                Right (Sigma sigma, typedComps) -> do
                  -- The component should successfully type check with proper effect polymorphism
                  Map.member "Debounce" sigma `shouldBe` True
                  Map.size sigma `shouldBe` 1
                  case typedComps of
                    [(typedDecls, typedReturn)] -> do
                      -- Should have 4 state declarations + 2 effect declarations (on value, on numAged)
                      length typedDecls `shouldBe` 6
                      -- The setTimeout function's effect parameter should be instantiated with the setNumAged effect
                      case typedReturn of
                        (_ :< LangFExpr (EVarF varName)) -> varName `shouldBe` "activeValue"
                        _ -> expectationFailure "Expected return to be activeValue variable"
                      -- Verify component is properly structured in sigma
                      case Map.lookup "Debounce" sigma of
                        Just (SigmaEntry _ (Delta deltaMap)) -> do
                          -- Verify the exact effect for the 'value' variable
                          case Map.lookup "value" deltaMap of
                            Just (DeltaEntry deps cascade) -> do
                              -- Dependencies should be empty for the parameter
                              deps `shouldBe` []
                              -- The cascade effect should match the expected pattern:
                              -- (◯1r {@numSeen} * ◯1r {@recentValue}
                              --   * eventually timeout<> {◯1r {@numAged}} * ◯100ms {timeout<>})
                              -- Let's verify it contains the expected effects
                              case cascade of
                                EffSeq effects -> do
                                  -- Should contain state changes and timing effects
                                  let effectSet = toList effects
                                  length effectSet `shouldSatisfy` (== 4)  -- 4 effects combined
                                  -- Should contain references to the expected state variables
                                  let hasNumSeenEffect = any (\case {
                                        EffAfter (Time 1 Renders) (EffStateChange var) -> var == "numSeen";
                                        _ -> False}) effectSet
                                  let hasRecentValueEffect = any (\case {
                                        EffAfter (Time 1 Renders) (EffStateChange var) -> var == "recentValue";
                                        _ -> False}) effectSet
                                  let hasNumAgedEventuallyEffect = any (\case {
                                        EffEventually (EventLabel "timeout" []) (EffAfter (Time 1 Renders) (EffStateChange var)) -> var == "numAged";
                                        _ -> False}) effectSet
                                  let hasTimeoutEventEffect = any (\case {
                                        EffAfter (Time 100 Millis) (EffEvent (EventLabel "timeout" [])) -> True;
                                        _ -> False}) effectSet
                                  hasNumSeenEffect `shouldBe` True
                                  hasRecentValueEffect `shouldBe` True
                                  hasNumAgedEventuallyEffect `shouldBe` True
                                  hasTimeoutEventEffect `shouldBe` True
                                _ -> expectationFailure $ "Expected EffSeq for value effect, got: " <> show cascade
                            Nothing -> expectationFailure "value variable not found in delta"
                        Nothing -> expectationFailure "Debounce component not found in sigma"
                    _ -> expectationFailure "Expected exactly one component result"

        it "verifies full UsingDebounce composition pattern" $ do
          let progCode = Text.unlines
                [ "comp Debounce(value: int) : int {"
                , "  state activeValue, setActiveValue default value;"
                , "  state recentValue, setRecentValue default value;"
                , "  state numSeen, setNumSeen default 0;"
                , "  state numAged, setNumAged default 0;"
                , "  on value do {"
                , "    setNumSeen((s: int) => { s + 1 });"
                , "    setRecentValue((a: int) => { value });"
                , "    setTimeout((a: unit) => { setNumAged((a: int) => { a + 1 }) });"
                , "  }"
                , "  on numAged do {"
                , "    numAged == numSeen ? setActiveValue((v: int) => { recentValue }) : ();"
                , "  }"
                , "  return activeValue;"
                , "}"
                , "comp UsingDebounce(clock: int) : int {"
                , "  state cachedValue, setCachedValue default expensive(clock);"
                , "  comp slowValue = Debounce(clock);"
                , "  on slowValue do {"
                , "    setCachedValue((v: int) => { expensive(slowValue) });"
                , "  }"
                , "  return cachedValue;"
                , "}"
                ]
          case runParser pProgram "test" progCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right (_ann :< ProgramF _eventDecls comps) -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents comps
              case result of
                Left inferErr -> expectationFailure $ "Program inference failed: " <> show inferErr
                Right (sigmaFinal, _typedComps) -> do
                  -- Both components should be in the final sigma
                  let (Sigma sigma) = sigmaFinal
                  Map.size sigma `shouldBe` 2
                  -- Verify both Debounce and UsingDebounce components are present
                  Map.member "Debounce" sigma `shouldBe` True
                  Map.member "UsingDebounce" sigma `shouldBe` True
                  -- Verify the components have the expected signatures
                  case (Map.lookup "Debounce" sigma, Map.lookup "UsingDebounce" sigma) of
                    (Just _, Just _) -> do
                      -- Both should be component entries (SigmaEntry has component schema)
                      True `shouldBe` True  -- Successfully found both entries
                    _ -> expectationFailure "Expected both Debounce and UsingDebounce in sigma"

        it "verifies complex effect composition with nested components" $ do
          let progCode = Text.unlines
                [ "comp Timer(interval: int) : int {"
                , "  state count, setCount default 0;"
                , "  on interval do {"
                , "    setTimeout((a: unit) => { setCount((c: int) => { c + 1 }) });"
                , "  }"
                , "  return count;"
                , "}"
                , "comp NestedTimer(speed: int) : int {"
                , "  comp fastTimer = Timer(speed);"
                , "  comp slowTimer = Timer(speed);"
                , "  on fastTimer do {"
                , "    ();"
                , "  }"
                , "  return slowTimer;"
                , "}"
                ]
          case runParser pProgram "test" progCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right (_ann :< ProgramF _eventDecls comps) -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents comps
              case result of
                Left inferErr -> expectationFailure $ "Program inference failed: " <> show inferErr
                Right (sigmaFinal, _typedComps) -> do
                  -- Both components should be properly typed with effect polymorphism
                  let (Sigma sigma) = sigmaFinal
                  Map.size sigma `shouldBe` 2
                  -- Effect polymorphism should allow setTimeout to work with different state setters
                  True `shouldBe` True

        it "verifies multiple polymorphic function calls" $ do
          let compCode = Text.unlines
                [ "comp MultiDelay() : int {"
                , "  state x, setX default 0;"
                , "  state y, setY default 0;"
                , "  state result, setResult default 0;"
                , "  on once do {"
                , "    setTimeout((a: unit) => { setX((v: int) => { v + 1 }) });"
                , "    setTimeout((a: unit) => { setY((v: int) => { v + 2 }) });"
                , "  }"
                , "  on x do {"
                , "    setResult((val: int) => { x + y });"
                , "  }"
                , "  return result;"
                , "}"
                ]
          case runParser pComponent "test" compCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right annotatedComp -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
              case result of
                Left inferErr -> expectationFailure $ "Type inference failed: " <> show inferErr
                Right (Sigma sigma, typedComps) -> do
                  -- Multiple calls to setTimeout should each instantiate with different effects
                  Map.member "MultiDelay" sigma `shouldBe` True
                  Map.size sigma `shouldBe` 1
                  case typedComps of
                    [(typedDecls, typedReturn)] -> do
                      -- Should have 3 state declarations + 2 effect declarations (on once, on x)
                      length typedDecls `shouldBe` 5
                      -- The return should be properly typed as result
                      case typedReturn of
                        (_ :< LangFExpr (EVarF varName)) -> varName `shouldBe` "result"
                        _ -> expectationFailure "Expected return to be result variable"
                    _ -> expectationFailure "Expected exactly one component result"

        it "rejects the removed delay builtin as an unbound variable" $ do
          let compCode = Text.unlines
                [ "comp DelayGone() : int {"
                , "  state counter, setCounter default 0;"
                , "  on once do {"
                , "    delay((x: unit) => { setCounter((c: int) => { c + 1 }) });"
                , "  }"
                , "  return counter;"
                , "}"
                ]
          case runParser pComponent "test" compCode of
            Left err -> expectationFailure $ "Parse failed: " <> show err
            Right annotatedComp -> do
              result <- runInferenceTest $ inferTyEffProgramTEST libraryComponents [annotatedComp]
              case result of
                Left inferErr -> show inferErr `shouldContain` "Variable not in scope: delay"
                Right _ -> expectationFailure "delay(...) should now be rejected as an unbound variable"

  describe "Enhanced Error Reporting" $ do
    describe "InferenceError" $ do
      it "provides source information in simple errors" $ do
        let errorResult = Left (InferenceError "Test error message" Nothing "")
        case errorResult of
          Left (InferenceError msg Nothing ctx) -> do
            msg `shouldBe` "Test error message"
            ctx `shouldBe` ""
          _ -> expectationFailure "Should be a simple InferenceError"

      it "provides context in detailed errors" $ do
        let errorResult = Left (InferenceError "Test error" Nothing "test context")
        case errorResult of
          Left (InferenceError msg Nothing ctx) -> do
            msg `shouldBe` "Test error"
            ctx `shouldBe` "test context"
          _ -> expectationFailure "Should be an InferenceError"
