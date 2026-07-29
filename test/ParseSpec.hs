module ParseSpec (spec) where

import Import
import Parse
import Test.Hspec
import Text.Megaparsec (runParser, initialPos, SourcePos(..), mkPos, unPos)
import qualified RIO.Text as Text
import Import
import Control.Comonad.Cofree (Cofree(..))

spec :: Spec
spec = do
  describe "Annotated Expression Parsing" $ do
    describe "Basic Expression Parsing" $ do
      it "parses components with integer expressions" $ do
        let compCode = Text.unlines
              [ "comp IntLiteral() : int {"
              , "  let x = 42;"
              , "  return x;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "IntLiteral"
            getComponentArgs annotatedComp `shouldBe` []

      it "parses components with boolean expressions" $ do
        let compCode = Text.unlines
              [ "comp BoolTest() : bool {"
              , "  let x = true;"
              , "  let y = false;"
              , "  return x;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "BoolTest"

      it "parses components with string expressions" $ do
        let compCode = Text.unlines
              [ "comp StringTest() : string {"
              , "  let greeting = \"hello\";"
              , "  return greeting;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "StringTest"

      it "parses components with variable expressions" $ do
        let compCode = Text.unlines
              [ "comp VarTest() : int {"
              , "  let x = 42;"
              , "  let y = x;"
              , "  return y;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "VarTest"

      it "parses components with function application" $ do
        let compCode = Text.unlines
              [ "comp FuncApp() : int {"
              , "  let fn = (x: int) => { x + 1 };"
              , "  let result = fn(42);"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "FuncApp"

      it "parses components with arrow functions" $ do
        let compCode = Text.unlines
              [ "comp ArrowFunc() : int {"
              , "  let fn = (x: int) => { x + 1 };"
              , "  let result = 42;"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "ArrowFunc"

      it "fails to parse invalid syntax" $ do
        let badCode = "comp Bad() : int { let x = ; return x; }"
        case runParser pComponent "test" badCode of
          Left err -> show err `shouldContain` "TrivialError"
          Right _ -> expectationFailure "Should have failed to parse"

  describe "Annotated Component Parsing" $ do
    describe "Component Structure" $ do
      it "parses simple component with proper structure" $ do
        let compCode = Text.unlines
              [ "comp SimpleComponent() : int {"
              , "  let x = 42;"
              , "  return x;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "SimpleComponent"
            getComponentArgs annotatedComp `shouldBe` []

      it "parses component with state declarations" $ do
        let compCode = Text.unlines
              [ "comp Counter() : int {"
              , "  state count, setCount default 0;"
              , "  return count;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "Counter"
            getComponentArgs annotatedComp `shouldBe` []

      it "parses component with parameters" $ do
        let compCode = Text.unlines
              [ "comp WithParams(x: int, y: string) : int {"
              , "  let result = x + 10;"
              , "  return result;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> expectationFailure $ "Parse failed: " <> show err
          Right annotatedComp -> do
            getComponentName annotatedComp `shouldBe` "WithParams"
            getComponentArgs annotatedComp `shouldBe` [("x", TInt), ("y", TString)]

      it "fails to parse component with invalid syntax" $ do
        let compCode = Text.unlines
              [ "comp Counter() : jsx {"  -- jsx is not a valid return type in our system
              , "  state count, setCount default 0;"
              , "  return count;"
              , "}"
              ]
        case runParser pComponent "test" compCode of
          Left err -> show err `shouldContain` "Label"
          Right _ -> expectationFailure "Should have failed to parse"

  describe "Event-layer effect syntax" $ do
    it "parses modalities inside a type schema" $ do
      let schemaCode = "forall e. (unit -> unit | e) -> unit | eventually timeout<> {e} * after 100ms {timeout<>}"
      case runParser pType "test" schemaCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right (TArrow _ _ _ latent) ->
          -- Hand-built EffSeq literal (not mkEffSeq): pEffect itself builds via
          -- mkEffSeq, so comparing against mkEffSeq would pin nothing.
          latent `shouldBe`
            EffSeq
              [ EffEventually (EventLabel "timeout" []) (EffVar (EffVarName "e"))
              , EffAfter (Time 100 Millis) (EffEvent (EventLabel "timeout" []))
              ]
        Right other -> expectationFailure $ "Expected a TArrow, got: " <> show other

    it "parses cancel/remove effects in a sequence" $ do
      case runParser pEffect "test" "cancel click<#doc> * remove click<#doc>" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff ->
          eff `shouldBe`
            EffSeq
              [ EffCancel (EventLabel "click" ["#doc"])
              , EffRemove (EventLabel "click" ["#doc"])
              ]

    it "parses the always modality with a braced body" $ do
      case runParser pEffect "test" "always click<#doc> {@x}" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff ->
          eff `shouldBe` EffAlways (EventLabel "click" ["#doc"]) (EffStateChange "x")

    it "parses a bare event effect with a multi-value tuple" $ do
      case runParser pEffect "test" "req<check,suc>" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff ->
          eff `shouldBe` EffEvent (EventLabel "req" ["check", "suc"])

    it "parses label values with URL-style characters (spec: values are base values, e.g. URLs)" $ do
      case runParser pEffect "test" "req<api.users/v2>" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff ->
          eff `shouldBe` EffEvent (EventLabel "req" ["api.users/v2"])

    it "still parses a bare identifier as an effect variable" $ do
      case runParser pEffect "test" "e" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff -> eff `shouldBe` EffVar (EffVarName "e")

    it "does NOT misparse event kinds whose name starts with a modality keyword" $ do
      -- Regression: 'symbol "cancel"' used to consume the keyword prefix of
      -- 'cancelled', silently turning the event into a cancellation.
      case runParser pEffect "test" "cancelled<x>" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff -> eff `shouldBe` EffEvent (EventLabel "cancelled" ["x"])
      case runParser pEffect "test" "removeAll<y>" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff -> eff `shouldBe` EffEvent (EventLabel "removeAll" ["y"])

    it "falls back to EffVar for a modality keyword not followed by a label" $ do
      case runParser pEffect "test" "always" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff -> eff `shouldBe` EffVar (EffVarName "always")
      case runParser pEffect "test" "cancel" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff -> eff `shouldBe` EffVar (EffVarName "cancel")

  describe "Event-layer program and expression syntax" $ do
    it "parses an event declaration" $ do
      let progCode = Text.unlines
            [ "event click<#doc> : int;"
            , "comp P() : unit {"
            , "  return ();"
            , "}"
            ]
      case runParser pProgram "test" progCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right prog -> case prog of
          (_ :< ProgramF eventDecls comps) -> do
            case eventDecls of
              [_ :< EventDeclF lbl ty] -> do
                lbl `shouldBe` EventLabel "click" ["#doc"]
                ty `shouldBe` TInt
              _ -> expectationFailure "expected exactly one event declaration"
            length comps `shouldBe` 1

    it "parses interleaved event declarations and components (partitioned, in order)" $ do
      let progCode = Text.unlines
            [ "event a<> : unit;"
            , "comp A() : unit {"
            , "  return ();"
            , "}"
            , "event b<x> : bool;"
            , "comp B() : unit {"
            , "  return ();"
            , "}"
            ]
      case runParser pProgram "test" progCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right prog -> case prog of
          (_ :< ProgramF eventDecls comps) -> do
            [lbl | (_ :< EventDeclF lbl _) <- eventDecls]
              `shouldBe` [EventLabel "a" [], EventLabel "b" ["x"]]
            map getComponentName comps `shouldBe` ["A", "B"]

    it "parses bind/once with a handler argument and cancel/remove as bare atoms" $ do
      let progCode = Text.unlines
            [ "event click<#doc> : int;"
            , "event timeout<> : unit;"
            , "comp P() : unit {"
            , "  let b = bind click<#doc> h;"
            , "  let o = once timeout<> ((e: unit) => { () });"
            , "  let c = cancel timeout<>;"
            , "  let rm = remove timeout<>;"
            , "  return ();"
            , "}"
            ]
      case runParser pProgram "test" progCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right prog -> case prog of
          (_ :< ProgramF _ [(_ :< ComponentF _ _ _ decls _ _)]) -> do
            let rhsOf name = listToMaybe [e | (_ :< DeclLetF v _ e) <- decls, v == name]
            case rhsOf "b" of
              Just (_ :< LangFExpr (EBindF lbl (_ :< LangFExpr (EVarF "h")))) ->
                lbl `shouldBe` EventLabel "click" ["#doc"]
              other -> expectationFailure $ "expected EBindF over variable h, got: " <> maybe "Nothing" showAnnotatedNode other
            case rhsOf "o" of
              Just (_ :< LangFExpr (EOnceF lbl (_ :< LangFExpr (EArrowF {})))) ->
                lbl `shouldBe` EventLabel "timeout" []
              other -> expectationFailure $ "expected EOnceF over an arrow, got: " <> maybe "Nothing" showAnnotatedNode other
            case rhsOf "c" of
              Just (_ :< LangFExpr (ECancelF lbl)) ->
                lbl `shouldBe` EventLabel "timeout" []
              other -> expectationFailure $ "expected ECancelF, got: " <> maybe "Nothing" showAnnotatedNode other
            case rhsOf "rm" of
              Just (_ :< LangFExpr (ERemoveF lbl)) ->
                lbl `shouldBe` EventLabel "timeout" []
              other -> expectationFailure $ "expected ERemoveF, got: " <> maybe "Nothing" showAnnotatedNode other
          _ -> expectationFailure "expected a single component"

    it "bind/once/cancel/remove still parse as ordinary variable names" $ do
      -- Contextual-keyword regression: the four event words are NOT reserved,
      -- so they must stay usable as identifiers in expression position.
      let progCode = Text.unlines
            [ "comp P() : int {"
            , "  let bind = 5;"
            , "  let once = bind;"
            , "  let cancel = once;"
            , "  let remove = cancel;"
            , "  return remove;"
            , "}"
            ]
      case runParser pProgram "test" progCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right prog -> case prog of
          (_ :< ProgramF [] [(_ :< ComponentF _ _ _ decls ret _)]) -> do
            ret `shouldBe` "remove"
            let rhsOf name = listToMaybe [e | (_ :< DeclLetF v _ e) <- decls, v == name]
            case rhsOf "once" of
              Just (_ :< LangFExpr (EVarF "bind")) -> pure ()
              other -> expectationFailure $ "expected EVarF bind, got: " <> maybe "Nothing" showAnnotatedNode other
            case rhsOf "cancel" of
              Just (_ :< LangFExpr (EVarF "once")) -> pure ()
              other -> expectationFailure $ "expected EVarF once, got: " <> maybe "Nothing" showAnnotatedNode other
            case rhsOf "remove" of
              Just (_ :< LangFExpr (EVarF "cancel")) -> pure ()
              other -> expectationFailure $ "expected EVarF cancel, got: " <> maybe "Nothing" showAnnotatedNode other
          _ -> expectationFailure "expected a single component and no event declarations"

    it "prefixed identifiers (binds, cancelled) do NOT parse as event forms" $ do
      -- 'pModalityKeyword' requires an identifier boundary, so a variable
      -- whose NAME merely starts with an event keyword stays a plain EVarF.
      let progCode = Text.unlines
            [ "comp P() : int {"
            , "  let binds = 1;"
            , "  let cancelled = binds;"
            , "  return cancelled;"
            , "}"
            ]
      case runParser pProgram "test" progCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right prog -> case prog of
          (_ :< ProgramF [] [(_ :< ComponentF _ _ _ decls ret _)]) -> do
            ret `shouldBe` "cancelled"
            let rhsOf name = listToMaybe [e | (_ :< DeclLetF v _ e) <- decls, v == name]
            case rhsOf "cancelled" of
              Just (_ :< LangFExpr (EVarF "binds")) -> pure ()
              other -> expectationFailure $ "expected EVarF binds, got: " <> maybe "Nothing" showAnnotatedNode other
          _ -> expectationFailure "expected a single component and no event declarations"

  describe "Compute time unit + asyncCompute schema" $ do
    it "parses the u (compute) time unit in after grades" $ do
      case runParser pEffect "test" "after 1u {comp<suc>}" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff ->
          eff `shouldBe`
            EffAfter (Time 1 Compute) (EffEvent (EventLabel "comp" ["suc"]))

    it "parses event labels whose name is a reserved keyword (comp<suc>)" $ do
      -- The paper's asyncCompute events are literally named comp[suc] /
      -- comp[err], and "comp" is the component keyword; pEventLabelName
      -- deliberately skips the reserved-keyword check (a label name is
      -- always immediately followed by '<').
      case runParser pEffect "test" "comp<suc> + comp<err>" of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right eff ->
          eff `shouldBe`
            EffBranch
              (EffEvent (EventLabel "comp" ["suc"]))
              (EffEvent (EventLabel "comp" ["err"]))

    it "parses the asyncCompute builtin schema verbatim" $ do
      -- The exact schema string from src/Builtins.hs (owner-pinned, §5):
      -- ∀F1, F2. … | ○¹ᵘ (comp[suc] + comp[err]) * ◇comp[suc](F1 * ✗comp[err])
      --            * ◇comp[err](F2 * ✗comp[suc]).
      -- NOTE: a curried schema's trailing `| F` attaches to the LAST arrow
      -- (A -> B -> C | F parses as A -> (B -> C | F)), so F fires exactly on
      -- full application — EX-ASYNCCOMPUTE in PaperExamplesSpec pins the
      -- instantiated effect. Here we pin the parse tree itself.
      let schemaCode = "forall e1, e2. (int -> unit | e1) -> (int -> unit | e2) -> unit | after 1u {comp<suc> + comp<err>} * eventually comp<suc> {e1 * remove comp<err>} * eventually comp<err> {e2 * remove comp<suc>}"
      case runParser pType "test" schemaCode of
        Left err -> expectationFailure $ "Parse failed: " <> show err
        Right (TArrow binders _ (TArrow [] _ _ latent) EffNone) -> do
          binders `shouldBe` [EffVarName "e1", EffVarName "e2"]
          -- Hand-built literal (see the schema test above for why not
          -- mkEffSeq).
          latent `shouldBe`
            EffSeq
              [ EffAfter (Time 1 Compute)
                  (EffBranch (EffEvent (EventLabel "comp" ["suc"])) (EffEvent (EventLabel "comp" ["err"])))
              , EffEventually (EventLabel "comp" ["suc"])
                  (EffSeq [EffVar (EffVarName "e1"), EffRemove (EventLabel "comp" ["err"])])
              , EffEventually (EventLabel "comp" ["err"])
                  (EffSeq [EffVar (EffVarName "e2"), EffRemove (EventLabel "comp" ["suc"])])
              ]
        Right other -> expectationFailure $ "Expected a curried TArrow, got: " <> show other
