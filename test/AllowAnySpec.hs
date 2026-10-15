-- | @--allow-any@: the unsound type @any@, the built-in @null@, and an
-- unannotated λ parameter typed @any@ anywhere, kept for programs written
-- against versions that had them. Each program here is run both ways: by
-- default it is rejected, and under the flag it is accepted as it was then.
module AllowAnySpec (spec) where

import Import
import PaperHarness
import InferenceMonad (InferenceError (..))
import Parse (pProgram, runAnnotatedParser)
import Test.Hspec
import qualified RIO.Text as Text

allowAny :: Options
allowAny = testOptions {optionsAllowAny = True}

-- | A component with one state variable x, around the given lines.
withX :: [Text] -> Text
withX body = Text.unlines $
  [ "comp C(clk: int) : unit {"
  , "  state x, setX default 0;"
  ]
  <> body <>
  [ "  return ();"
  , "}"
  ]

-- | The program is rejected by default, with a message containing @needle@.
rejectedByDefault :: String -> Text -> Expectation
rejectedByDefault needle src = do
  result <- inferSourceEither src
  case result of
    Left err -> Text.unpack (errorMessage err) `shouldContain` needle
    Right _ -> expectationFailure "accepted without --allow-any"

spec :: Spec
spec = describe "--allow-any" $ do

  describe "the type any" $ do

    let src = withX
          [ "  on clk do { fetch(\"/u\", (res: any) => { setX((c: int) => { c + 1 }) }) };" ]

    it "is not a type by default" $
      isLeft (runAnnotatedParser False pProgram "test" src) `shouldBe` True

    it "parses under the flag" $ do
      (sigma, _) <- inferSourceWith allowAny src
      cascadeOf sigma "C" "clk" `shouldBe` EffAfter (Time 1 NetworkReq) (after1r (at "x"))

    it "unifies with every type under the flag, which is what makes it unsound" $ do
      -- One value used as an int and as a string.
      _ <- inferSourceWith allowAny $ withX
        [ "  let both = (v: any) => { (v + 1, v ++ \"!\") };" ]
      pure ()

  describe "the built-in null" $ do

    let src = withX [ "  let nn = null;" ]

    it "is not in scope by default" $
      rejectedByDefault "Variable not in scope: null" src

    it "has type any under the flag" $ do
      (_, typed) <- inferSourceWith allowAny src
      nn <- expectJust "let nn in C" (findLetExpr "nn" (typedDeclsOf typed 0))
      getType nn `shouldBe` TAny

  describe "an unannotated λ outside an expected arrow" $ do

    let src = withX
          [ "  let inc = (v) => { setX((c: int) => { c + v }) };"
          , "  on clk do { inc(1) };"
          ]

    it "is rejected by default, asking for an annotation" $
      rejectedByDefault "needs a type annotation" src

    it "gets parameter type any under the flag" $ do
      (sigma, _) <- inferSourceWith allowAny src
      cascadeOf sigma "C" "clk" `shouldBe` after1r (at "x")

    it "is still rejected under the flag when its parameter is applied" $ do
      result <- inferSourceEitherWith allowAny $ withX [ "  let g = (f) => { f(1) };" ]
      case result of
        Left err -> do
          let msg = Text.unpack (errorMessage err)
          msg `shouldContain` "Cannot apply f"
          msg `shouldContain` "any"
        Right _ -> expectationFailure "applying a parameter of type any was accepted"

  describe "a λ with no parameters" $ do

    -- fetch hands its callback a string: () => … fits only if its
    -- parameter is any.
    let src = withX
          [ "  on clk do { fetch(\"/u\", () => { setX((c: int) => { c + 1 }) }) };" ]

    it "takes unit by default" $
      rejectedByDefault "Type mismatch" src

    it "takes any under the flag" $ do
      (sigma, _) <- inferSourceWith allowAny src
      cascadeOf sigma "C" "clk" `shouldBe` EffAfter (Time 1 NetworkReq) (after1r (at "x"))
