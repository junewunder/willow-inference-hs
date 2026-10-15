-- | Algorithm W's substitution discipline, on whole programs: what one step
-- of inference learns about a unification variable holds at every later
-- step. The substitution is threaded through a component, composed rather
-- than merged, applied to the context and to what has already been built,
-- and never binds a variable to an effect it occurs in.
--
-- Each program here was accepted, or inferred a different effect, when
-- unifiers were local to the node that computed them. The laws behind these
-- (composition, idempotence, the occurs check) are QuickCheck properties in
-- "EffectVariableLawsSpec".
--
-- Also here: the checker's other error-reporting fixes (an unannotated λ, the
-- source span of a declaration, the number of explicit effect arguments).
module SubstitutionSpec (spec) where

import Import
import PaperHarness
import InferenceMonad (InferenceError (..))
import InferTyEffect (unifyEffect)
import Test.Hspec
import Text.Megaparsec.Pos (sourceColumn, sourceLine, unPos)
import qualified RIO.Map as Map
import qualified RIO.Text as Text

spec :: Spec
spec = describe "Substitutions (Algorithm W)" $ do

  let setX = "(v: int) => { setX((c: int) => { c + v }) }"
      setY = "(v: int) => { setY((c: int) => { c + v }) }"
      withXY body = Text.unlines $
        [ "comp C(clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  let needsX = (h: int -> unit | after 1r {@x}) => { h(1) };"
        ]
        <> body <>
        [ "  return ();"
        , "}"
        ]

  -- -----------------------------------------------------------------------
  describe "a unifier is applied to the context" $ do

    it "an application inside a λ fixes the λ's parameter, so the λ is not generalised over it" $ do
      -- needsX(f) binds f's e to ○¹ʳ @x. useX is therefore
      -- (int → unit | ○¹ʳ @x) → unit, not ∀e. (int → unit | e) → unit, and a
      -- function that changes y is not a valid argument.
      let prog arg = withXY
            [ "  let useX = (f: int -> unit | e) => { needsX(f) };"
            , "  on clk do { useX(" <> arg <> ") };"
            ]
      (sigma, _) <- inferSource (prog setX)
      cascadeOf sigma "C" "clk" `shouldBe` after1r (at "x")
      result <- inferSourceEither (prog setY)
      rejected "a function that changes y passed where needsX fixed the effect to @x" result

    it "a conditional's branches fix the λ's parameter the same way" $ do
      let prog arg = withXY
            [ "  let pick = (f: int -> unit | e) => { (true ? f : " <> setX <> ") };"
            , "  on clk do { pick(" <> arg <> ")(1) };"
            ]
      (sigma, _) <- inferSource (prog setX)
      cascadeOf sigma "C" "clk" `shouldBe` seqE [branchE EffNone EffNone, after1r (at "x")]
      result <- inferSourceEither (prog setY)
      rejected "a function that changes y passed where the other branch fixed the effect to @x" result

    it "an effect built before a later unification is brought under it" $ do
      -- f(1) has effect ?e when it is inferred; needsX(f) binds ?e earlier
      -- in the same body. Nothing binds it afterwards (the argument already
      -- has effect ○¹ʳ @x), so no unification variable may survive.
      (sigma, _) <- inferSource $ withXY
        [ "  on clk do { ((f: int -> unit | e) => { needsX(f) ;; f(1) })(" <> setX <> ") };" ]
      cascadeOf sigma "C" "clk" `shouldBe` after1r (at "x")

  -- -----------------------------------------------------------------------
  describe "an annotation's unifier is kept" $ do

    -- A's f is left open by the polymorphic argument nn, so
    -- a.g : int → unit | ?e, and a.clk's cascade is ?e.
    let parent body = Text.unlines $
          [ "comp A<f>(g: int -> unit | f, clk: int) : unit {"
          , "  on clk do { g(1) };"
          , "  return ();"
          , "}"
          ]
          <> body

    it "a let annotation fixes a variable of the context, and Δ sees it" $ do
      (sigma, _) <- inferSource $ parent
        [ "comp P(nn: forall G. int -> unit | G, clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  comp a = A(nn, clk);"
        , "  let h : int -> unit | after 1r {@x} = a.g;"
        , "  return ();"
        , "}"
        ]
      cascadeOf sigma "P" "a.clk" `shouldBe` after1r (at "x")

    it "a second annotation that contradicts the first is rejected, not resolved in the first's favour" $ do
      result <- inferSourceEither $ parent
        [ "comp P(nn: forall G. int -> unit | G, clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  comp a = A(nn, clk);"
        , "  let h : int -> unit | after 1r {@x} = a.g;"
        , "  let h2 : int -> unit | after 1r {@y} = a.g;"
        , "  return ();"
        , "}"
        ]
      rejected "a.g annotated at effect @x and then at effect @y" result

    it "a component's return annotation fixes a variable of the context, in Δ and in the typed tree" $ do
      (sigma, typed) <- inferSource $ parent
        [ "comp P(nn: forall G. int -> unit | G, clk: int) : int -> unit | after 1r {@x} {"
        , "  comp a = A(nn, clk);"
        , "  let rv = a.g;"
        , "  return rv;"
        , "}"
        ]
      cascadeOf sigma "P" "a.clk" `shouldBe` after1r (at "x")
      rv <- expectJust "let rv in P" (findLetExpr "rv" (typedDeclsOf typed 1))
      getType rv `shouldBe` TArrow [] TInt TUnit (after1r (at "x"))

  -- -----------------------------------------------------------------------
  describe "the occurs check" $ do

    it "rejects a program whose effect would have to contain itself" $ do
      -- both needs two functions of one effect e. The second is h followed
      -- by a change to x, so e = e * ○¹ʳ @x.
      result <- inferSourceEither $ withXY
        [ "  let both = (p: (int -> unit | e) * (int -> unit | e)) => { p.0(1) };"
        , "  let lp = (h: int -> unit | f) => { both(h, (k: int) => { h(k) ;; setX((c: int) => { c + k }) }) };"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "occurs check"
        Right _ -> expectationFailure "e = e * after 1r {@x} was solved"

    it "rejects ?e ≐ ?e * @x" $ do
      result <- runInferenceTest $ unifyEffect (EffUnif 1) (seqE [EffUnif 1, at "x"])
      isLeft result `shouldBe` True

    it "a sequence's premises are solved in turn: ○¹ʳ ?e * ?e ≐ ○¹ʳ @x * · does not bind ?e to both @x and ·" $ do
      -- The first premise binds ?e to @x; the second, ?e ≐ ·, is then
      -- @x ≐ ·, which fails. A union of the two unifiers kept ?e ↦ @x.
      result <- runInferenceTest $
        unifyEffect (seqE [after1r (EffUnif 1), EffUnif 1]) (seqE [after1r (at "x"), EffNone])
      isLeft result `shouldBe` True

  -- -----------------------------------------------------------------------
  describe "sequences unify only with sequences of the same length" $ do

    it "unifies element by element" $ do
      result <- runInferenceTest $
        unifyEffect (seqE [EffUnif 1, at "y"]) (seqE [at "x", EffUnif 2])
      result `shouldBe` Right (Map.fromList [(Unif 1, at "x"), (Unif 2, at "y")])

    it "rejects a sequence against a non-sequence: @x * ?e ≐ @x" $ do
      -- Matching @x against the first element and every other element
      -- against · would accept this, binding ?e to ·.
      r1 <- runInferenceTest $ unifyEffect (seqE [at "x", EffUnif 1]) (at "x")
      isLeft r1 `shouldBe` True
      r2 <- runInferenceTest $ unifyEffect (at "x") (seqE [at "x", EffUnif 1])
      isLeft r2 `shouldBe` True

    it "rejects sequences of different lengths: ?e1 * ?e2 ≐ @x * · * ?e3" $ do
      -- Matching the whole shorter sequence against the first element of the
      -- longer, and · against the rest, would accept this with ?e2, ?e3 ↦ ·.
      result <- runInferenceTest $
        unifyEffect (seqE [EffUnif 1, EffUnif 2]) (seqE [at "x", EffNone, EffUnif 3])
      isLeft result `shouldBe` True

    it "an unflattened one-element sequence [F] still unifies with F" $ do
      r1 <- runInferenceTest $ unifyEffect (EffSeq [after1r (EffUnif 1)]) (after1r (at "x"))
      r1 `shouldBe` Right (Map.fromList [(Unif 1, at "x")])
      r2 <- runInferenceTest $ unifyEffect (after1r (at "x")) (EffSeq [after1r (EffUnif 1)])
      r2 `shouldBe` Right (Map.fromList [(Unif 1, at "x")])

  -- -----------------------------------------------------------------------
  describe "an unannotated λ is typed only against an expected arrow" $ do

    let needsAnnotation what src = do
          result <- inferSourceEither src
          case result of
            Left err -> do
              let msg = Text.unpack (errorMessage err)
              msg `shouldContain` "Cannot infer the type of the parameter"
              msg `shouldContain` "needs a type annotation"
            Right _ -> expectationFailure (what <> " was accepted")

    it "an unannotated λ bound by a let is rejected, asking for an annotation" $
      needsAnnotation "an unannotated λ with no expected type" $ Text.unlines
        [ "comp C(clk: int) : unit {"
        , "  let g = (f) => { f(1) };"
        , "  return ();"
        , "}"
        ]

    it "an unannotated λ applied directly is rejected" $
      needsAnnotation "an unannotated λ in function position" $ withXY
        [ "  on clk do { ((v) => { " <> setX <> "(v) })(1) };" ]

    it "an unannotated λ passed for an arrow parameter takes the parameter's type" $ do
      (sigma, _) <- inferSource $ withXY
        [ "  on clk do { needsX((v) => { setX((c: int) => { c + v }) }) };" ]
      cascadeOf sigma "C" "clk" `shouldBe` after1r (at "x")

    it "a λ with no parameters takes unit" $ do
      (sigma, _) <- inferSource $ withXY
        [ "  let tick = () => { setX((c: int) => { c + 1 }) };"
        , "  on clk do { tick(()) };"
        ]
      cascadeOf sigma "C" "clk" `shouldBe` after1r (at "x")

  -- -----------------------------------------------------------------------
  describe "applying a value that is not a function" $ do

    it "an int is rejected with its type in the message" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp C(clk: int) : unit {"
        , "  let a = 1;"
        , "  let b = a(2);"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "not a function: it has type int"
        Right _ -> expectationFailure "applying an int was accepted"

  -- -----------------------------------------------------------------------
  describe "a declaration's error points at the declaration" $ do

    let errorAt line column src = do
          result <- inferSourceEither src
          case result of
            Left err -> case errorSource err of
              Just sp -> do
                unPos (sourceLine (spanStart sp)) `shouldBe` line
                unPos (sourceColumn (spanStart sp)) `shouldBe` column
              Nothing -> expectationFailure "the error has no source span"
            Right _ -> expectationFailure "the program was accepted"

    it "on" $ errorAt 3 3 $ Text.unlines
      [ "comp C(clk: int) : unit {"
      , "  state x, setX default 0;"
      , "  on nope do { () };"
      , "  return ();"
      , "}"
      ]

    it "state" $ errorAt 3 3 $ Text.unlines
      [ "comp C(clk: int) : unit {"
      , "  state x, setX default 0;"
      , "  state y, setY default setX((c: int) => { c + 1 });"
      , "  return ();"
      , "}"
      ]

    it "comp" $ errorAt 2 3 $ Text.unlines
      [ "comp C(clk: int) : unit {"
      , "  comp a = Nope(clk);"
      , "  return ();"
      , "}"
      ]

    it "a component's return type" $ errorAt 2 1 $ Text.unlines
      [ ""
      , "comp C(clk: int) : bool {"
      , "  state x, setX default 0;"
      , "  return x;"
      , "}"
      ]

  -- -----------------------------------------------------------------------
  describe "explicit effect arguments" $ do

    let program args = Text.unlines
          [ "comp A<f, g>(h: int -> unit | f, k: int -> unit | g, clk: int) : unit {"
          , "  on clk do { h(1) ;; k(1) };"
          , "  return ();"
          , "}"
          , "comp P(nn: forall G. int -> unit | G, clk: int) : unit {"
          , "  comp a = A" <> args <> "(nn, nn, clk);"
          , "  return ();"
          , "}"
          ]

    forM_ ["", "<?, ?>", "<none, ?>"] $ \args ->
      it ("A" <> Text.unpack args <> " is accepted for two effect parameters") $ do
        _ <- inferSource (program args)
        pure ()

    forM_ ["<?>", "<?, ?, ?>", "<none, none, none>"] $ \args ->
      it ("A" <> Text.unpack args <> " is rejected for two effect parameters") $ do
        result <- inferSourceEither (program args)
        case result of
          Left err -> Text.unpack (errorMessage err) `shouldContain` "takes 2 effect argument(s)"
          Right _ -> expectationFailure "a mismatched number of effect arguments was accepted"

  -- -----------------------------------------------------------------------
  describe "once is a keyword, not a built-in" $

    it "once on its own is not in scope" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp C(clk: int) : unit {"
        , "  let o = once;"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "Variable not in scope: once"
        Right _ -> expectationFailure "once was accepted as a value"

rejected :: String -> Either InferenceError a -> Expectation
rejected what result = case result of
  Left _ -> pure ()
  Right _ -> expectationFailure (what <> " was accepted")
