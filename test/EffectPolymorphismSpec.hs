-- | Effect polymorphism, checked against textbook Hindley–Milner with rigid
-- and flexible variables.
--
-- The paper's formal system has no effect polymorphism, so these are not
-- paper rules. They pin the behaviour the checker's polymorphism is meant to
-- have: written effect variables are rigid and distinct from the unification
-- variables inference creates, every @let@ is generalised over what the
-- context does not own, an annotated @let@ is checked against its
-- annotation, and each component instance gets fresh variables.
--
-- The algebraic laws behind these (instantiation, generalisation,
-- capture-avoiding substitution) are QuickCheck properties in
-- "EffectVariableLawsSpec".
module EffectPolymorphismSpec (spec) where

import Import
import PaperHarness
import InferenceMonad (InferenceError (..))
import InferTyEffect (unifyEffect, unifyType)
import Analysis.Common (fullEffectVar)
import Test.Hspec
import qualified RIO.Text as Text

spec :: Spec
spec = describe "Effect polymorphism (Hindley–Milner)" $ do

  -- -----------------------------------------------------------------------
  describe "written and unification variables are distinct" $ do

    it "a fresh variable never takes the name of a written one" $ do
      -- fetch : ∀e. (string × (any → unit | e)) → unit | ○¹ⁿ e. Passing
      -- null leaves its e unconstrained, so the call's effect keeps the
      -- fresh variable. The component's own parameter is spelled e0, the
      -- name the first fresh variable used to get: the two must stay apart.
      (sigma, _) <- inferSource $ Text.unlines
        [ "comp Fresh<e0>(g: int -> unit | e0, clk: int) : unit {"
        , "  on clk do { fetch(\"/u\", null) ;; g(1) };"
        , "  return ();"
        , "}"
        ]
      printed (cascadeOf sigma "Fresh" "clk") `shouldBe` "after 1n {?_e0} * ?e0"

    it "a written variable unifies with itself" $ do
      _ <- inferSource $ Text.unlines
        [ "comp Same<F>(g: int -> unit | F) : int -> unit | F {"
        , "  return g;"
        , "}"
        ]
      pure ()

    it "two different written variables do not unify" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp Different<F, G>(g: int -> unit | F) : int -> unit | G {"
        , "  return g;"
        , "}"
        ]
      rejected "a function of effect F returned at effect G" result

    it "a written variable does not unify with a concrete effect" $ do
      -- The return annotation promises effect F, whatever the caller picks;
      -- the function returned changes x.
      result <- inferSourceEither $ Text.unlines
        [ "comp Concrete<F>(clk: int) : int -> unit | F {"
        , "  state x, setX default 0;"
        , "  let f = (k: int) => { setX((c: int) => { c + k }) };"
        , "  return f;"
        , "}"
        ]
      rejected "a function that changes x returned at effect F" result

    -- A λ-parameter annotation is read like an OCaml type annotation, as in
    -- fun (f : 'a -> unit) -> …: a variable no enclosing scope binds is
    -- flexible, and stands for whatever effect the argument has. It is one
    -- variable per name across the whole declaration, not per λ.
    let applied params arg = Text.unlines
          [ "comp L" <> params <> "(clk: int) : unit {"
          , "  state x, setX default 0;"
          , "  state y, setY default 0;"
          , "  on clk do { " <> arg <> " };"
          , "  return ();"
          , "}"
          ]
        setX = "(v: int) => { setX((c: int) => { c + v }) }"
        setY = "(v: int) => { setY((c: int) => { c + v }) }"

    it "an unbound variable in a λ-parameter annotation is flexible" $ do
      (sigma, _) <- inferSource $ applied "" ("((f: int -> unit | e) => { f(1) })(" <> setX <> ")")
      cascadeOf sigma "L" "clk" `shouldBe` after1r (at "x")

    it "a λ-parameter annotation's variable bound by the component stays rigid" $ do
      result <- inferSourceEither $ applied "<e>" ("((f: int -> unit | e) => { f(1) })(" <> setX <> ")")
      rejected "a function that changes x passed where the component's e is required" result

    it "two uses of one name in a λ-parameter annotation are the same variable" $ do
      let pairOf a b =
            "((p: ((int -> unit | e) * (int -> unit | e))) => { p.0(1) })(" <> a <> ", " <> b <> ")"
      (sigma, _) <- inferSource $ applied "" (pairOf setX setX)
      cascadeOf sigma "L" "clk" `shouldBe` after1r (at "x")
      result <- inferSourceEither $ applied "" (pairOf setX setY)
      rejected "two functions of different effects for the same e" result

    -- Two lets, or one let whose curried λs both annotate their parameter
    -- with G, applied to a function that changes x and one that changes y.
    let curried = Text.unlines
          [ "comp C(clk: int) : int {"
          , "  state x, setX default 0;"
          , "  state y, setY default 0;"
          , "  let ap = (f: int -> unit | G) => (g: int -> unit | G) => { f(1) ;; g(1) };"
          , "  on clk do { ap((u: int) => setX((c: int) => u))((u: int) => setY((c: int) => u)) };"
          , "  return clk;"
          , "}"
          ]
        separate = Text.unlines
          [ "comp C(clk: int) : int {"
          , "  state x, setX default 0;"
          , "  state y, setY default 0;"
          , "  let apf = (f: int -> unit | G) => { f(1) };"
          , "  let apg = (g: int -> unit | G) => { g(1) };"
          , "  on clk do { apf((u: int) => setX((c: int) => u)) ;; apg((u: int) => setY((c: int) => u)) };"
          , "  return clk;"
          , "}"
          ]

    it "one name in the annotations of two λs of one declaration is the same variable" $ do
      result <- inferSourceEither curried
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "Cannot unify effects: @x and @y"
        Right _ -> expectationFailure "two functions of different effects for the same G were accepted"

    it "one name in the annotations of two declarations is two variables" $ do
      (sigma, _) <- inferSource separate
      cascadeOf sigma "C" "clk" `shouldBe` seqE [after1r (at "x"), after1r (at "y")]

    it "an annotation's flexible variable is generalised with its let" $ do
      (sigma, _) <- inferSource $ Text.unlines
        [ "comp C(clk: int) : int {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  let ap = (f: int -> unit | G) => f(1);"
        , "  on clk do { ap((u: int) => setX((c: int) => u)) ;; ap((u: int) => setY((c: int) => u)) };"
        , "  return clk;"
        , "}"
        ]
      cascadeOf sigma "C" "clk" `shouldBe` seqE [after1r (at "x"), after1r (at "y")]

    it "unification binds neither of two different written variables" $ do
      result <- runInferenceTest $ unifyEffect (EffVar (EffVarName "F")) (EffVar (EffVarName "G"))
      isLeft result `shouldBe` True

    it "unification does not bind a written variable to a concrete effect" $ do
      result <- runInferenceTest $ unifyEffect (EffVar (EffVarName "F")) (after1r (at "x"))
      isLeft result `shouldBe` True

  -- -----------------------------------------------------------------------
  describe "let generalises only what the context does not own" $ do

    -- The reproducer: g's effect F belongs to the component, so a let bound
    -- to g must keep it.
    let component ann = Text.unlines
          [ "comp C<F>(g: int -> unit | F, clk: int) : unit {"
          , "  let h" <> ann <> " = g;"
          , "  on clk do { h(1) };"
          , "  return ();"
          , "}"
          ]

    it "unannotated: let h = g keeps the component's F" $ do
      (sigma, _) <- inferSource (component "")
      cascadeOf sigma "C" "clk" `shouldBe` EffVar (EffVarName "F")

    it "annotated with the component's F: let h : int -> unit | F = g checks and keeps F" $ do
      (sigma, _) <- inferSource (component " : int -> unit | F")
      cascadeOf sigma "C" "clk" `shouldBe` EffVar (EffVarName "F")

    it "annotated with forall F: rejected, since g works at one F only" $ do
      -- The annotation's F is a new, rigid variable, not the component's.
      -- Claiming h works for every effect is more than g provides.
      result <- inferSourceEither (component " : forall F. int -> unit | F")
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "does not have its annotated type"
        Right _ -> expectationFailure "∀F. int → unit | F was accepted for a function of one fixed effect"

    it "an unannotated let is generalised over a variable the context does not own" $ do
      -- apply's e is written only in its own λ, so apply is ∀e and each use
      -- instantiates it afresh.
      (sigma, _) <- inferSource $ Text.unlines
        [ "comp Apply(clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  let apply = (f: int -> unit | e) => { f(1) };"
        , "  on clk do {"
        , "    apply((v: int) => { setX((c: int) => { c + v }) }) ;;"
        , "    apply((v: int) => { setY((c: int) => { c + v }) })"
        , "  };"
        , "  return ();"
        , "}"
        ]
      cascadeOf sigma "Apply" "clk" `shouldBe` seqE [after1r (at "x"), after1r (at "y")]

    it "an annotation may not quantify a variable the context fixes" $ do
      -- a.g has effect ?_e: A's parameter, left open because its argument
      -- has type any. That variable is in the context, so it cannot be
      -- generalised, and binding it to the annotation's F would let F escape.
      result <- inferSourceEither $ Text.unlines
        [ "comp A<f>(g: int -> unit | f, clk: int) : unit {"
        , "  on clk do { g(1) };"
        , "  return ();"
        , "}"
        , "comp P(clk: int) : unit {"
        , "  let nn = null;"
        , "  comp a = A(nn, clk);"
        , "  let h : forall F. int -> unit | F = a.g;"
        , "  return ();"
        , "}"
        ]
      rejected "∀F. int → unit | F for a function whose effect the context fixes" result

  -- -----------------------------------------------------------------------
  describe "component instances rename their effect parameters apart" $ do

    let parent param = Text.unlines
          [ "comp A<" <> param <> ">(g: int -> unit | " <> param <> ", clk: int) : unit {"
          , "  on clk do { g(1) };"
          , "  return ();"
          , "}"
          , "comp P(clk: int) : unit {"
          , "  state x, setX default 0;"
          , "  let h = (k: int) => { setX((c: int) => { c + k }) };"
          , "  comp a = A<after 1r {@x}>(h, clk);"
          , "  on clk do { setTimeout((u: unit) => { () }) };"
          , "  return ();"
          , "}"
          ]

    forM_ ["e", "f"] $ \param ->
      it ("an instance of A<" <> Text.unpack param <> "> leaves the built-in setTimeout : ∀e. … alone") $ do
        (sigma, _) <- inferSource (parent param)
        cascadeOf sigma "P" "a.clk" `shouldBe` after1r (at "x")
        cascadeOf sigma "P" "clk"
          `shouldBe` seqE
            [ at "a.clk"
            , EffEventually (EventLabel "timeout" []) EffNone
            , EffAfter (Time 100 Millis) (EffEvent (EventLabel "timeout" []))
            ]

    it "a parameter left unbound does not leak into the parent under its own name" $ do
      -- nn : any binds nothing, so A's f stays open. It must not become the
      -- parent's own parameter f.
      (sigma, _) <- inferSource $ Text.unlines
        [ "comp A<f>(g: int -> unit | f, clk: int) : unit {"
        , "  on clk do { g(1) };"
        , "  return ();"
        , "}"
        , "comp P<f>(k: int -> unit | f, clk: int) : unit {"
        , "  let nn = null;"
        , "  comp a = A(nn, clk);"
        , "  on clk do { k(1) };"
        , "  return ();"
        , "}"
        ]
      let parentF = EffVar (EffVarName "f")
      cascadeOf sigma "P" "a.clk" `shouldNotBe` parentF
      occurrences parentF (fullEffectVar (deltaOf sigma "P") "clk") `shouldBe` 1

    it "an explicit effect argument still instantiates the parameter" $ do
      (sigma, _) <- inferSource (parent "f")
      cascadeOf sigma "P" "a.clk" `shouldBe` after1r (at "x")

    it "a polymorphic argument is accepted for a polymorphic parameter" $ do
      _ <- inferSource $ Text.unlines
        [ "comp A(k: forall F. int -> unit | F, clk: int) : unit {"
        , "  return ();"
        , "}"
        , "comp P(k2: forall G. int -> unit | G, clk: int) : unit {"
        , "  comp a = A(k2, clk);"
        , "  return ();"
        , "}"
        ]
      pure ()

  -- -----------------------------------------------------------------------
  describe "schemas unify up to renaming of their binders" $ do

    let arrowOf vs eff = TArrow (map EffVarName vs) TInt TUnit eff
        var = EffVar . EffVarName

    it "∀F. int → unit | F unifies with ∀G. int → unit | G" $ do
      result <- runInferenceTest $ unifyType (arrowOf ["F"] (var "F")) (arrowOf ["G"] (var "G"))
      isRight result `shouldBe` True

    it "∀F. int → unit | F does not unify with ∀G. int → unit | ○¹ʳ @x (its binder is not bindable)" $ do
      result <- runInferenceTest $ unifyType (arrowOf ["F"] (var "F")) (arrowOf ["G"] (after1r (at "x")))
      isLeft result `shouldBe` True

    it "∀F. int → unit | F does not unify with ∀G. int → unit | H (a bound and a free variable differ)" $ do
      result <- runInferenceTest $ unifyType (arrowOf ["F"] (var "F")) (arrowOf ["G"] (var "H"))
      isLeft result `shouldBe` True

-- | The canonical one-line rendering of an effect.
printed :: Effect -> Text
printed = Text.pack . show . prettyEffect

-- | How many times an effect occurs as a leaf of another.
occurrences :: Effect -> Effect -> Int
occurrences leaf eff
  | eff == leaf = 1
  | otherwise = case eff of
      EffSeq es -> sum (map (occurrences leaf) es)
      EffBranch a b -> occurrences leaf a + occurrences leaf b
      EffAfter _ e -> occurrences leaf e
      EffAlways _ e -> occurrences leaf e
      EffEventually _ e -> occurrences leaf e
      _ -> 0

rejected :: String -> Either InferenceError a -> Expectation
rejected what result = case result of
  Left _ -> pure ()
  Right _ -> expectationFailure (what <> " was accepted")
