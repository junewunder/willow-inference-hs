-- | One test per typing rule from the paper. Test names carry the rule IDs
-- the paper uses (T-STATE-DECL, T-APP, C-DEP, SE-DELAY, …) so that when
-- inference misbehaves we can tell immediately which rule of the formalism is
-- breaking down.
--
-- Conventions (see "PaperHarness" haddock):
--   Typing rules are ordinary tests over inferred programs. The sub-effecting
--   rules (SE-*) instead call the pure decision procedure
--   'Analysis.Common.subEffect' directly on hand-built effect trees. The
--   T-STATE-DECL / T-LET-DECL purity premises are enforced as rejections —
--   their negative tests live below — while the T-ON-DECL causes premise is
--   discharged by accumulation in the inferred-Δ prototype.
module PaperRulesSpec (spec) where

import Import
import PaperHarness
import InferenceMonad (InferenceError (..))
import Analysis.Common (fullEffect, fullEffectVar, simplifyEffect, subEffect)
import Test.Hspec
import qualified RIO.Map as Map
import qualified RIO.Text as Text

spec :: Spec
spec = describe "Paper typing rules" $ do

  -- ---------------------------------------------------------------------
  -- §3 Declaration-level typing (main text Fig 6; appendix Fig 12)
  -- ---------------------------------------------------------------------
  describe "Declaration rules" $ do

    it "T-RETURN-DECL: return x : τ checks x against the declared return type" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TReturn() : int {"
        , "  let x = 42;"
        , "  return x;"
        , "}"
        ]
      getType (typedReturnOf typedComps 0) `shouldBe` TInt
      -- Paper premise Δ ⊢ @x ⇒ @return (the returned variable's changes must
      -- be accounted for under a special @return node) has no counterpart in
      -- the impl, which validates the return *type* only.

    it "T-RETURN-DECL (negative): a return type mismatch is rejected" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp TReturnBad() : string {"
        , "  let x = 42;"
        , "  return x;"
        , "}"
        ]
      case result of
        Left _ -> pure ()
        Right _ -> expectationFailure "expected a return-type mismatch error"

    it "T-STATE-DECL: setX gets type (τ → τ | ·) → unit | ○¹ʳ @x; x gets no dependencies" $ do
      (sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TState(clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  on clk do { setX(addOne) };"
        , "  return ();"
        , "}"
        ]
      -- Applying the setter releases its latent seed effect ○¹ʳ @x (the
      -- application lives in an on-block: an impure let RHS is a type error,
      -- so `let u = setX(addOne);` is not an option):
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [s] -> do
          getType s `shouldBe` TUnit
          getEffect s `shouldBe` after1r (at "x")
        _ -> expectationFailure "expected a single-statement on-block"
      -- State variables have no dependencies: Δ entry is x[] ∣ F. The effect
      -- lands on clk's cascade, so x's own cascade stays ·.
      depsOf sigma "TState" "x" `shouldBe` []
      cascadeOf sigma "TState" "x" `shouldBe` EffNone

    it "T-STATE-DECL (side condition): the default expression must be pure (Γ ⊢ e : τ ∣ ·)" $ do
      -- An impure default is a type error. Note that the 'impure' default
      -- must be genuinely effectful: `print("hi")` does not work here, since
      -- `print` is a PURE builtin (string -> unit) and could never be
      -- rejected. Hence the pair-projection idiom: (setY(addOne), 0).1
      -- evaluates the setter
      -- (effect ○¹ʳ @y) and yields the int 0.
      result <- inferSourceEither $ Text.unlines
        [ "comp TStatePure() : unit {"
        , "  state y, setY default 0;"
        , "  state x, setX default (setY(addOne), 0).1;"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> do
          Text.unpack (errorMessage err) `shouldContain` "Impure state default for 'x'"
          Text.unpack (errorMessage err) `shouldContain` "T-STATE-DECL requires Gamma |- e : tau | ."
          Text.unpack (errorMessage err) `shouldContain` "@y"
        Right _ -> expectationFailure "impure state default was accepted"

    it "T-LET-DECL: dependencies come from the dataflow function df(e) (free variables)" $ do
      (sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TLet(a: int) : int {"
        , "  let y = a + 1;"
        , "  let z = y + a;"
        , "  return z;"
        , "}"
        ]
      depsOf sigma "TLet" "y" `shouldBe` ["a"]
      depsOf sigma "TLet" "z" `shouldBe` ["a", "y"]
      z <- expectJust "let z" $ findLetExpr "z" (typedDeclsOf typedComps 0)
      getType z `shouldBe` TInt

    it "T-LET-DECL (side condition): the right-hand side must be pure (Γ ⊢ e : τ ∣ ·)" $ do
      -- `let u = setX(addOne);` is a type error; effectful expressions belong
      -- in on-block bodies. The effect (○¹ʳ @x) must not vanish from Δ via an
      -- unrecorded let RHS.
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetPure() : unit {"
        , "  state x, setX default 0;"
        , "  let u = setX(addOne);"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> do
          Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'u'"
          Text.unpack (errorMessage err) `shouldContain` "T-LET-DECL requires Gamma |- e : tau | ."
          Text.unpack (errorMessage err) `shouldContain` "@x"
        Right _ -> expectationFailure "impure let right-hand side was accepted"

    it "T-LET-DECL (side condition): an effect inside a JSX attribute is caught" $ do
      -- JSX must PROPAGATE the effects of its attribute and child expressions
      -- rather than flatten them to ·. Rendering does nothing itself, but if a
      -- node reported · regardless of what is inside it, an effectful
      -- expression could be smuggled past this premise and vanish from Δ.
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetJSXAttr() : html {"
        , "  state x, setX default 0;"
        , "  let bad = <div v={setX(addOne)} />;"
        , "  return <div></div>;"
        , "}"
        ]
      case result of
        Left err -> do
          Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'bad'"
          Text.unpack (errorMessage err) `shouldContain` "@x"
        Right _ -> expectationFailure "effectful JSX attribute was accepted in a let"

    it "T-LET-DECL (side condition): an effect inside a JSX child is caught" $ do
      -- Same premise through the child path, which reaches JSX inference by a
      -- different route than attributes do.
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetJSXChild() : html {"
        , "  state x, setX default 0;"
        , "  let bad = <div>{setX(addOne)}</div>;"
        , "  return <div></div>;"
        , "}"
        ]
      case result of
        Left err -> do
          Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'bad'"
          Text.unpack (errorMessage err) `shouldContain` "@x"
        Right _ -> expectationFailure "effectful JSX child was accepted in a let"

    it "T-LET-DECL (side condition): `return e` is a let, so effectful JSX is caught there too" $ do
      -- The parser desugars `return e` into `let returnVar = e`, so the
      -- returned tree is held to the same purity premise as any other let.
      result <- inferSourceEither $ Text.unlines
        [ "comp TReturnJSX() : html {"
        , "  state x, setX default 0;"
        , "  return <div>{setX(addOne)}</div>;"
        , "}"
        ]
      case result of
        Left err ->
          Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'returnVar'"
        Right _ -> expectationFailure "effectful JSX was accepted in a return"

    it "T-LET-DECL (side condition): pure JSX still has effect ·, so it is accepted" $ do
      -- The propagation must not make ordinary rendering look impure: a tree of
      -- pure reads sequences to ·, which is what every paper example returns.
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TPureJSX(b: bool) : html {"
        , "  state x, setX default 0;"
        , "  let ok = <div v={x}><span>y</span></div>;"
        , "  return <div></div>;"
        , "}"
        ]
      okNode <- expectJust "let ok" $ findLetExpr "ok" (typedDeclsOf typedComps 0)
      getType okNode `shouldBe` THtml
      getEffect okNode `shouldBe` EffNone

    it "T-LET-DECL (side condition): JSX around a pure ternary is · + ·, still accepted" $ do
      -- Propagation carries the · + · of a pure ternary child up through the
      -- node (it is never simplified to ·, per the · + · note on
      -- 'enforcePureStateDefault'), so acceptance here rides on the same
      -- SE-PLUS-L path as the non-JSX ternary case below.
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TPureJSXTernary(b: bool) : html {"
        , "  let ok = <div>{b ? <span>y</span> : <span></span>}</div>;"
        , "  return <div></div>;"
        , "}"
        ]
      okNode <- expectJust "let ok" $ findLetExpr "ok" (typedDeclsOf typedComps 0)
      getEffect okNode `shouldBe` EffBranch EffNone EffNone

    it "T-LET-DECL (side condition): a pure-but-non-· RHS (· + ·) is accepted" $ do
      -- Pins the SE-PLUS-L acceptance path of the purity predicate: a pure
      -- ternary's effect is EffBranch EffNone EffNone — NEVER simplified to
      -- · (see the · + · note on 'enforcePureStateDefault') — so a
      -- structural-equality purity check (eff == EffNone) would FALSELY
      -- reject this program while subEffect F EffNone accepts it (both arms
      -- are ≤ ·, so · + · ≤ ·).
      -- The getEffect pin proves the test exercises that path: if the impl
      -- ever starts simplifying · + ·, it fails loudly instead of going
      -- vacuous.
      (sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TLetPureTernary(b: bool) : unit {"
        , "  let u = b ? 1 : 2;"
        , "  return ();"
        , "}"
        ]
      u <- expectJust "let u" $ findLetExpr "u" (typedDeclsOf typedComps 0)
      getType u `shouldBe` TInt
      getEffect u `shouldBe` EffBranch EffNone EffNone
      -- And the accepted let's Δ entry is the usual pure one:
      depsOf sigma "TLetPureTernary" "u" `shouldBe` ["b"]

    it "T-STATE-DECL (side condition): a pure ternary default (· + ·) is accepted" $ do
      -- Same SE-PLUS-L acceptance path through the state-default check: the
      -- default's effect is EffBranch EffNone EffNone ≤ ·. (Acceptance IS the
      -- assertion — a Left here is a false rejection.)
      result <- inferSourceEither $ Text.unlines
        [ "comp TStatePureTernary(b: bool) : int {"
        , "  state x, setX default b ? 1 : 2;"
        , "  return x;"
        , "}"
        ]
      case result of
        Left err -> expectationFailure ("pure ternary default falsely rejected: " <> Text.unpack (errorMessage err))
        Right (sigma, _typedComps) -> cascadeOf sigma "TStatePureTernary" "x" `shouldBe` EffNone

    -- + is a join, so the purity check needs EVERY arm of a ternary to be
    -- ≤ ·. Reading + as a meet (F₁ + F₂ ≤ Fᵢ) would discharge ○¹ʳ@x + · ≤ ·
    -- through the pure arm, letting a ternary smuggle a state change past
    -- T-LET-DECL with @x lost from the inferred effect.
    it "T-LET-DECL (side condition): a ternary with one effectful arm is rejected" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetSneakyTernary(flag: bool) : unit {"
        , "  state x, setX default 0;"
        , "  let v = flag ? setX(addOne) : ();"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'v'"
        Right _ -> expectationFailure "ternary with an effectful arm passed the purity check"

    it "T-LET-DECL (side condition): a ternary with both arms pure is accepted" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetUnitTernary(flag: bool) : unit {"
        , "  state x, setX default 0;"
        , "  let v = flag ? () : ();"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> expectationFailure ("pure ternary falsely rejected: " <> Text.unpack (errorMessage err))
        Right (sigma, _typedComps) -> depsOf sigma "TLetUnitTernary" "v" `shouldBe` ["flag"]

    it "T-LET-DECL (side condition): a ternary with both arms effectful is rejected" $ do
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetEffectfulTernary(flag: bool) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  let v = flag ? setX(addOne) : setY(addOne);"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'v'"
        Right _ -> expectationFailure "ternary with two effectful arms passed the purity check"

    it "T-LET-DECL (side condition): an effect-variable RHS is conservatively rejected" $ do
      -- EffVar is SE-EQ-only, so ?e ≰ ·: an effect-polymorphic function's
      -- latent may instantiate to an impure effect, and the paper (which has
      -- no effect polymorphism) requires ·. Pin the rejection end-to-end
      -- (previously pinned only at the subEffect unit level).
      result <- inferSourceEither $ Text.unlines
        [ "comp TLetEffVar(h: (int -> unit | e)) : unit {"
        , "  let u = h(1);"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> do
          Text.unpack (errorMessage err) `shouldContain` "Impure let right-hand side for 'u'"
          Text.unpack (errorMessage err) `shouldContain` "?e"
        Right _ -> expectationFailure "effect-variable let right-hand side was accepted"

    it "T-ON-DECL: the body is unit-typed with effect F, and every watched variable accounts for F" $ do
      (sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TOn(clk: int, clk2: int) : unit {"
        , "  state x, setX default 0;"
        , "  on clk, clk2 do { setX(addOne) };"
        , "  return ();"
        , "}"
        ]
      -- ∀i, Δ ⊢ @clkᵢ ⇒ F — here realized as each watched variable's Δ
      -- cascade recording the body effect:
      cascadeOf sigma "TOn" "clk" `shouldBe` after1r (at "x")
      cascadeOf sigma "TOn" "clk2" `shouldBe` after1r (at "x")
      -- Γ ⊢ e : unit ∣ F for the block body itself:
      stmts <- expectJust "on-block" $ findOnBlock ["clk", "clk2"] (typedDeclsOf typedComps 0)
      case stmts of
        [s] -> do
          getType s `shouldBe` TUnit
          getEffect s `shouldBe` after1r (at "x")
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-ON-DECL (causes check): discharged by accumulation in the inferred-Δ prototype" $ do
      -- Paper: ∀i ∈ [n], Δ ⊢ @xᵢ ⇒ F is a *check* against a DECLARED Δ. The
      -- prototype INFERS Δ instead: each on-block's effect is ACCUMULATED
      -- into each watched variable's cascade (InferTyEffect.hs DeclEffectF
      -- case: effSeq e combinedEffect), so C-DIRECT's F ≤ Δ(xᵢ) holds by
      -- construction via SE-MULT — there is no rejection to test. The paper's
      -- premise is a consistency condition against a declared Δ, which the
      -- prototype infers rather than receives.
      --
      -- What CAN be pinned is the accumulation itself: two on-blocks on the
      -- same trigger sequence their effects onto its cascade in source order.
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp TOnCauses(clk: int) : unit {"
        , "  state a, setA default 0;"
        , "  state b, setB default 0;"
        , "  on clk do { setA(addOne) };"
        , "  on clk do { setB(addOne) };"
        , "  return ();"
        , "}"
        ]
      cascadeOf sigma "TOnCauses" "clk"
        `shouldBe` seqE [after1r (at "a"), after1r (at "b")]

    it "T-SUBCOMP-DECL: A's Δ is α-renamed with the instance prefix; args and return are wired as dependencies" $ do
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp Inner(v: int) : int {"
        , "  state s, setS default v;"
        , "  on v do { setS((w: int) => { v }) };"
        , "  return s;"
        , "}"
        , "comp Outer(clk: int) : int {"
        , "  comp i = Inner(clk);"
        , "  on i do { () };"
        , "  return i;"
        , "}"
        ]
      let (Sigma sigmaMap) = sigma
      Map.member "Inner" sigmaMap `shouldBe` True
      Map.member "Outer" sigmaMap `shouldBe` True
      -- Inner's own Δ: changing v cascades to ○¹ʳ @s.
      cascadeOf sigma "Inner" "v" `shouldBe` after1r (at "s")
      -- α-renamed into Outer with the "i." prefix.
      cascadeOf sigma "Outer" "i.v" `shouldBe` after1r (at "i.s")
      -- The supplied argument is a same-render cause of the parameter:
      -- Δ ⊢ @clk ⇒ @i.v.
      cascadeOf sigma "Outer" "clk" `shouldBe` at "i.v"
      -- The instance variable depends on Inner's (renamed) return.
      depsOf sigma "Outer" "i" `shouldBe` ["i.s"]

  -- ---------------------------------------------------------------------
  -- §4 Expression-level typing (main text Fig 7; appendix Fig 13)
  -- ---------------------------------------------------------------------
  describe "Expression rules" $ do

    it "T-UNIT: Γ ⊢ () : unit ∣ ·" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TUnit() : unit {"
        , "  let x = ();"
        , "  return x;"
        , "}"
        ]
      x <- expectJust "let x" $ findLetExpr "x" (typedDeclsOf typedComps 0)
      getType x `shouldBe` TUnit
      getEffect x `shouldBe` EffNone

    it "T-BOOL: Γ ⊢ c : bool ∣ ·" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TBool() : bool {"
        , "  let x = true;"
        , "  return x;"
        , "}"
        ]
      x <- expectJust "let x" $ findLetExpr "x" (typedDeclsOf typedComps 0)
      getType x `shouldBe` TBool
      getEffect x `shouldBe` EffNone

    it "T-BASE: Γ ⊢ c : α ∣ · (impl: int and string literals)" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TBase() : int {"
        , "  let i = 42;"
        , "  let s = \"hello\";"
        , "  return i;"
        , "}"
        ]
      i <- expectJust "let i" $ findLetExpr "i" (typedDeclsOf typedComps 0)
      s <- expectJust "let s" $ findLetExpr "s" (typedDeclsOf typedComps 0)
      getType i `shouldBe` TInt
      getEffect i `shouldBe` EffNone
      getType s `shouldBe` TString
      getEffect s `shouldBe` EffNone

    it "T-VAR: Γ, x : τ ⊢ x : τ ∣ ·" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TVar() : int {"
        , "  let x = 42;"
        , "  let y = x;"
        , "  return y;"
        , "}"
        ]
      y <- expectJust "let y" $ findLetExpr "y" (typedDeclsOf typedComps 0)
      getType y `shouldBe` TInt
      getEffect y `shouldBe` EffNone

    it "T-FN: λx. e captures the body effect in the arrow; the closure itself has effect ·" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TFn() : unit {"
        , "  state c, setC default 0;"
        , "  let f = (x: int) => { setC(addOne) };"
        , "  return ();"
        , "}"
        ]
      f <- expectJust "let f" $ findLetExpr "f" (typedDeclsOf typedComps 0)
      getType f `shouldBe` TArrow [] TInt TUnit (after1r (at "c"))
      getEffect f `shouldBe` EffNone

    it "T-FN (pure): a pure body gives a pure latent effect" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TFnPure() : int {"
        , "  let f = (x: int) => { x + 1 };"
        , "  let res = f(0);"
        , "  return res;"
        , "}"
        ]
      f <- expectJust "let f" $ findLetExpr "f" (typedDeclsOf typedComps 0)
      getType f `shouldBe` TArrow [] TInt TInt EffNone
      getEffect f `shouldBe` EffNone

    it "T-APP: e₁ e₂ : τ₂ ∣ F₁ * F₂ * F — application releases the latent effect" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TApp(clk: int) : unit {"
        , "  state c, setC default 0;"
        , "  on clk do { setC(addOne) };"
        , "  return ();"
        , "}"
        ]
      -- The application lives in an on-block (the purity premise): its effect is
      -- · * · * ○¹ʳ @c — e₁ and e₂ are pure, the latent ○¹ʳ @c is released.
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [s] -> do
          getType s `shouldBe` TUnit
          getEffect s `shouldBe` after1r (at "c")
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-APP (pure): applying a pure function composes · effects" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TAppPure() : int {"
        , "  let f = (x: int) => { x + 1 };"
        , "  let res = f(5);"
        , "  return res;"
        , "}"
        ]
      res <- expectJust "let res" $ findLetExpr "res" (typedDeclsOf typedComps 0)
      getType res `shouldBe` TInt
      getEffect res `shouldBe` EffNone

    it "T-SEQ: e₁ ; e₂ : τ₂ ∣ F₁ * F₂ (impl surface: the ;; operator)" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TSeq(clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  on clk do { setX(addOne) ;; setY(addOne) };"
        , "  return ();"
        , "}"
        ]
      -- The ;; sequence lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [s] -> do
          getType s `shouldBe` TUnit
          getEffect s `shouldBe` seqE [after1r (at "x"), after1r (at "y")]
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-BRANCH: if e₁ then e₂ else e₃ : τ ∣ F₁ * (F₂ + F₃)" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TBranch(clk: int, b: bool) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  on clk do { b ? setX(addOne) : setY(addOne) };"
        , "  return ();"
        , "}"
        ]
      -- The ternary lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [s] -> do
          getType s `shouldBe` TUnit
          -- F₁ = · (variable condition), so · * (F₂ + F₃) = F₂ + F₃:
          getEffect s `shouldBe` branchE (after1r (at "x")) (after1r (at "y"))
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-PROD: (e₁, e₂) : τ₁ × τ₂ ∣ F₁ * F₂" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TProd(clk: int) : unit {"
        , "  state x, setX default 0;"
        , "  state y, setY default 0;"
        , "  on clk do { (setX(addOne), setY(addOne)) };"
        , "  return ();"
        , "}"
        ]
      -- The pair lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [p] -> do
          getType p `shouldBe` TPair TUnit TUnit
          getEffect p `shouldBe` seqE [after1r (at "x"), after1r (at "y")]
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-FST: fst e : τ₁ ∣ F (impl surface: e.0)" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TFst() : int {"
        , "  let p = (1, true);"
        , "  let f = p.0;"
        , "  return f;"
        , "}"
        ]
      f <- expectJust "let f" $ findLetExpr "f" (typedDeclsOf typedComps 0)
      getType f `shouldBe` TInt
      getEffect f `shouldBe` EffNone

    it "T-SND: snd e : τ₂ ∣ F (impl surface: e.1; the appendix's τ₁ conclusion is a paper typo)" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TSnd() : bool {"
        , "  let p = (1, true);"
        , "  let s = p.1;"
        , "  return s;"
        , "}"
        ]
      s <- expectJust "let s" $ findLetExpr "s" (typedDeclsOf typedComps 0)
      getType s `shouldBe` TBool
      getEffect s `shouldBe` EffNone

  -- ---------------------------------------------------------------------
  -- §4 Event-layer expression rules
  -- ---------------------------------------------------------------------
  describe "Event-layer expression rules" $ do

    it "T-BIND: bind ℓ⟨v⟩ e : unit ∣ F_e * □ℓ⟨v⟩(F)" $ do
      -- Rule: Γ ⊢ e : (τ → unit | F) ∣ F_e,  τ = Σ_E(ℓ⟨v⟩).
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "event click<#doc> : int;"
        , "comp TBind(clk: int) : unit {"
        , "  state p, setP default 0;"
        , "  let h = (e: int) => { setP(addOne) };"
        , "  on clk do { bind click<#doc> h };"
        , "  return ();"
        , "}"
        ]
      -- The bind lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [u] -> do
          getType u `shouldBe` TUnit
          -- h is a var, so F_e = · and the sequence collapses to the modality;
          -- h's latent effect is ○¹ʳ@p (setP's schema yields that per call).
          getEffect u `shouldBe` EffAlways (EventLabel "click" ["#doc"]) (after1r (at "p"))
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-BIND (F_e): the handler expression's own effect is sequenced before the modality" $ do
      -- Rule shape F_e * □ℓ⟨v⟩(F): evaluating the handler expression itself may
      -- be effectful and F_e must appear BEFORE the modality. (An implementation
      -- that drops F_e passes every other T-BIND test; this one pins it.
      -- Hand-built EffSeq literal on the right — not mkEffSeq — no tautology.)
      -- The handler must be an effectful expression that EVALUATES to a function;
      -- `setQ(addOne) ;; h` does not typecheck (the ;; builtin is unit->unit->unit,
      -- so a sequence cannot return a function), hence the pair-projection idiom:
      -- (h, setQ(addOne)).0 : (int → unit | ○¹ʳ@p) with F_e = ○¹ʳ@q.
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "event click<#doc> : int;"
        , "comp TBindFE(clk: int) : unit {"
        , "  state p, setP default 0;"
        , "  state q, setQ default 0;"
        , "  let h = (e: int) => { setP(addOne) };"
        , "  on clk do { bind click<#doc> (h, setQ(addOne)).0 };"
        , "  return ();"
        , "}"
        ]
      -- The bind lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [u] -> do
          getType u `shouldBe` TUnit
          getEffect u `shouldBe`
            EffSeq [after1r (at "q"), EffAlways (EventLabel "click" ["#doc"]) (after1r (at "p"))]
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-ONCE: once ℓ⟨v⟩ e : unit ∣ F_e * ◇ℓ⟨v⟩(F)" $ do
      -- Same as T-BIND but a one-shot listener → eventually/diamond modality.
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "event timeout<> : unit;"
        , "comp TOnce(clk: int) : unit {"
        , "  state p, setP default 0;"
        , "  on clk do { once timeout<> ((e: unit) => { setP(addOne) }) };"
        , "  return ();"
        , "}"
        ]
      -- The once lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [u] -> do
          getType u `shouldBe` TUnit
          getEffect u `shouldBe` EffEventually (EventLabel "timeout" []) (after1r (at "p"))
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-CANCEL: cancel ℓ⟨v⟩ : unit ∣ ⊘ℓ⟨v⟩" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "event timeout<> : unit;"
        , "comp TCancel(clk: int) : unit {"
        , "  on clk do { cancel timeout<> };"
        , "  return ();"
        , "}"
        ]
      -- The cancel lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [u] -> do
          getType u `shouldBe` TUnit
          getEffect u `shouldBe` EffCancel (EventLabel "timeout" [])
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-REMOVE: remove ℓ⟨v⟩ : unit ∣ ✗ℓ⟨v⟩" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "event timeout<> : unit;"
        , "comp TRemove(clk: int) : unit {"
        , "  on clk do { remove timeout<> };"
        , "  return ();"
        , "}"
        ]
      -- The remove lives in an on-block (the purity premise).
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [u] -> do
          getType u `shouldBe` TUnit
          getEffect u `shouldBe` EffRemove (EventLabel "timeout" [])
        _ -> expectationFailure "expected a single-statement on-block"

    it "T-BIND/T-ONCE/T-CANCEL/T-REMOVE (strict Σ_E): undeclared event labels are rejected" $ do
      -- Σ_E is populated ONLY by top-level event declarations; using any other
      -- label is a type error (owner ruling). A Left from 'inferSourceEither'
      -- is a genuine INFERENCE error — parse errors fail the test outright.
      let progs =
            [ ("bind", "click<#doc>", Text.unlines
                [ "comp PBind() : unit {"
                , "  state p, setP default 0;"
                , "  let h = (e: int) => { setP(addOne) };"
                , "  let u = bind click<#doc> h;"
                , "  return ();"
                , "}"
                ])
            , ("once", "timeout<>", Text.unlines
                [ "comp POnce() : unit {"
                , "  let u = once timeout<> ((e: unit) => { () });"
                , "  return ();"
                , "}"
                ])
            , ("cancel", "timeout<>", Text.unlines
                [ "comp PCancel() : unit {"
                , "  let u = cancel timeout<>;"
                , "  return ();"
                , "}"
                ])
            , ("remove", "timeout<>", Text.unlines
                [ "comp PRemove() : unit {"
                , "  let u = remove timeout<>;"
                , "  return ();"
                , "}"
                ])
            ]
      forM_ progs $ \(name, lbl, prog) -> do
        result <- inferSourceEither prog
        case result of
          Left err -> do
            Text.unpack (errorMessage err) `shouldContain` "Unknown event label"
            Text.unpack (errorMessage err) `shouldContain` lbl
          Right _ -> expectationFailure (name <> " with an undeclared event label was accepted")

    it "T-WF-PROGRAM (Σ_E): duplicate event declarations are rejected" $ do
      result <- inferSourceEither $ Text.unlines
        [ "event click<#doc> : int;"
        , "event click<#doc> : bool;"
        , "comp PDup() : unit {"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "Duplicate event declaration"
        Right _ -> expectationFailure "duplicate event declarations were accepted"

    it "T-BIND (payload mismatch): the closure's parameter type must equal Σ_E(ℓ⟨v⟩)" $ do
      result <- inferSourceEither $ Text.unlines
        [ "event click<#doc> : int;"
        , "comp PBindBad() : unit {"
        , "  let h = (e: bool) => { () };"
        , "  let u = bind click<#doc> h;"
        , "  return ();"
        , "}"
        ]
      case result of
        -- Pin the REASON: a unification failure, not an incidental error
        -- (and definitely not the strict-label check — the label is declared).
        Left err -> do
          Text.unpack (errorMessage err) `shouldContain` "Type mismatch"
          Text.unpack (errorMessage err) `shouldNotContain` "Unknown event label"
        Right _ -> expectationFailure "a handler whose parameter type differs from the payload was accepted"

    it "T-BIND (return-type mismatch): the closure must return unit" $ do
      -- The rule's handler type is (τ → unit | F); a handler returning int must
      -- be rejected (pins the retTy ~ unit unification, which the positive
      -- tests only exercise on the success path).
      result <- inferSourceEither $ Text.unlines
        [ "event click<#doc> : int;"
        , "comp PBindRet() : unit {"
        , "  let u = bind click<#doc> ((e: int) => { 42 });"
        , "  return ();"
        , "}"
        ]
      case result of
        Left err -> Text.unpack (errorMessage err) `shouldContain` "Type mismatch"
        Right _ -> expectationFailure "a handler returning int (not unit) was accepted"

  -- ---------------------------------------------------------------------
  -- §5 The "causes" judgement Δ ⊢ @x ⇒ F (main text §5.1; appendix Fig 14)
  --
  -- The impl has no separate causes judgement; its analogue is that the
  -- inferred Δ, expanded by fullEffect/fullEffectVar, contains exactly the
  -- effects each variable causes. These tests pin that behavior.
  -- ---------------------------------------------------------------------
  describe "Causes judgement (realized via Δ expansion)" $ do

    it "C-DIRECT: x causes F when Δ's cascade for x is at least F (x[…] ∣ F′ ∈ Δ, F ≤ F′)" $ do
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp CDirect(clk: int) : unit {"
        , "  state y, setY default 0;"
        , "  on clk do { setY(addOne) };"
        , "  return ();"
        , "}"
        ]
      fullEffectVar (deltaOf sigma "CDirect") "clk" `shouldBe` after1r (at "y")

    it "C-DEP: x causes @y when y lists x among its dependencies" $ do
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp CDep() : int {"
        , "  state x, setX default 0;"
        , "  let y = x + 1;"
        , "  return y;"
        , "}"
        ]
      fullEffect (deltaOf sigma "CDep") (at "x") `shouldBe` seqE [at "x", at "y"]

    it "C-SEQ: 'causes' closes under sequencing (Δ ⊢ @x ⇒ F₁ * F₂)" $ do
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp CSeq(clk: int) : unit {"
        , "  state a, setA default 0;"
        , "  state b, setB default 0;"
        , "  on clk do { setA(addOne); setB(addOne) };"
        , "  return ();"
        , "}"
        ]
      fullEffectVar (deltaOf sigma "CSeq") "clk"
        `shouldBe` seqE [after1r (at "a"), after1r (at "b")]

  -- ---------------------------------------------------------------------
  -- §6 Sub-effecting F ≤ F′ (appendix Fig 15)
  --
  -- The relation is implemented as the pure decision procedure
  -- 'Analysis.Common.subEffect', which decides the closure of the printed
  -- rules: SE-TRANS is folded into the structural recursion and SE-SPLIT-L/R
  -- are handled up front by same-unit delay-merge normalization. These tests
  -- call 'subEffect' directly on hand-built effect trees; inference uses the
  -- relation as the purity predicate for T-STATE-DECL / T-LET-DECL.
  -- ---------------------------------------------------------------------
  describe "Sub-effecting (Analysis.Common.subEffect)" $ do
    let click = EventLabel "click" ["#doc"]
        timeoutLbl = EventLabel "timeout" []

    it "SE-EQ: F ≤ F′ when F = F′ (reflexivity)" $ do
      subEffect (after1r (at "x")) (after1r (at "x")) `shouldBe` True
      -- Effect variables are SE-EQ-only: equal variables relate, but a
      -- variable never relates to a concrete effect.
      subEffect (EffVar (EffVarName "e")) (EffVar (EffVarName "e")) `shouldBe` True
      subEffect (EffVar (EffVarName "e")) (at "x") `shouldBe` False
      subEffect (at "x") (EffVar (EffVarName "e")) `shouldBe` False
      subEffect (at "x") (at "y") `shouldBe` False

    it "SE-TRANS: F ≤ F′ and F′ ≤ F″ implies F ≤ F″" $ do
      -- TRANS is folded into the structural recursion of 'subEffect'; these
      -- verdicts need it explicitly in the printed system:
      --   · ≤ ℓ⟨v⟩ (SE-SUBEFFECTING-NSE) and ℓ⟨v⟩ ≤ ℓ⟨v⟩ * ⊘ℓ⟨v⟩ (SE-MULT),
      --   hence · ≤ ℓ⟨v⟩ * ⊘ℓ⟨v⟩ (SE-TRANS).
      subEffect EffNone (seqE [EffEvent click, EffCancel click]) `shouldBe` True
      --   · ≤ @x (SE-SUBEFFECTING) and @x ≤ ○⁰@x (SE-ZERO-R), hence · ≤ ○⁰@x.
      subEffect EffNone (EffAfter (Time 0 Renders) (at "x")) `shouldBe` True
      subEffect (at "x") (at "y") `shouldBe` False

    it "SE-PLUS-R: F ≤ Fᵢ implies F ≤ F₁ + F₂ (each arm is below the branch)" $ do
      -- F ≤ F₁ suffices; so does F ≤ F₂
      subEffect (at "x") (branchE (at "x") (at "y")) `shouldBe` True
      subEffect (at "y") (branchE (at "x") (at "y")) `shouldBe` True
      subEffect EffNone (branchE (at "x") (EffEvent click)) `shouldBe` True
      -- the premise itself may go through SE-MULT
      subEffect (at "x") (branchE (at "z") (seqE [at "x", at "y"])) `shouldBe` True
      -- F must be below at least one arm
      subEffect (at "z") (branchE (at "x") (at "y")) `shouldBe` False

    it "SE-PLUS-L: F₁ ≤ F′ and F₂ ≤ F′ implies F₁ + F₂ ≤ F′ (+ is a join)" $ do
      subEffect (branchE EffNone EffNone) EffNone `shouldBe` True
      subEffect (branchE EffNone (at "x")) (at "x") `shouldBe` True
      subEffect (branchE (at "x") (at "y")) (seqE [at "x", at "y"]) `shouldBe` True
      -- branch commutativity is derivable (PLUS-L, then PLUS-R per arm)
      subEffect (branchE (at "x") (at "y")) (branchE (at "y") (at "x")) `shouldBe` True
      -- the old, unsound direction is gone: a branch is NOT below one of its
      -- arms, because that would lose the other arm (reviewer B's objection)
      subEffect (branchE (at "x") (at "y")) (at "x") `shouldBe` False
      subEffect (branchE (at "x") (at "y")) (at "y") `shouldBe` False
      subEffect (branchE (after1r (at "x")) EffNone) EffNone `shouldBe` False

    it "SE-MULT: F ≤ Fᵢ implies F ≤ F₁ * F₂ (* is a join)" $ do
      subEffect (at "x") (seqE [at "x", at "y"]) `shouldBe` True
      subEffect (at "y") (seqE [at "x", at "y"]) `shouldBe` True
      subEffect (at "z") (seqE [at "x", at "y"]) `shouldBe` False
      -- There is NO *-left rule beyond SE-EQ — no monotonicity and no
      -- right-weakening of sequences: a sequence on the left only relates to
      -- itself.
      subEffect (seqE [at "x", at "z"]) (seqE [at "y", at "z"]) `shouldBe` False
      subEffect (seqE [at "x", at "z"]) (seqE [at "x", at "z", at "w"]) `shouldBe` False

    it "SE-ZERO-L: ○⁰ F ≤ F′ when F ≤ F′" $ do
      subEffect (EffAfter (Time 0 Renders) (at "x")) (at "x") `shouldBe` True
      -- combines with SE-MULT: ○⁰@x ≤ @x * @y
      subEffect (EffAfter (Time 0 Renders) (at "x")) (seqE [at "x", at "y"]) `shouldBe` True
      subEffect (EffAfter (Time 0 Renders) (at "x")) (at "y") `shouldBe` False

    it "SE-ZERO-R: F ≤ ○⁰ F′ when F ≤ F′" $ do
      subEffect (at "x") (EffAfter (Time 0 Renders) (at "x")) `shouldBe` True
      subEffect (at "x") (EffAfter (Time 0 Renders) (at "y")) `shouldBe` False
      -- Only grade 0 strips: there is NO printed rule deriving · ≤ ○ᵗF′
      -- (or @x ≤ ○ᵗ@x) for t ≠ 0.
      subEffect EffNone (after1r (at "x")) `shouldBe` False
      subEffect (at "x") (after1r (at "x")) `shouldBe` False

    it "SE-DELAY: ○ᵗ F ≤ ○ᵗ′ F′ when (○^(t−t′) F) ≤ F′ and t ≤ t′" $ do
      -- NOTE (owner-pinned reading): the printed premise really is
      -- (○^(t−t′) F) ≤ F′ with t ≤ t′ (verified against the rendered
      -- willow-preprint.pdf page 31, Fig 15) — as printed the grade t−t′ is NEGATIVE,
      -- unrepresentable in the impl's Delay (Time Int Unit, Int ≥ 0 surface
      -- values). Reading grades as a group, the premise is equivalent (by
      -- SE-DELAY-EQ + SE-SPLIT + SE-ZERO) to the positive-rebase form
      -- F ≤ ○^(t′−t) F′, which is what 'subEffect' implements for t < t′.
      -- For simple Time grades that branch is observably VACUOUS: its premise
      -- only holds when it collapses to SE-EQ, which delay-merge
      -- normalization already handles — so different grades are incomparable
      -- beyond equality:
      subEffect (after1r (at "x")) (EffAfter (Time 2 Renders) (at "x")) `shouldBe` False
      subEffect (EffAfter (Time 2 Renders) (at "x")) (after1r (at "x")) `shouldBe` False
      -- but the SPLIT-derived equality holds (○¹ʳ○¹ʳ@x merges to ○²ʳ@x):
      subEffect (after1r (after1r (at "x"))) (EffAfter (Time 2 Renders) (at "x")) `shouldBe` True
      -- cross-unit delays have no printed rule: False in both directions
      subEffect (after1r (at "x")) (EffAfter (Time 100 Millis) (at "x")) `shouldBe` False
      subEffect (EffAfter (Time 100 Millis) (at "x")) (after1r (at "x")) `shouldBe` False

    it "SE-DELAY-EQ: ○ᵗ F ≤ ○ᵗ F′ when F ≤ F′ (monotone delay)" $ do
      subEffect (after1r EffNone) (after1r (at "x")) `shouldBe` True
      subEffect (after1r (at "x")) (after1r (at "y")) `shouldBe` False

    it "SE-SPLIT-L: ○^(t₁+t₂) F ≤ ○ᵗ¹ ○ᵗ² F (grades split, same unit only)" $ do
      subEffect (EffAfter (Time 2 Renders) (at "x")) (after1r (after1r (at "x"))) `shouldBe` True
      subEffect (EffAfter (Time 2 Renders) (at "x")) (after1r (after1r (at "y"))) `shouldBe` False
      -- same-unit only: 2 renders is not 1 render + 100ms
      subEffect (EffAfter (Time 2 Renders) (at "x"))
        (after1r (EffAfter (Time 100 Millis) (at "x"))) `shouldBe` False

    it "SE-SPLIT-R: ○ᵗ¹ ○ᵗ² F ≤ ○^(t₁+t₂) F (grades merge, same unit only)" $ do
      subEffect (after1r (after1r (at "x"))) (EffAfter (Time 2 Renders) (at "x")) `shouldBe` True
      -- same-unit Plus-of-Times grades fold too (parser produces Plus delays)
      subEffect (EffAfter (Plus (Time 1 Renders) (Time 1 Renders)) (at "x"))
        (EffAfter (Time 2 Renders) (at "x")) `shouldBe` True
      -- cross-unit nestings stay untouched: no reordering rule either
      subEffect (after1r (EffAfter (Time 100 Millis) (at "x")))
        (EffAfter (Time 100 Millis) (after1r (at "x"))) `shouldBe` False

    it "SE-SUBEFFECTING: · ≤ @x" $ do
      subEffect EffNone (at "x") `shouldBe` True
      subEffect (at "x") EffNone `shouldBe` False
      -- EffLoop is not among the printed ·-refinement leaves
      subEffect EffNone (EffLoop "l") `shouldBe` False

    it "SE-SUBEFFECTING-NSE: · ≤ ℓ⟨v⟩" $ do
      subEffect EffNone (EffEvent click) `shouldBe` True
      subEffect (EffEvent click) EffNone `shouldBe` False

    it "SE-SUBEFFECTING-EVENTUALLY: · ≤ ◇ℓ⟨v⟩(F)" $ do
      subEffect EffNone (EffEventually timeoutLbl (after1r (at "p"))) `shouldBe` True
      subEffect (EffEventually timeoutLbl (after1r (at "p"))) EffNone `shouldBe` False

    it "SE-SUBEFFECTING-ALWAYS: · ≤ □ℓ⟨v⟩(F)" $ do
      subEffect EffNone (EffAlways click (after1r (at "p"))) `shouldBe` True
      subEffect (EffAlways click (after1r (at "p"))) EffNone `shouldBe` False

    it "SE-SUBEFFECTING-CANCEL: · ≤ ⊘ℓ⟨v⟩" $ do
      subEffect EffNone (EffCancel timeoutLbl) `shouldBe` True
      subEffect (EffCancel timeoutLbl) EffNone `shouldBe` False

    it "SE-SUBEFFECTING-REMOVE: · ≤ ✗ℓ⟨v⟩" $ do
      subEffect EffNone (EffRemove timeoutLbl) `shouldBe` True
      subEffect (EffRemove timeoutLbl) EffNone `shouldBe` False

    it "SE-EVENTUALLY-BODY: ◇ℓ⟨v⟩(F) ≤ ◇ℓ⟨v⟩(F′) when F ≤ F′ (monotone body)" $ do
      subEffect (EffEventually click EffNone) (EffEventually click (at "x")) `shouldBe` True
      -- labels must match
      subEffect (EffEventually click EffNone) (EffEventually timeoutLbl EffNone) `shouldBe` False
      -- bodies must relate
      subEffect (EffEventually click (at "x")) (EffEventually click (at "y")) `shouldBe` False

    it "SE-ALWAYS-BODY: □ℓ⟨v⟩(F) ≤ □ℓ⟨v⟩(F′) when F ≤ F′ (monotone body)" $ do
      subEffect (EffAlways click EffNone) (EffAlways click (at "x")) `shouldBe` True
      subEffect (EffAlways click (at "x")) (EffAlways click (at "y")) `shouldBe` False
      -- ◇ and □ are different modalities: no cross rule
      subEffect (EffEventually click (at "x")) (EffAlways click (at "x")) `shouldBe` False

  -- ---------------------------------------------------------------------
  -- Effect algebra (implementation mechanics behind the effect grammar)
  -- ---------------------------------------------------------------------
  describe "Effect algebra" $ do

    it "ALGEBRA-IDEMPOTENCE: state changes dedup (@x * @x = @x) but event effects must not (ℓ⟨v⟩ * ℓ⟨v⟩ ≠ ℓ⟨v⟩)" $ do
      -- Owner ruling (2026-07-17): state changes are idempotent, event effects
      -- are NOT, and effect variables conservatively are NOT (they may
      -- instantiate to event effects). 'mkEffSeq' dedups only effects whose
      -- entire tree is idempotent ('isIdempotentEffect').
      -- State changes dedup (here, through simplifyEffect):
      simplifyEffect (effSeq (at "x") (at "x")) `shouldBe` at "x"
      -- Event effects do NOT dedup: both firings are kept. NOTE: the RHS is
      -- the hand-built EffSeq literal, NOT mkEffSeq — comparing effSeq against
      -- mkEffSeq would be a tautology (effSeq is defined via mkEffSeq).
      let ev = EffEvent (EventLabel "timeout" [])
      effSeq ev ev `shouldBe` EffSeq [ev, ev]
      -- Effect variables do NOT dedup either.
      let v = EffVar (EffVarName "e")
      effSeq v v `shouldBe` EffSeq [v, v]
      -- A fully idempotent tree (○¹ʳ@x) dedups to a single copy.
      effSeq (after1r (at "x")) (after1r (at "x")) `shouldBe` after1r (at "x")

  -- ---------------------------------------------------------------------
  -- §1–2 Structural rules (program/component well-formedness, decl blocks)
  -- ---------------------------------------------------------------------
  describe "Structural rules" $ do

    it "T-DECLS: declarations sequence, each extending the typing environment for the next" $ do
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TDecls() : int {"
        , "  let a = 1;"
        , "  let b = a + 1;"
        , "  return b;"
        , "}"
        ]
      b <- expectJust "let b" $ findLetExpr "b" (typedDeclsOf typedComps 0)
      getType b `shouldBe` TInt  -- b's type flows through the extended Γ

    it "T-COMPONENT: arguments seed Γ and Δ for the body" $ do
      (sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp TComponent(a: int) : int {"
        , "  return a;"
        , "}"
        ]
      getType (typedReturnOf typedComps 0) `shouldBe` TInt
      depsOf sigma "TComponent" "a" `shouldBe` []

    it "T-WF-COMP: a checked component's (code, Δ, Γ) is threaded into the signature" $ do
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp TWFComp() : int {"
        , "  state c, setC default 0;"
        , "  return c;"
        , "}"
        ]
      -- The signature entry records the inferred Δ for the component.
      depsOf sigma "TWFComp" "c" `shouldBe` []
      cascadeOf sigma "TWFComp" "c" `shouldBe` EffNone

    it "T-WF-PROGRAM: components check in order; later components see earlier ones in Σ" $ do
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "comp Helper() : int {"
        , "  let value = 10;"
        , "  return value;"
        , "}"
        , "comp Main() : int {"
        , "  comp h = Helper();"
        , "  return h;"
        , "}"
        ]
      let (Sigma sigmaMap) = sigma
      Map.member "Helper" sigmaMap `shouldBe` True
      Map.member "Main" sigmaMap `shouldBe` True
      -- Main could only use Helper because Helper's entry was threaded in.
      depsOf sigma "Main" "h" `shouldBe` ["h.value"]
