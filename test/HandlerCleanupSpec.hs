-- | The §5.4 "event handlers cleaned up" analysis
-- ("Analysis.HandlerCleanup"): a walk over an effect's graph checking that
-- every handler registration is matched by a @remove@ modality.
--
-- The paper's own worked case (asyncCompute) is asserted end-to-end in
-- "PaperExamplesSpec"; these tests pin the walk itself, clause by clause, on
-- hand-built effect trees.
module HandlerCleanupSpec (spec) where

import Import
import Analysis.HandlerCleanup
import Test.Hspec

click :: EventLabel
click = EventLabel "click" ["#doc"]

timerLbl :: EventLabel
timerLbl = EventLabel "timeout" []

other :: EventLabel
other = EventLabel "keydown" ["#doc"]

after1r :: Effect -> Effect
after1r = EffAfter (Time 1 Renders)

-- | The labels+kinds reported stale, ignoring the qualifier flags.
staleOf :: Effect -> [(EventLabel, HandlerKind)]
staleOf eff = [(staleLabel sh, staleKind sh) | sh <- crStale (cleanupReport eff)]

spec :: Spec
spec = describe "Event handler cleanup analysis (§5.4)" $ do

  describe "the basic matching rule" $ do
    it "a bind with no remove is stale" $ do
      let eff = EffAlways click (after1r (EffStateChange "position"))
      staleOf eff `shouldBe` [(click, Persistent)]
      handlersCleanedUp eff `shouldBe` False

    it "a once with no remove is stale" $ do
      let eff = EffEventually timerLbl (after1r (EffStateChange "slow"))
      staleOf eff `shouldBe` [(timerLbl, OneShot)]

    it "remove-then-bind (the §2 idiom) is clean" $ do
      -- ✗click⟨#doc⟩ * □click⟨#doc⟩(○¹ʳ @position) — MovingDot's shape. The
      -- remove comes FIRST, which is exactly what §2 (ii) calls cleaned up, so
      -- matching must not be order-sensitive.
      let eff = EffSeq
            [ EffRemove click
            , EffAlways click (after1r (EffStateChange "position"))
            ]
      handlersCleanedUp eff `shouldBe` True

    it "bind-then-remove is clean too" $ do
      handlersCleanedUp (EffSeq [EffAlways click EffNone, EffRemove click])
        `shouldBe` True

    it "a remove for a different label does not discharge the registration" $ do
      staleOf (EffSeq [EffRemove other, EffAlways click EffNone])
        `shouldBe` [(click, Persistent)]

    it "an effect with no registrations is trivially clean" $ do
      let eff = EffSeq [after1r (EffStateChange "x"), EffEvent click]
      cleanupReport eff `shouldBe` CleanupReport [] []

  describe "cancel is not remove" $ do
    it "⊘ℓ⟨v⟩ alone leaves the handler registered" $ do
      -- setTimeout without clearTimeout's ✗ half: cancel suppresses the
      -- pending firing, it does not unregister.
      staleOf (EffSeq [EffCancel timerLbl, EffEventually timerLbl EffNone])
        `shouldBe` [(timerLbl, OneShot)]

    it "clearTimeout's ⊘ * ✗ pair does discharge it" $ do
      -- Debounce's cascade: ⊘timeout⟨⟩ * ✗timeout⟨⟩ * ◇timeout⟨⟩(○¹ʳ @slow)
      --   * ○¹⁰⁰ᵐˢ timeout⟨⟩
      let eff = EffSeq
            [ EffCancel timerLbl
            , EffRemove timerLbl
            , EffEventually timerLbl (after1r (EffStateChange "slow"))
            , EffAfter (Time 100 Millis) (EffEvent timerLbl)
            ]
      handlersCleanedUp eff `shouldBe` True

  describe "walking both branches of + separately" $ do
    it "a remove on only one branch leaves the other branch stale" $ do
      let eff = EffBranch
            (EffSeq [EffAlways click EffNone, EffRemove click])
            (EffAlways click EffNone)
      staleOf eff `shouldBe` [(click, Persistent)]

    it "and reports it as branch-specific, not unconditional" $ do
      let eff = EffBranch
            (EffSeq [EffAlways click EffNone, EffRemove click])
            (EffAlways click EffNone)
      map staleEveryBranch (crStale (cleanupReport eff)) `shouldBe` [False]

    it "a remove sequenced before a branch covers both branches" $ do
      -- ✗click⟨#doc⟩ * (□click⟨#doc⟩(○¹ʳ @position) + ·) — MovingDot's
      -- conditional bind, which §2 (iii) reports as correctly cleaned up.
      let eff = EffSeq
            [ EffRemove click
            , EffBranch (EffAlways click (after1r (EffStateChange "position"))) EffNone
            ]
      handlersCleanedUp eff `shouldBe` True

    it "a registration on one branch and its remove on the other is stale" $ do
      -- The two are never on the same path, so neither discharges the other.
      staleOf (EffBranch (EffAlways click EffNone) (EffRemove click))
        `shouldBe` [(click, Persistent)]

  describe "looking inside the □ and ◇ modalities" $ do
    it "a remove inside a modality body discharges an outer registration" $ do
      -- This is the clause that makes asyncCompute come out clean.
      let eff = EffSeq
            [ EffEventually click EffNone
            , EffEventually other (EffRemove click)
            , EffRemove other
            ]
      handlersCleanedUp eff `shouldBe` True

    it "a registration inside a modality body is checked too" $ do
      staleOf (EffSeq [EffRemove other, EffAlways other (EffAlways click EffNone)])
        `shouldBe` [(click, Persistent)]

    it "asyncCompute's mutual removes leave nothing behind (§5.4)" $ do
      -- ○¹ᵘ(comp⟨suc⟩ + comp⟨err⟩) * ◇comp⟨suc⟩(F1 * ✗comp⟨err⟩)
      --   * ◇comp⟨err⟩(F2 * ✗comp⟨suc⟩)
      let suc = EventLabel "comp" ["suc"]
          err = EventLabel "comp" ["err"]
          eff = EffSeq
            [ EffAfter (Time 1 Compute) (EffBranch (EffEvent suc) (EffEvent err))
            , EffEventually suc (EffSeq [after1r (EffStateChange "x"), EffRemove err])
            , EffEventually err (EffSeq [after1r (EffStateChange "y"), EffRemove suc])
            ]
      handlersCleanedUp eff `shouldBe` True
      crHandlers (cleanupReport eff)
        `shouldBe` [(err, OneShot), (suc, OneShot)]

  describe "effects the walk cannot see through" $ do
    it "flags an unmatched registration under ?e as unconfirmed" $ do
      let eff = EffSeq [EffAlways click EffNone, EffVar (EffVarName "F")]
      map staleUnderVar (crStale (cleanupReport eff)) `shouldBe` [True]

    it "but an explicit remove still settles it, ?e or not" $ do
      handlersCleanedUp (EffSeq [EffAlways click EffNone, EffVar (EffVarName "F"), EffRemove click])
        `shouldBe` True

    it "treats a loop[x] cut-off the same way" $ do
      let eff = EffSeq [EffAlways click EffNone, EffLoop "x"]
      map staleUnderVar (crStale (cleanupReport eff)) `shouldBe` [True]

  describe "a firing event does not count as cleanup" $ do
    it "◇ℓ⟨v⟩ is not discharged by ℓ⟨v⟩ being promised to fire" $ do
      -- A one-shot handler is consumed when it fires, but the paper's rule
      -- asks for a remove; staying conservative here is the safe direction.
      staleOf (EffSeq [EffEventually timerLbl EffNone, EffAfter (Time 100 Millis) (EffEvent timerLbl)])
        `shouldBe` [(timerLbl, OneShot)]

  describe "the same label bound both ways" $ do
    it "reports □ and ◇ registrations separately" $ do
      staleOf (EffSeq [EffAlways click EffNone, EffEventually click EffNone])
        `shouldBe` [(click, Persistent), (click, OneShot)]

    it "and one remove discharges both" $ do
      handlersCleanedUp (EffSeq [EffAlways click EffNone, EffEventually click EffNone, EffRemove click])
        `shouldBe` True
