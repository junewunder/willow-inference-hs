-- | The initial-render analysis ("Analysis.InitialRender"): what a component
-- does when it mounts, split by the event-layer modalities into the part that
-- settles, the handlers left armed, and the events already scheduled.
--
-- The paper examples are asserted end-to-end in "PaperExamplesSpec"; these
-- tests pin the split itself, clause by clause, on hand-built effect trees.
module InitialRenderSpec (spec) where

import Import
import Analysis.InitialRender
import Analysis.HandlerCleanup (HandlerKind (..))
import Test.Hspec

click :: EventLabel
click = EventLabel "click" ["#doc"]

timerLbl :: EventLabel
timerLbl = EventLabel "timeout" []

after1r :: Effect -> Effect
after1r = EffAfter (Time 1 Renders)

spec :: Spec
spec = describe "Initial render analysis" $ do

  describe "what settles" $ do
    it "keeps state changes and the delays between them" $ do
      let eff = after1r (EffStateChange "x")
      settlingEffect eff `shouldBe` after1r (EffStateChange "x")
      settleTime (settlingEffect eff) `shouldBe` [(1, Renders)]

    it "drops a □ body: a bound handler waits for its event" $ do
      -- MovingDot's shape. The ○¹ʳ @position inside the □ does NOT run at
      -- mount, so nothing settles even though the effect mentions a state
      -- change.
      let eff = EffSeq
            [ EffRemove click
            , EffAlways click (after1r (EffStateChange "position"))
            ]
      settlingEffect eff `shouldBe` EffNone
      armedHandlers eff `shouldBe` [(click, Persistent)]

    it "drops a ◇ body for the same reason" $ do
      settlingEffect (EffEventually timerLbl (after1r (EffStateChange "slow")))
        `shouldBe` EffNone

    it "drops ⊘ and ✗, which only touch the handler table" $ do
      settlingEffect (EffSeq [EffCancel timerLbl, EffRemove timerLbl])
        `shouldBe` EffNone

    it "prunes a delay left empty by dropping its body" $ do
      -- setTimeout's ○¹⁰⁰ᵐˢ timeout⟨⟩ has its firing removed as scheduled, and
      -- the bare ○¹⁰⁰ᵐˢ · that remains is not something to print.
      settlingEffect (EffAfter (Time 100 Millis) (EffEvent timerLbl))
        `shouldBe` EffNone

    it "prunes a branch whose arms both emptied out" $ do
      settlingEffect (EffBranch (EffAlways click EffNone) EffNone)
        `shouldBe` EffNone

    it "but keeps a branch as soon as one arm carries something" $ do
      -- TextInput's (?F + ·): the caller's effect may or may not run, which is
      -- a real thing to report.
      let eff = EffBranch (EffVar (EffVarName "F")) EffNone
      settlingEffect eff `shouldBe` eff

  describe "settle time" $ do
    it "adds delays along a path" $ do
      settleTime (after1r (after1r (EffStateChange "x")))
        `shouldBe` [(2, Renders)]

    it "takes the worst case across a branch" $ do
      let eff = EffBranch
            (after1r (EffStateChange "x"))
            (EffAfter (Time 3 Renders) (EffStateChange "y"))
      settleTime eff `shouldBe` [(3, Renders)]

    it "maximizes across a sequence rather than summing it" $ do
      -- The operands of * start at the same moment; only nesting under ○
      -- advances the clock.
      let eff = EffSeq
            [ after1r (EffStateChange "x")
            , EffAfter (Time 2 Renders) (EffStateChange "y")
            ]
      settleTime eff `shouldBe` [(2, Renders)]

    it "accumulates units separately, since they do not convert" $ do
      let eff = after1r (EffAfter (Time 1 NetworkReq) (EffStateChange "x"))
      settleTime eff `shouldBe` [(1, Renders), (1, NetworkReq)]
      describeSettleTime (settleTime eff) `shouldBe` "1r + 1n"

    it "reports an immediate mount as such" $ do
      describeSettleTime (settleTime (EffStateChange "x")) `shouldBe` "immediate"

  describe "armed handlers" $ do
    it "agrees with the cleanup analysis about what counts as a registration" $ do
      let eff = EffSeq [EffAlways click EffNone, EffEventually timerLbl EffNone]
      armedHandlers eff `shouldBe` [(click, Persistent), (timerLbl, OneShot)]

    it "finds a handler armed inside another handler's body" $ do
      armedHandlers (EffAlways click (EffEventually timerLbl EffNone))
        `shouldBe` [(click, Persistent), (timerLbl, OneShot)]

  describe "scheduled events" $ do
    it "reports a promised firing with the delay it arrives after" $ do
      scheduledEvents (EffAfter (Time 100 Millis) (EffEvent timerLbl))
        `shouldBe` [(timerLbl, [[(100, Millis)]])]

    it "does not descend into a modality body" $ do
      -- A firing inside a □/◇ body happens when that handler runs, which is
      -- not mount's business.
      scheduledEvents (EffAlways click (EffAfter (Time 100 Millis) (EffEvent timerLbl)))
        `shouldBe` []

    it "collects every distinct arrival time for the same event" $ do
      -- Branches can issue the same request at different times.
      let eff = EffBranch
            (EffAfter (Time 1 NetworkReq) (EffEvent timerLbl))
            (after1r (EffAfter (Time 1 NetworkReq) (EffEvent timerLbl)))
      scheduledEvents eff
        `shouldBe` [(timerLbl, [[(1, NetworkReq)], [(1, Renders), (1, NetworkReq)]])]

  describe "loops on mount" $ do
    it "names the state variables the settling part loops through" $ do
      settleLoops (after1r (EffSeq [EffStateChange "y", after1r (EffLoop "x")]))
        `shouldBe` ["x"]

    it "a loop reached on every path means mount never finishes" $ do
      -- MutualRecursion: both blocks loop and neither is guarded.
      let eff = EffSeq
            [ after1r (EffSeq [EffStateChange "y", after1r (EffLoop "x")])
            , after1r (EffSeq [EffStateChange "x", after1r (EffLoop "y")])
            ]
      alwaysLoops eff `shouldBe` True

    it "one non-looping operand of * does not rescue the mount" $ do
      -- Everything under * happens, so a single non-terminating operand hangs
      -- the mount regardless of the others.
      alwaysLoops (EffSeq [EffStateChange "x", EffLoop "y"]) `shouldBe` True

    it "a branch that escapes downgrades it to 'may not settle'" $ do
      -- UsernameInputFixed's guarded retry cycle: the block bails with () when
      -- a request is already in flight, so one arm terminates.
      let eff = EffBranch EffNone (after1r (EffLoop "status"))
      settleLoops eff `shouldBe` ["status"]
      alwaysLoops eff `shouldBe` False

    it "a loop inside a modality body is not a mount loop at all" $ do
      -- It needs its event to fire first, so it never runs during mount.
      settleLoops (settlingEffect (EffAlways click (EffLoop "x"))) `shouldBe` []
