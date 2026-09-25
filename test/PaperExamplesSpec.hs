-- | The paper's worked examples as whole-program tests. Test names carry the
-- example IDs the paper uses (EX-SETTER-SEQ, EX-MOVINGDOT, …) and assert the
-- effects the paper says Willow infers.
--
-- These exercise the whole language: the event layer (bind/once/cancel/remove,
-- the □ ◇ ⊘ ✗ modalities, event effects, event decls / Σ_E), the paper's timer
-- builtins, the sub-effecting decision procedure, the Compute time unit @u@,
-- the @asyncCompute@/@fetchUsernameCheck@/@has@ builtins, and the
-- @examples/paper/@ files. The T-STATE-DECL / T-LET-DECL purity premises mean
-- every effectful expression in these programs lives in an on-block body;
-- their own tests live in "PaperRulesSpec".
module PaperExamplesSpec (spec) where

import Import
import PaperHarness
import Analysis.Common (fullEffectVar, hasLoopsInEffect)
import Analysis.HandlerCleanup (handlersCleanedUp)
import Test.Hspec
import Control.Comonad.Cofree (Cofree(..))
import qualified RIO.Map as Map
import qualified RIO.Text as Text

-- | Read and infer @examples/paper/UsernameInput.txt@ (the §7 file:
-- Debounce + the buggy UsernameInput + the fixed UsernameInputFixed).
inferUsernameInput :: IO (Sigma, [([AnnotatedDeclaration], AnnotatedNode)])
inferUsernameInput = readFileUtf8 "examples/paper/UsernameInput.txt" >>= inferSource

spec :: Spec
spec = describe "Paper worked examples" $ do

  it "EX-SETTER-SEQ: setX(f); setY(f) infers ○¹ʳ @x * ○¹ʳ @y" $ do
    (sigma, _typedComps) <- inferSource $ Text.unlines
      [ "comp SetterSeq(clk: int) : unit {"
      , "  state x, setX default 0;"
      , "  state y, setY default 0;"
      , "  on clk do { setX(addOne); setY(addOne) };"
      , "  return ();"
      , "}"
      ]
    cascadeOf sigma "SetterSeq" "clk"
      `shouldBe` seqE [after1r (at "x"), after1r (at "y")]

  it "EX-SETTER-BRANCH: if b then setX(f) else setY(f) infers ○¹ʳ @x + ○¹ʳ @y" $ do
    (sigma, _typedComps) <- inferSource $ Text.unlines
      [ "comp SetterBranch(clk: int, b: bool) : unit {"
      , "  state x, setX default 0;"
      , "  state y, setY default 0;"
      , "  on clk do { b ? setX(addOne) : setY(addOne) };"
      , "  return ();"
      , "}"
      ]
    cascadeOf sigma "SetterBranch" "clk"
      `shouldBe` branchE (after1r (at "x")) (after1r (at "y"))

  it "EX-SETTER-BRANCH (verbatim): the paper's if-then-else form infers the same effect" $ do
    (sigma, _typedComps) <- inferSource $ Text.unlines
      [ "comp SetterBranchIf(clk: int, b: bool) : unit {"
      , "  state x, setX default 0;"
      , "  state y, setY default 0;"
      , "  on clk do { if b then setX(addOne) else setY(addOne) };"
      , "  return ();"
      , "}"
      ]
    cascadeOf sigma "SetterBranchIf" "clk"
      `shouldBe` branchE (after1r (at "x")) (after1r (at "y"))

  describe "EX-ONCHANGE: text-input onChange (§2)" $ do
    it "inner part: a handler that updates z has effect ○¹ʳ @z" $ do
      -- The application lives in an on clk block (purity: an impure let RHS
      -- like `let fired = handleChange(1);` is a type error).
      (_sigma, typedComps) <- inferSource $ Text.unlines
        [ "comp OnChange(clk: int) : unit {"
        , "  state z, setZ default 0;"
        , "  let handleChange = (e: int) => { setZ(addOne) };"
        , "  on clk do { handleChange(1) };"
        , "  return ();"
        , "}"
        ]
      stmts <- expectJust "on clk block" $ findOnBlock ["clk"] (typedDeclsOf typedComps 0)
      case stmts of
        [s] -> getEffect s `shouldBe` after1r (at "z")
        _ -> expectationFailure "expected a single-statement on-block"

    it "full example: the input listener wraps the handler effect in □change⟨input⟩(○¹ʳ @z)" $ do
      -- Paper source (§2): a text input whose onChange handler updates state
      -- z. Adaptation: the paper's JSX onChange listener is modeled as a bind
      -- inside an `on clk do { … }` block (purity: effects may only live in
      -- on-block bodies, enforced as rejections); the clk
      -- argument exists only to host that block. Bind's own F_e is ·, so the
      -- block effect is exactly the □.
      (sigma, _typedComps) <- inferSource $ Text.unlines
        [ "event change<input> : int;"
        , "comp OnChange(clk: int) : unit {"
        , "  state z, setZ default 0;"
        , "  let handleChange = (e: int) => { setZ(addOne) };"
        , "  on clk do { bind change<input> handleChange };"
        , "  return ();"
        , "}"
        ]
      -- The paper's □change⟨input⟩(○¹ʳ @z), feature for feature: EffAlways =
      -- □, EventLabel "change" ["input"] = change⟨input⟩, and the body ○¹ʳ @z
      -- is the handler's setZ effect from the inner test above.
      cascadeOf sigma "OnChange" "clk"
        `shouldBe` EffAlways (EventLabel "change" ["input"]) (after1r (at "z"))

  it "EX-MOVINGDOT: the §2 main example — click listener guarded by canMove" $ do
    -- Paper source (§2): examples/paper/MovingDot.txt. Adaptations
    -- recorded in the file: the payload IS the coordinate pair (no
    -- e.clientX/e.clientY field access), and the clk arg hosts the
    -- mount-time on-block that wires up the canMove checkbox.
    -- Target effects (paper §2):
    --   bind click⟨#doc⟩ handleClick : □click⟨#doc⟩(○¹ʳ @position)
    --   remove click⟨#doc⟩           : ✗click⟨#doc⟩
    --   on canMove block body        : ✗click⟨#doc⟩ * (□click⟨#doc⟩(○¹ʳ @position) + ·)
    content <- readFileUtf8 "examples/paper/MovingDot.txt"
    (sigma, typedComps) <- inferSource content
    let lbl = EventLabel "click" ["#doc"]
        chk = EventLabel "change" ["#checkCanMove"]
    -- The block-body cascade, feature for feature: the old listener is
    -- removed BEFORE a new one is (maybe) registered; the (+ ·) is the
    -- conditional registration (canMove ? bind … : ()).
    cascadeOf sigma "MovingDot" "canMove"
      `shouldBe` EffSeq
        [ EffRemove lbl
        , EffBranch (EffAlways lbl (after1r (at "position"))) EffNone
        ]
    -- The mount-time block that wires up the checkbox driving canMove: the
    -- same remove-then-bind shape, one level up. Its □ body is ○¹ʳ @canMove,
    -- which is exactly what re-triggers the canMove block asserted above.
    cascadeOf sigma "MovingDot" "clk"
      `shouldBe` EffSeq
        [ EffRemove chk
        , EffAlways chk (after1r (at "canMove"))
        ]
    -- The bind expression's own effect is the paper's first line,
    -- □click⟨#doc⟩(○¹ʳ @position): the let-bound handleClick (body
    -- setPosition(…), effect ○¹ʳ @position) flows through the bind.
    blk <- expectJust "on canMove block" $ findOnBlock ["canMove"] (typedDeclsOf typedComps 0)
    case blk of
      [_removeE, ifE] -> case ifE of
        (_ :< LangFExpr (EIfF _ thenE _)) ->
          getEffect thenE `shouldBe` EffAlways lbl (after1r (at "position"))
        _ -> expectationFailure "expected the canMove ternary as the block's second statement"
      _ -> expectationFailure "expected [remove, ternary] statements in the on canMove block"
    -- §2 (ii): "we see that ✗click⟨#doc⟩ happens before the new event handler
    -- is registered, so we know that stale event handlers are cleaned up."
    -- The §5.4 walk agrees, on both blocks and on both branches of the
    -- conditional registration.
    handlersCleanedUp (fullEffectVar (deltaOf sigma "MovingDot") "canMove")
      `shouldBe` True
    handlersCleanedUp (fullEffectVar (deltaOf sigma "MovingDot") "clk")
      `shouldBe` True

  it "EX-DEBOUNCE: the paper's setTimeout/clearTimeout debounce (§2)" $ do
    -- Paper source (§2):
    --   comp Debounce (value: any) : any {
    --     state slow, setSlow default value;
    --     on value do {
    --       clearTimeout();
    --       setTimeout(λ_. setSlow(λ_. value))
    --     };
    --     return slow;
    --   }
    -- Builtin types: setTimeout f : ◇timeout⟨⟩(F_f) * ○¹⁰⁰ᵐˢ timeout⟨⟩
    --                clearTimeout() : ⊘timeout⟨⟩ * ✗timeout⟨⟩
    -- Target cascade of value:
    --   ⊘timeout⟨⟩ * ✗timeout⟨⟩ * ◇timeout⟨⟩(○¹ʳ @slow) * ○¹⁰⁰ᵐˢ timeout⟨⟩
    -- (The older, counter-based encoding — setTimeout(…) + numSeen/numAged
    -- states — is tested in InferAnnotatedSpec; this is the paper's version.
    -- Same program also lives in examples/paper/Debounce.txt.)
    (sigma, _typedComps) <- inferSource $ Text.unlines
      [ "comp Debounce(value: int) : int {"
      , "  state slow, setSlow default value;"
      , "  on value do {"
      , "    clearTimeout();"
      , "    setTimeout((u: unit) => { setSlow((v: int) => { value }) })"
      , "  };"
      , "  return slow;"
      , "}"
      ]
    let lbl = EventLabel "timeout" []
    cascadeOf sigma "Debounce" "value"
      `shouldBe` EffSeq
        [ EffCancel lbl
        , EffRemove lbl
        , EffEventually lbl (EffAfter (Time 1 Renders) (EffStateChange "slow"))
        , EffAfter (Time 100 Millis) (EffEvent lbl)
        ]

  it "EX-DEBOUNCE-COMPOSE: debounce survives composition (§2)" $ do
    --   comp slowInput = Debounce(input);
    --   on slowInput do { fetch("/api/search?q=" ++ (toString slowInput), …) };
    -- Target: the effect of input carries the prefix ◇timeout⟨⟩(○¹ʳ(○¹ⁿ F)) —
    -- the network call is visibly behind the debounce timer. (Parens around
    -- (toString slowInput): application binds LOOSER than ++ in the impl's
    -- grammar.) fetch's existing schema
    --   forall e. (string * (any -> unit | e)) -> unit | after 1n {e}
    -- already has the shape this example needs; F = · (the pure callback).
    content <- readFileUtf8 "examples/paper/Debounce.txt"
    let search = Text.unlines
          [ "comp Search(input: int) : unit {"
          , "  comp slowInput = Debounce(input);"
          , "  on slowInput do { fetch(\"/api/search?q=\" ++ (toString slowInput), (res: any) => { () }) };"
          , "  return ();"
          , "}"
          ]
    (sigma, _typedComps) <- inferSource (content <> search)
    let lbl = EventLabel "timeout" []
        d = deltaOf sigma "Search"
    -- The fetch itself: ○¹ⁿ F with F := · instantiated for the pure callback.
    cascadeOf sigma "Search" "slowInput"
      `shouldBe` EffAfter (Time 1 NetworkReq) EffNone
    -- Expanding input's full effect crosses the subcomponent boundary:
    -- @slowInput.value (the argument handoff) unfolds into Debounce's body
    -- with slow renamed to slowInput.slow, and slowInput's own cascade
    -- (○¹ⁿ ·) unfolds behind the ○¹ʳ inside the ◇ guard. The result carries
    -- the paper's prefix ◇timeout⟨⟩(○¹ʳ(… ○¹ⁿ · …)) literally — the network
    -- call is visibly behind the debounce timer (a missing debounce would
    -- drop the leading ◇, which Willow's analyses can flag).
    fullEffectVar d "input"
      `shouldBe` EffSeq
        [ at "slowInput.value"
        , EffCancel lbl
        , EffRemove lbl
        , EffEventually lbl
            (after1r (EffSeq [at "slowInput.slow", at "slowInput", EffAfter (Time 1 NetworkReq) EffNone]))
        , EffAfter (Time 100 Millis) (EffEvent lbl)
        ]

  it "EX-MUTUALRECURSION: the x ⇄ y setter loop is detected as loop[x]" $ do
    content <- readFileUtf8 "examples/paper/MutualRecursion.txt"
    (sigma, _typedComps) <- inferSource content
    let d = deltaOf sigma "MutualRecursion"
    -- Paper: changing x has full effect ○¹ʳ(@y * ○¹ʳ loop[x]) (and dually).
    fullEffectVar d "x"
      `shouldBe` after1r (seqE [at "y", after1r (EffLoop "x")])
    fullEffectVar d "y"
      `shouldBe` after1r (seqE [at "x", after1r (EffLoop "y")])
    hasLoopsInEffect (fullEffectVar d "x") `shouldBe` True

  it "EX-FULLEFFECT: graph expansion of §5's Δ gives ○¹ʳ(@z * @y * ○¹ʳ loop[x])" $ do
    -- The paper's given effect environment (§5, §5.4):
    --   x[] ∣ ○¹ʳ @z    y[z] ∣ ·    z[] ∣ ○¹ʳ @x
    let d = Delta (Map.fromList
          [ ("x", DeltaEntry [] (after1r (at "z")))
          , ("y", DeltaEntry ["z"] EffNone)
          , ("z", DeltaEntry [] (after1r (at "x")))
          ])
    fullEffectVar d "x"
      `shouldBe` after1r (seqE [at "z", at "y", after1r (EffLoop "x")])

  it "EX-ASYNCCOMPUTE: asyncCompute's full lifecycle (§5)" $ do
    --   asyncCompute : ∀F1, F2. (int → unit | F1) -> (int → unit | F2) -> unit
    --                |  ○¹ᵘ (comp[suc] + comp[err])
    --                *  ◇comp[suc](F1 * ✗comp[err])
    --                *  ◇comp[err](F2 * ✗comp[suc])
    -- (builtin schema in src/Builtins.hs; the ○¹ᵘ grade uses the Compute
    -- unit, surface "u"). The event decls are for paper fidelity —
    -- Σ_E strictness applies only to bind/once/cancel/remove expressions,
    -- not to builtin schemas. The call lives inside an on-block (purity:
    -- effects may only live in on-block bodies). The ∀F1,F2 instantiation
    -- (F1 := ○¹ʳ @x from cb1, F2 := ○¹ʳ @y from cb2) is the same mechanism
    -- EX-BOTH exercises.
    (sigma, _typedComps) <- inferSource $ Text.unlines
      [ "event comp<suc> : int;"
      , "event comp<err> : int;"
      , "comp AsyncComp(clk: int) : unit {"
      , "  state x, setX default 0;"
      , "  state y, setY default 0;"
      , "  let cb1 = (v: int) => { setX(addOne) };"
      , "  let cb2 = (e2: int) => { setY(addOne) };"
      , "  on clk do { asyncCompute(cb1)(cb2) };"
      , "  return ();"
      , "}"
      ]
    let suc = EventLabel "comp" ["suc"]
        err = EventLabel "comp" ["err"]
    -- The instantiated schema, feature for feature: after one unit u of
    -- compute time either comp[suc] or comp[err] fires (+ is the join); the
    -- success branch runs F1 and removes comp[err] handlers (and dually) —
    -- every event is handled and all handlers are cleaned up.
    cascadeOf sigma "AsyncComp" "clk"
      `shouldBe` EffSeq
        [ EffAfter (Time 1 Compute) (EffBranch (EffEvent suc) (EffEvent err))
        , EffEventually suc (EffSeq [after1r (at "x"), EffRemove err])
        , EffEventually err (EffSeq [after1r (at "y"), EffRemove suc])
        ]
    -- §5.4 revisits this example for the "event handlers cleaned up" walk:
    -- "we see, just with Willow's type-and-effect system, that no event
    -- handlers are left after the function executes." Each ◇ registration is
    -- matched by the ✗ inside the OTHER branch's modality body, which is why
    -- the walk has to look inside □/◇ bodies.
    handlersCleanedUp (fullEffectVar (deltaOf sigma "AsyncComp") "clk")
      `shouldBe` True

  it "EX-BOTH: both : ∀F. (int → unit | F) → (int × int) → unit | F * F (effect polymorphism)" $ do
    (sigma, _typedComps) <- inferSource $ Text.unlines
      [ "comp BothTest(clk: int) : unit {"
      , "  state x, setX default 0;"
      , "  let both : forall e. (int -> unit | e) -> (int * int) -> unit | e * e ="
      , "    (f: (int -> unit | e)) => { (p: (int * int)) => { f(p.0) ;; f(p.1) } };"
      , "  on clk do { both((v: int) => { setX((c: int) => { c + v }) })(1, 2) };"
      , "  return ();"
      , "}"
      ]
    -- NOTE: the paper's effect is `F * F` — the parameter is applied twice.
    -- With F := ○¹ʳ @x (a state change) collapsing to a single ○¹ʳ @x is
    -- CORRECT per the paper's algebra (owner ruling: state changes are
    -- idempotent, @x * @x = @x). The impl achieves it via 'mkEffSeq', which
    -- dedups only effects whose entire tree is idempotent — event effects and
    -- effect variables are kept (see ALGEBRA-IDEMPOTENCE in PaperRulesSpec).
    cascadeOf sigma "BothTest" "clk" `shouldBe` seqE [after1r (at "x")]

  it "EX-TEXTINPUT: the onChange effect propagates through subcomponent instantiation (§5.3)" $ do
    content <- readFileUtf8 "examples/paper/TextInput.txt"
    let signup = Text.unlines
          [ "comp Signup() : html {"
          , "  state saved, setSaved default \"\";"
          , "  comp ti = TextInput(\"\", (s: string) => { setSaved((old: string) => { s }) }, (s: string) => { true }, 0);"
          , "  return <div></div>;"
          , "}"
          ]
    (sigma, _typedComps) <- inferSource (content <> signup)
    -- Inside TextInput the cascade of `text` is the abstract (?F + ·):
    cascadeOf sigma "TextInput" "text"
      `shouldBe` branchE (EffVar (EffVarName "F")) EffNone
    -- The input's own listener is bound in the mount-time clk block:
    -- ✗change⟨#input⟩ * □change⟨#input⟩(○¹ʳ @text). That ○¹ʳ @text is what
    -- feeds the `text` cascade above.
    let inputLbl = EventLabel "change" ["#input"]
    cascadeOf sigma "TextInput" "clk"
      `shouldBe` EffSeq
        [ EffRemove inputLbl
        , EffAlways inputLbl (after1r (at "text"))
        ]
    -- Instantiated with onChange := λs. setSaved(λ_. s), it becomes (○¹ʳ @saved + ·):
    cascadeOf sigma "Signup" "ti.text"
      `shouldBe` branchE (after1r (at "saved")) EffNone

  describe "EX-USERNAMEINPUT: the §7 signup-form case study" $ do
    -- Paper source (§7): examples/paper/UsernameInput.txt — UsernameInput
    -- with the Debounce subcomponent and the
    -- asyncCompute-shaped fetchUsernameCheck builtin (events req⟨check,suc⟩ /
    -- req⟨check,err⟩). Adaptations recorded in the file: availableNames is a
    -- string not a Set (has / ++ stand in); the JSX onChange listener is a
    -- bind inside an `on clk do { … }` block (the only effectful context);
    -- e.target.value is the event payload itself; the ternary condition is
    -- parenthesized because application binds looser than `? :`.
    -- §7's db⟨⟩ is a figure-local renaming of timeout⟨⟩, the label the
    -- setTimeout builtin uses.
    it "clk cascade: ✗change⟨#name⟩ * □change⟨#name⟩(○¹ʳ @username)" $ do
      (sigma, _tc) <- inferUsernameInput
      -- The mount-time block removes any stale listener before binding the
      -- new one (same remove-then-bind discipline as MovingDot's canMove
      -- block); the □ body is the paper's ○¹ʳ @username.
      let nameLbl = EventLabel "change" ["#name"]
      cascadeOf sigma "UsernameInput" "clk"
        `shouldBe` EffSeq
          [ EffRemove nameLbl
          , EffAlways nameLbl (after1r (at "username"))
          ]

    it "username cascade: the debounce shape across the subcomponent boundary" $ do
      (sigma, _tc) <- inferUsernameInput
      -- The paper's chain @username → ⊘db⟨⟩ * ✗db⟨⟩ * ◇db⟨⟩(○¹ʳ @slow-ish) *
      -- ○¹⁰⁰ᵐˢ db⟨⟩ splits at the subcomponent boundary: username's cascade
      -- is just the argument handoff @slowUsername.value …
      cascadeOf sigma "UsernameInput" "username"
        `shouldBe` at "slowUsername.value"
      -- … and slowUsername.value carries the debounce body itself, with slow
      -- renamed to slowUsername.slow inside the ◇ guard.
      let lbl = EventLabel "timeout" []
      cascadeOf sigma "UsernameInput" "slowUsername.value"
        `shouldBe` EffSeq
          [ EffCancel lbl
          , EffRemove lbl
          , EffEventually lbl (after1r (at "slowUsername.slow"))
          , EffAfter (Time 100 Millis) (EffEvent lbl)
          ]

    it "slowUsername cascade: the branchy network lifecycle, with paper bug 1 visible" $ do
      (sigma, _tc) <- inferUsernameInput
      let reqSuc = EventLabel "req" ["check", "suc"]
          reqErr = EventLabel "req" ["check", "err"]
          -- PAPER BUG 1 (stuck loading), visible literally: the success
          -- handler's body is (○¹ʳ @availableNames + ·) * ✗req⟨check,err⟩ —
          -- it updates availableNames (the + · is the paper's
          -- `if isAvailable then … else ()`) and removes the err listeners,
          -- but @status is never reset, so the spinner would spin forever.
          sucBody = EffSeq [EffBranch (after1r (at "availableNames")) EffNone, EffRemove reqErr]
      -- The paper's then/else split (§7 lines 11-15): cached → ○¹ʳ @status
      -- ("idle"); miss → ○¹ʳ @status ("checking") sequenced by the ;; builtin
      -- (both sides unit) with the fetchUsernameCheck lifecycle
      -- ○¹ⁿ(reqs) * ◇suc(sucBody) * ◇err(○¹ʳ @status * ✗suc).
      cascadeOf sigma "UsernameInput" "slowUsername"
        `shouldBe` EffBranch
          (after1r (at "status"))
          (EffSeq
            [ after1r (at "status")
            , EffAfter (Time 1 NetworkReq) (EffBranch (EffEvent reqSuc) (EffEvent reqErr))
            , EffEventually reqSuc sucBody
            , EffEventually reqErr (EffSeq [after1r (at "status"), EffRemove reqSuc])
            ])

    it "bug 1 fix: only UsernameInputFixed resets @status on the success path" $ do
      (sigma, _tc) <- inferUsernameInput
      let reqSuc = EventLabel "req" ["check", "suc"]
          reqErr = EventLabel "req" ["check", "err"]
      -- UsernameInputFixed applies BOTH of §7's fixes, and each one is
      -- readable off this cascade:
      --   bug 1 (stuck loading, p.22): the ◇suc body now leads with ○¹ʳ
      --     @status (setStatus "idle") before the conditional ○¹ʳ
      --     @availableNames, so the spinner is cleared on success.
      --   bug 2 (request race, p.22): the then-branch is · rather than the
      --     buggy version's ○¹ʳ @status, because the guarded on-block bails
      --     with () when a request is already in flight.
      cascadeOf sigma "UsernameInputFixed" "slowUsername"
        `shouldBe` EffBranch
          EffNone
          (EffSeq
            [ after1r (at "status")
            , EffAfter (Time 1 NetworkReq) (EffBranch (EffEvent reqSuc) (EffEvent reqErr))
            , EffEventually reqSuc (EffSeq
                [ EffSeq
                    [ after1r (at "status")
                    , EffBranch (after1r (at "availableNames")) EffNone
                    ]
                , EffRemove reqErr
                ])
            , EffEventually reqErr (EffSeq [after1r (at "status"), EffRemove reqSuc])
            ])

    it "loop detection: the buggy program is loop-free; the fixed program flags loop[status]" $ do
      (sigma, _tc) <- inferUsernameInput
      let dBuggy = deltaOf sigma "UsernameInput"
          dFixed = deltaOf sigma "UsernameInputFixed"
      -- Buggy (`on slowUsername do …`, the paper's §7 listing): nothing
      -- watches status, so its full effect is · — no loop arises, and the
      -- request race of bug 2 is exactly what that missing edge encodes.
      fullEffectVar dBuggy "status" `shouldBe` EffNone
      hasLoopsInEffect (fullEffectVar dBuggy "status") `shouldBe` False
      -- Fixed (`on slowUsername, status do …`, the bug-2 fix): status is now
      -- watched, so the effect graph's expansion of status revisits status
      -- and loop detection fires. This is the paper's p.23 graph — an
      -- intentional error-retry cycle (◇err ⇒ ○¹ʳ @status "error" ⇒ the block
      -- runs again) that Willow surfaces for a human to judge rather than
      -- auto-rejecting.
      hasLoopsInEffect (fullEffectVar dFixed "status") `shouldBe` True
      -- p.23 puts loop[status] on BOTH the suc and the err path. That second
      -- cycle exists only once bug 1 is also fixed — it is the suc handler's
      -- own ○¹ʳ @status that closes it — and UsernameInputFixed applies both
      -- fixes, so we reproduce the figure edge for edge.
      case fullEffectVar dFixed "status" of
        EffBranch EffNone (EffSeq effs) -> do
          let loopsUnder lbl =
                or [hasLoopsInEffect body | EffEventually l body <- effs, l == lbl]
          loopsUnder (EventLabel "req" ["check", "suc"]) `shouldBe` True
          loopsUnder (EventLabel "req" ["check", "err"]) `shouldBe` True
        other ->
          expectationFailure $ "unexpected shape for the fixed status expansion: " <> show other
