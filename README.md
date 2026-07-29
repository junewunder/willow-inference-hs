# Willow

**Willow** is a type-and-effect checker for a small React-like language. You write a
program describing React components — state, effect blocks (`on … do`), `let`s, JSX,
and sub-components — and Willow infers, for every component, not just its *type* but
its **timing behavior**: which state changes happen, how long each takes (measured in
renders, network requests, milliseconds, or debounce windows), which handlers are bound
to which events, and whether any of it cascades into an inter-render **loop**.

The goal is to catch **React timing bugs** — extra renders, effects that fire in
cascades, stuck-loading states, request races, debounce misuse, leaked listeners — at
type-check time.

This repository is the artifact accompanying the paper *A Type-and-Effect System for
Temporal Dependency Analysis of Render-based Reactive Programs*, by June Wunder, Ankush
Das, and Marco Gaboardi (Boston University). The paper is included as
[`willow-preprint.pdf`](willow-preprint.pdf); it gives the semantics, the typing rules,
and the metatheory that this implementation is meant to match, with the appendix
(collected grammars, the full rule set, and the proofs) from §A onward. The rest of this
README
summarizes the paper for readers who haven't read it, then explains how to run the
checker.

## The problem: reactive programs hide their timing

Modern interactive software is increasingly structured as **reactive programs** that
continuously respond to streams of events originating from users, sensors, and network
services. Frameworks such as React have popularized a declarative model for building
such systems, in which programs describe how outputs depend on changing inputs rather
than explicitly orchestrating control flow.

Although this model makes it easy to reason about *what* an application computes, the
**temporal** behavior of reactive programs — when updates occur and how they propagate —
remains difficult to understand and verify. Reactive applications implicitly encode
timing assumptions about when updates occur, how quickly state propagates, and how
computations interact with asynchronous events. Those dependencies can be intentionally
or accidentally *mutually recursive*: an update to `x` leads to an update to `y` which,
in turn, leads to an update to `x`. State changes are often conditional on other pieces
of program state. And because the timing rules live in the framework's runtime rather
than in the program, timing reasoning is left to informal means.

The result is a family of bugs that ordinary type systems say nothing about:
computations may observe **stale state** if updates have not yet propagated; **transient
inconsistencies** (glitches) appear when dependent values are updated at different
times; **order-dependence** makes an outcome depend on the scheduler's choice of
evaluation order; and deferred execution or batching produces effects later than the
program assumed. Graphical user interfaces have long been recognized as hard to test,
owing to the combinatorial space of possible event sequences and orderings.

A second source of complexity is the **lifecycle of event handlers**. Handlers must be
repeatedly torn down and re-bound as program state changes, and deciding which state
changes invalidate which handler is left entirely to the programmer. Programmers can and
do forget to remove old handlers, which gives rise to logic bugs and memory leaks.

Willow is the static analysis this motivates: a simplified core calculus inspired by
React, together with a type-and-effect system that makes the temporal behavior of a
reactive program part of its type.

## How Willow models time

At its core Willow models time using **renders** — the moment when a component is
evaluated to produce a description of the user interface. A render is triggered whenever
one of the state variables changes, and Willow treats renders as the fundamental
computation step. State is immutable *during* a render: setter calls are queued and
flushed between renders, so a value written now is visible only on the next render.

The key idea of the type system is to **integrate state and event dependencies with
quantitative delay information**. For a state variable `x`, the base effect `@x`
indicates that `x` may change, and `after 1r {@x}` (the paper's `○¹ʳ@x`) indicates that
`x` may have a different value in exactly the next render. Effects compose with `*` for
sequence (`F₁ * F₂`: both happen, in order) and `+` for branching (`F₁ + F₂`: either may
happen), and they propagate through expressions the way traditional effect systems
propagate effects — so the timing of a larger component is inferred from the timing of
its parts.

### An example: a dot that follows your clicks

The paper's running example is a component that moves a dot to wherever you click, with
a checkbox controlling whether movement is enabled. In React it looks like this:

```jsx
export default function MovingDot() {
  const [position, setPosition] = useState({ x: 0, y: 0 });
  const [canMove, setCanMove] = useState(true);
  let handleClick = (e) => { setPosition(_ => ({ x: e.clientX, y: e.clientY })); };
  useEffect(() => {
    if (canMove) { document.addEventListener("click", handleClick); }
    return () => document.removeEventListener("click", handleClick);
  }, [canMove]);
  return ( /* a checkbox bound to setCanMove, and the positioned dot */ );
}
```

Its correctness relies on several temporal assumptions that appear nowhere in the types:

1. When the user clicks, the registered listener calls `setPosition`, but `position`
   only updates on the *next* render, not during the event.
2. When `canMove` flips, the effect block runs its cleanup function to remove the old
   listener first; only after that does the body decide whether to attach a new one.
   Forgetting the cleanup would be both a program logic mismatch and a memory leak.
3. The points in time at which a click can move the dot are not determined by the code
   itself; they are determined by when the effect block last ran and what `canMove`'s
   value was at that point.

This kind of effect-block programming is a common idiom in modern React and,
unfortunately, also a common source of bugs. To use it correctly a programmer must track
which renders re-run the effect, which of those runs trigger the cleanup, and in what
order the resulting side effects occur relative to one another and to the surrounding
renders — which is infeasible in a large application.

Willow encodes those assumptions in the type system, so they can be known at compile
time. The same component in Willow — abridged here from
[`examples/paper/MovingDot.txt`](examples/paper/MovingDot.txt), which additionally
declares the event labels it uses and wires up the checkbox:

```
comp MovingDot (clk: int) : html {
  state position, setPosition default (0, 0);
  state canMove, setCanMove default true;
  let handleClick = (e: (int * int)) => { setPosition((p: (int * int)) => { e }) };
  on canMove do {
    remove click<#doc>;
    canMove ? bind click<#doc> handleClick : ()
  };
  return ( /* same html as in React */ );
}
```

React's `useEffect` block becomes an **on-block**, `on canMove do { … }`, which fires
whenever its watched variable changes. An on-block executes cleanup at the beginning, so
`remove` is called first and only then does the rest of the body run. The argument
`click<#doc>` is an **event label**: a tagged identifier for a class of external events,
where `click` names the kind of event and `#doc` identifies *which* element of that kind
it comes from.

The effects Willow infers for this component are exactly the assumptions listed above:

```
  bind click<#doc> handleClick : always click<#doc> {after 1r {@position}}
  remove click<#doc>           : remove click<#doc>
  on canMove block body        : remove click<#doc>
                                   * (always click<#doc> {after 1r {@position}} + none)
```

Reading them back: the click listener modifies `position` on the next render
(`after 1r {@position}`); when `canMove` changes, `remove click<#doc>` happens *before*
the new handler is registered, so stale handlers are provably cleaned up; and the
registration is wrapped in a `+ none`, which says the handler is only *sometimes*
registered — it is conditional.

### Two layers: renders and events

The constructs above describe **synchronous** state changes: setter calls queued during
a render and flushed deterministically before the next one begins, requiring no external
trigger. **Asynchronous** events — a DOM click, a timer expiry, a network response — may
arrive at any point in time, interleaved between renders, or not at all. Their occurrence
is contingent on the outside world, not on the program's own execution.

So the effect language provides a second layer of modalities, indexed by **event labels**
rather than by render counts. A family of them tracks the full lifecycle of an event
handler — when handlers are registered, when they fire, when pending events are
cancelled, and when handlers are removed:

- `always ℓ⟨v⟩ {F}` (the paper's `□ℓ⟨v⟩(F)`) registers `F` as a **persistent** handler:
  every time the event fires, `F` happens.
- `eventually ℓ⟨v⟩ {F}` (`◇ℓ⟨v⟩(F)`) registers a **one-shot** handler: when the event
  fires the callback runs once and the registration is consumed.
- `cancel ℓ⟨v⟩` (`⊘ℓ⟨v⟩`) suppresses one pending firing; `remove ℓ⟨v⟩` (`✗ℓ⟨v⟩`)
  unregisters every listener attached to the event.

The two layers meet at effects of the form `always ℓ⟨v⟩ {after 1r {@x}}` — contingent on
an external event `ℓ⟨v⟩` firing, `x` may change in the render that follows. And the
delay modality is indexed not only by renders but by any declared **time unit** —
renders, milliseconds, network round-trips — so the system can describe asynchronous
schedules alongside synchronous render counts. A debounce, for instance
([`examples/paper/Debounce.txt`](examples/paper/Debounce.txt)), infers as

```
  on value:
        cancel timeout<>
      * remove timeout<>
      * eventually timeout<> {after 1r {@slow}}
      * after 100ms {timeout<>}
```

which reads: when `value` changes, (1) any pending `timeout<>` is cancelled and its
handlers unregistered, (2) a fresh `timeout<>` is scheduled to fire after 100ms, and
(3) contingent on it firing, `slow` may change in the next render.

The payoff is that such protection **survives composition**. If a parent watches the
debounced `slow` value and issues a network request from it, the request's effect carries
the `eventually timeout<>` prefix — so a parent or library author can see in the type
that the downstream `fetch` is protected by a debounce. Were the debounce missing, the
type would be missing that prefix, and Willow's analyses could warn.

### Temporal dependency graphs

React's `useEffect` is intentionally an "escape hatch" from the declarative paradigm: it
carves out a section of the program where predictability no longer holds. Willow's key
insight is that the effects it infers form a **temporal dependency graph** — nodes are
potential state changes, edges are the delays between them — and that this graph captures
variable dependency over the entire execution, not just a single render. By recursively
expanding effects over the graph, Willow computes the **full effect** of any event, and
standard graph algorithms then do the analysis. The paper uses them to:

1. detect long **render cascades**, where one event drives many sequential renders and
   degrades performance;
2. flag **inter-render loops**, where updates repeatedly trigger one another;
3. warn when expensive handlers are bound to **high-frequency events**;
4. confirm that stale event handlers are always **cleaned up**; and
5. analyze the timing of an app's **first render**.

The simplest looping example is a pair of blocks that write to each other's variable
([`examples/paper/MutualRecursion.txt`](examples/paper/MutualRecursion.txt)): changing
`x` sets `y` one render later, and `y`'s block sets `x` one render after that, so the
full effect of modifying `x` is an infinite chain. Willow cuts the cycle with `loop[x]`
and reports it at compile time.

Analyses (4) and (5) ship in this checker as the [`--cleanup`](#--cleanup-checking-that-event-handlers-are-removed)
and [`--first`](#--first-what-a-component-does-when-it-mounts) flags, described below;
loop detection (2) is part of the ordinary output, since `loop[x]` appears in the
inferred effect itself.

## What the paper contributes

| Contribution | Paper |
|---|---|
| A core calculus for reactive programming, with a time-aware operational semantics making explicit the temporal and causal structure of updates | §4 |
| A type-and-effect system tracking timing constraints, enabling static reasoning about when computations produce observable effects | §5 |
| Metatheory establishing preservation of the effect system with respect to an instrumented semantics — well-typed programs respect the timing guarantees described by their effects | §6 |
| Post-typecheck analyses that statically catch common bugs and tell programmers what to inspect | §5.4 |
| A prototype type-and-effect **inference** algorithm — this repository — demonstrating feasibility for real React programs | §7 |
| Type-checking of real-world examples: a stuck loading state, a request race, and an update loop in a realistic signup form | §7 |

The last two rows are what you can run here. Everything below is about doing that.

## Build

Willow is a Haskell project built with [Stack](https://docs.haskellstack.org/). The
snapshot pins GHC 9.10.3 and every dependency version, so the first build downloads a
toolchain (a few minutes, network required); later builds are incremental and no
further network access is needed.

```sh
stack build
```

## Run

Analyze a program by passing it as an argument:

```sh
stack exec -- willow-hs-exe examples/paper/MovingDot.txt
```

With no argument, the executable prints usage and lists the worked examples from the
paper:

```sh
stack exec -- willow-hs-exe
```

Willow exits `0` when the program type-checks and `1` on a parse, type, or effect
error. Results go to stdout and progress chatter to stderr, so
`… MovingDot.txt 2>/dev/null` gives just the inferred effects; on an error, everything
goes to stderr and stdout stays empty.

### Reading the output

A successful run prints two sections. The first is the **component summary** — the
environment Σ that inference produces, one row per bound variable, giving that
variable's *immediate* effect:

```
--- Component Summary (Sigma) ---
comp MovingDot
  canMove |
      remove click<#doc> * (always click<#doc> {after 1r {@position}} + none)
  clk |
        remove change<#checkCanMove>
      * always change<#checkCanMove> {after 1r {@canMove}}
  handleClick [setPosition] | none
  position | none
  returnVar [canMove, position] | none
```

The `canMove` row reads: when `canMove` changes, Willow removes the old document
`click` handler and — if `canMove` is true — binds a handler that, one render later
(`after 1r`), sets `@position`. The `clk` row is the mount-time block that wires up the
checkbox driving `canMove`, in the same remove-then-bind shape. A row's square
brackets, where present, list the variables it depends on.

The second section gives the **full effect** of each variable an `on` block watches:
the same effects, but with every state change followed through the temporal dependency
graph, so one row shows the whole cascade a change sets off rather than just its first
step.

```
--- Effects for MovingDot ---
  on canMove:
        remove click<#doc>
      * (always click<#doc> {after 1r {@position * @returnVar}} + none)

  on clk:
        remove change<#checkCanMove>
      * always change<#checkCanMove> {
          after 1r {
              @canMove
            * @returnVar
            * remove click<#doc>
            * (always click<#doc> {after 1r {@position * @returnVar}} + none)
          }
        }
```

In the `clk` row the checkbox handler's `@canMove` has been expanded into what changing
`canMove` in turn causes — rebinding the click handler — which the summary listed as a
separate row. This is where cascades and `loop[x]` become visible, and it is the
section that gets large: expanding a cycle through a realistic component can run to
hundreds of lines (`examples/paper/UsernameInput.txt` is the extreme case, ~900).

Effects are printed as a tree: a cascade stays on one line while it fits, and otherwise
breaks one operand per line with the `*`/`+` operator in a gutter on the left and
modality bodies as indented blocks. Whichever way it breaks, the printed effect is in
the same concrete syntax Willow parses, so it can be pasted back into a program.

### Flags

| Flag | Effect |
|------|--------|
| `-v` / `--verbose` | verbose logging; dumps the parsed AST |
| `--first` | additionally show the initial-render (mount) analysis |
| `--cleanup` | additionally check that every event handler is removed again |

The two analyses are the paper's post-typecheck analyses (§5.4). Both are additive:
they append a section after the normal output rather than replacing it, and they can be
combined in one run.

### `--first`: what a component does when it mounts

Every `on … do { … }` block runs once when the component mounts, so the mount effect is
all of them together. The event-layer modalities split what that means into three
parts, and `--first` reports them separately:

- what **settles** — the state changes and the delays between them. The component keeps
  re-rendering until these are exhausted, so this is what decides how long mounting
  takes.
- what is **armed** — `always ℓ⟨v⟩` and `eventually ℓ⟨v⟩` register a body without
  running it. Those bodies are excluded from the settling part precisely because they
  are waiting for `ℓ⟨v⟩` to fire.
- what is **scheduled** — an event the mount effect itself promises to fire, like the
  `after 100ms {timeout<>}` a `setTimeout` produces. An armed body will run when it
  arrives, with no user interaction, so mount is not really over when the settling part
  finishes.

```sh
stack exec -- willow-hs-exe --first examples/paper/Debounce.txt
```

```
=== Initial Render Analysis ===
comp Debounce
  settles: nothing (no state changes on mount)
  arms:
    eventually timeout<> — body waits for the event
  schedules:
    timeout<> after 100ms — fires with no user interaction
```

A `loop[x]` in the settling part is an inter-render loop entered on the very first
render, so the component never finishes mounting:

```sh
stack exec -- willow-hs-exe --first examples/paper/MutualRecursion.txt
```

```
=== Initial Render Analysis ===
comp MutualRecursion
  settles:
        after 1r {@y * after 1r {@x * after 1r {loop[y]}}}
      * after 1r {@x * after 1r {@y * after 1r {loop[x]}}}
  ⚠️  never settles — loops through y, x
```

The warning distinguishes a loop every path reaches (`never settles`, as here) from one
some branch escapes (`may not settle`) — `UsernameInputFixed` in
[`examples/paper/UsernameInput.txt`](examples/paper/UsernameInput.txt) is the latter,
where the guarded retry cycle is deliberate.

### `--cleanup`: checking that event handlers are removed

A listener that is registered and never removed is both a logic bug and a memory leak —
the React `useEffect` whose cleanup function forgets `removeEventListener`, or the
`setTimeout` with no `clearTimeout`. `--cleanup` walks each variable's full effect and
checks that every registration (`always ℓ⟨v⟩` / `eventually ℓ⟨v⟩`) is matched by a
`remove ℓ⟨v⟩`, taking the two branches of `+` separately and looking inside modality
bodies:

```sh
stack exec -- willow-hs-exe --cleanup examples/StaleListener.txt
```

```
=== Event Handler Cleanup Analysis ===
comp StaleListener
  on clk:
    ⚠️  always click<#doc> — no matching remove click<#doc> (handler left behind)
    ⚠️  eventually timeout<> — no matching remove timeout<> (handler left behind)
comp StaleListenerFixed
  on clk:
    ✓ always click<#doc> — cleaned up
    ✓ eventually timeout<> — cleaned up
```

Note that `cancel ℓ⟨v⟩` does not discharge a registration: cancelling suppresses one
pending firing of the event, while `remove` is what unregisters the handlers. All five
examples in `examples/paper/` come out clean under this check.

### When a program doesn't check

Type and effect errors are reported with the source span and a caret, and the run exits
`1`. Given a setter for an `int` state handed a `string`-returning updater, Willow
reports:

```
====================
 Type/Effect Error
====================
Type mismatch:
  Expected int
  Actual   string
Location: Bad.txt:3:15-23
  1: comp Bad (clk: int) : int {
  2:   state count, setCount default 0;
> 3:   on clk do { setCount((s: string) => { "oops" }) };
                    ^^^^^^^
  4:   return count;
  5: }

Context:
  setCount (s: string => "oops")
```

Leaving a handler behind is a *lint*, not a type error — `--cleanup` warns, but the
program still type-checks and still exits `0`. The same is true of `loop[x]`: Willow
reports cycles for a human to judge rather than rejecting them, since some retry loops
are intentional.

## What to expect

Every example in this repository type-checks, and the paper examples' inferred effects
are what the paper prints. Each example file ends with a comment block recording the
paper section it comes from, the adaptations made to fit Willow's concrete syntax
(Willow has no field access and no effectful JSX attributes, so handlers take the event
payload directly and listeners are bound in a mount-time block), and the cascades it
should infer — including the paper's glyph notation alongside Willow's ASCII.

| Example | Paper | Demonstrates |
|---------|-------|--------------|
| [`paper/MovingDot.txt`](examples/paper/MovingDot.txt) | §2 | the running example: remove-then-bind handler lifecycle, and a state change that only happens on one branch |
| [`paper/Debounce.txt`](examples/paper/Debounce.txt) | §2 | scheduled events and millisecond delays — `cancel`/`remove`/`eventually` on a timer |
| [`paper/MutualRecursion.txt`](examples/paper/MutualRecursion.txt) | §2 | the inter-render loop Willow is built to find; the one example that never settles on mount (`--first`) |
| [`paper/TextInput.txt`](examples/paper/TextInput.txt) | §5.3 | effect polymorphism: a component quantified over its caller's latent effect, `?F` surviving inference |
| [`paper/UsernameInput.txt`](examples/paper/UsernameInput.txt) | §7 | the signup-form case study — the stuck-loading bug, the request race, and the intentional retry loop the fix exposes; buggy and fixed components side by side |
| [`StaleListener.txt`](examples/StaleListener.txt) | §5.4 | negative example for `--cleanup`: a component leaking two handlers, next to the same component written correctly |

### Reproducing the paper's claims

The inferred effects are pinned by the test suite, so the examples above are checked
rather than merely documented. Two suites are of particular interest for artifact
evaluation:

- **`PaperRulesSpec`** — one test per typing rule from the paper, named by the rule ID
  the paper uses (`T-STATE-DECL`, `T-APP`, `SE-DELAY`, …).
- **`PaperExamplesSpec`** — the paper's worked examples, checked end-to-end against the
  effects the paper reports.

The rest of the suite covers the parser, inference, the two analyses, and a round trip
that pins every effect printer against the parser. Run everything:

```sh
stack test
```

Expect **191 examples, 0 failures**, in well under a second. The suite is the evidence
for the paper's claims — a failure means the implementation or the paper is wrong, not
that a test needs relaxing.

## Repository layout

| Path | Contents |
|------|----------|
| `src/` | the checker — parser (`Parse.hs`), type-and-effect inference (`InferTyEffect.hs`), the type/effect language and pretty-printer (`Types.hs`), analyses (`Analysis/`), orchestration (`Run.hs`) |
| `app/Main.hs` | the CLI |
| `test/` | hspec suites, including the paper-conformance suites |
| `examples/` | Willow programs, each with a comment block tying it to the paper |
| `willow-preprint.pdf` | the paper, with its appendix |

## The type-and-effect language, briefly

Every expression has a type **and** an effect. Effects describe what happens over time.
Willow prints ASCII; the paper uses glyphs.

| Willow | Paper | Meaning |
|--------|-------|---------|
| `@x` | `@x` | a change to state variable `x` |
| `after Nu {F}` | `○ᴺᵤ F` | `F`, delayed by `N` units of time `u` |
| `F₁ * F₂` | `F₁ * F₂` | sequencing |
| `F₁ + F₂` | `F₁ + F₂` | branching |
| `none` | `·` | no effect |
| `always ℓ⟨v⟩ {F}` | `□ℓ⟨v⟩(F)` | register `F` as a persistent handler for the event |
| `eventually ℓ⟨v⟩ {F}` | `◇ℓ⟨v⟩(F)` | register `F` as a one-time handler |
| `cancel ℓ⟨v⟩` | `⊘ℓ⟨v⟩` | suppress one pending firing of the event |
| `remove ℓ⟨v⟩` | `✗ℓ⟨v⟩` | unregister the event's handlers |
| `loop[x]` | `loop[x]` | an inter-render loop through `x` |
| `?e` | `F` | an effect variable inference did not pin down |

Time units are `r` renders, `n` network requests, `ms` milliseconds, `db` a debounce
window, `i` intervals, `u` compute units.

Two notational cautions. `*` binds **looser** than `+` — the opposite of arithmetic — so
Willow always brackets a mixed grouping rather than leaving it to the reader. And the
bracket in `always click<#doc> {…}` delimits the handler *body*, not a delay; delays are
the `{…}` after `after Nu`.

Inference is Hindley–Milner-style, extended so that library functions (`fetch`,
`setTimeout`, `setInterval`, …) are polymorphic in their latent effect — which is what
lets `TextInput` above be typed once and instantiated per caller. The paper gives the
grammar (Fig. 5) and the full set of typing rules (Figs. 6–7, and Figs. 10–15 in the
appendix).

## License

MIT — see [`LICENSE`](LICENSE).
</content>
