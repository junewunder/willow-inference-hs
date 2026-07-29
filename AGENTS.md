# Willow — agent guide

Willow is a type-and-effect checker for a small React-like language: it infers, per
component, both a type and a **timing effect** (which state changes happen, how long
they take, whether they cascade into an inter-render loop). Haskell, built with Stack.

**This repo is the public artifact accompanying the Willow paper.** That shapes every
decision here — see [Public-artifact rules](#public-artifact-rules) below. Read
[`README.md`](README.md) first for the user-facing story, and `willow-preprint.pdf` for
the formalism the implementation is meant to match — main text through §7, then the
appendix (collected grammars, full rule set, proofs) from §A onward.

## Build, run, test

```sh
stack build
stack test
stack exec -- willow-hs-exe examples/paper/MovingDot.txt
stack exec -- willow-hs-exe            # usage + lists the paper examples
```

Flags: `-v/--verbose` (dumps the parsed AST), `--first` (initial-render analysis),
`--cleanup` (stale-listener check).

After any change to the language: `stack build`, then `stack test`, then run a
relevant `examples/*.txt` through the exe and eyeball the printed effect. The tests
pin exact effect strings, so "it compiles" is not evidence the semantics are right.

## Layout

| Path | Contents |
|------|----------|
| `src/Types.hs` | **All** data types (`ExprF`/`JSXNodeF`/`JSXChildF`, `Type`, `Effect`, `Delay`, `Unit`, `Delta`, `Sigma`), the `Pretty` instances, the manual `Show/Eq/Ord` for `AnnotatedNode`, `mk*` smart constructors, `Options` |
| `src/Parse.hs` | Megaparsec parser → `AnnotatedProgram` with dummy type/effect annotations |
| `src/InferTyEffect.hs` | Type + effect inference: `unifyType`/`unifyEffect`, `substType`/`substEffect`, `instantiateSchema`, `generalizeEffect`, `freeVars` |
| `src/InferenceMonad.hs` | `InferenceM` = `ExceptT InferenceError (ReaderT InferenceContext (RIO RIOApp))`; fresh effect vars from `appVarCounter` |
| `src/Builtins.hs` | Built-in function schemas, written as **strings** and parsed by `Parse.pType` at load |
| `src/Analysis/` | `Common` (`fullEffect`, `simplifyEffect`, `relevantEffect`), `EffectReadability` (`effectSummary`), `InitialRender` (`--first`), `HandlerCleanup` (`--cleanup`) |
| `src/ErrorDisplay.hs` | Type/effect errors with source span + caret |
| `src/Run.hs`, `app/Main.hs` | Orchestration (read → parse → infer → display/analyze) and the CLI |
| `src/Import.hs` | Re-exports `RIO` + `Types` + `Util`; most modules just `import Import` |
| `test/` | hspec; `Spec.hs` is the discovery driver |
| `examples/paper/` | the paper's worked examples |

Everything runs in `RIO RIOApp`. `RIOApp` carries the log func, process context, CLI
`Options`, and `appVarCounter :: IORef Int` (source of fresh effect variables).

## Things that will bite you

- **`willow-hs.cabal` is generated from `package.yaml` by hpack. Edit
  `package.yaml`.** Cabal-file edits get silently overwritten on the next build.
- **The pretty printers live inside `Types.hs`**, not a separate module. "Update the
  printer" means a second pass over `Types.hs`.
- **There are two effect printers, and both must stay in step.** `prettyEffect` (the
  `Pretty Effect` instance) is the canonical one-line form; `prettyEffectReadable` /
  `renderEffect` is the line-breaking form used wherever a whole cascade is displayed.
  They share notation and parenthesization and differ only in layout — a change to one
  is almost always a change to both. Both print the concrete syntax `Parse.pEffect`
  accepts; `test/EffectPrettySpec.hs` pins that round trip, so a printer change that
  breaks it fails the suite rather than silently emitting unparseable output.
- **`*` binds looser than `+`** in the effect grammar (`pEffect` is a `*`-separated
  list of `+`-chains) — the opposite of arithmetic. The printers deliberately bracket
  every mixed grouping instead of relying on the reader knowing that; don't "simplify"
  those brackets away.
- **`prettyExprF` has no catch-all.** A missing case is a *runtime* crash
  ("Non-exhaustive patterns"), not a warning.
- **Adding a constructor temporarily breaks everything, and that is expected.** The
  core sum types are `case`-matched exhaustively across the pipeline, so a new
  constructor produces a cascade of `-Wincomplete-patterns` warnings. There is no
  `-Werror`, so the build still "succeeds" — treat those warnings as errors and use
  the warning list as your to-do list. Don't try to land it in one clean edit.
- **The AST is `Cofree` over a hand-rolled functor**, so `Show`/`Eq`/`Ord` are manual
  (`showLangF`/`eqLangF`/`compareLangF` and the per-functor `show*`/`eq*`/`compare*`
  in `Types.hs`), not derived. New constructors need all three by hand, plus the
  `tag*` helpers that order across constructors.
- **Annotations differ by level:** top-level nodes carry `SourceAnnotation` (a span);
  expressions/JSX carry `NodeAnnotation` (span + inferred `Type` + inferred
  `Effect`). The parser fills the latter with dummies (`TUnit`, `EffNone`); inference
  overwrites them.

## Adding to the language

Rough order, since each step's absence shows up as a warning (or crash) in the next:

- **New expression form:** `Types.hs` data + manual show/eq/compare + `mk*` + export →
  `prettyExprF` → `Parse.hs` (`pExprAtom`/`operatorTable`, plus `reservedKeywords` for
  a new keyword) → `InferTyEffect.hs` (`inferTyEffExprTypedM`, and
  `inferTyEffExprTypedWithExpectedM`/`freeVars` if relevant) → `Analysis/*` if the node
  carries or hides effects.
- **New `Type`:** `Types.hs` (+`prettyType`) → `InferTyEffect.hs` (`unifyType`,
  `substType`, `freeEffVarsType`, `instantiateSchema`, `generalizeEffect`) →
  `Parse.hs` (`pBaseType`/`pType`, `pSchema` for `forall` interactions).
- **New `Effect`:** `Types.hs` (`prettyEffectPrec` *and* `readableEffectPrec`; a leaf
  only needs the former, anything with a body wants a `readableBlock` case, and a new
  operator wants an `opList` case) → `Parse.hs` (`pEffectFactor`, or
  `pEffect`/`pEffectTerm` for a new operator) → `test/EffectPrettySpec.hs` (add it to
  `examples`, which round-trips it through the parser) → `InferTyEffect.hs`
  (`substEffect`, `unifyEffect`, `freeEffVarsEffect`) → `Util.hs` (`effSeq`, if it
  interacts with sequencing) → `Analysis/Common.hs` → `Analysis/EffectReadability.hs` →
  `Analysis/HandlerCleanup.hs` and `Analysis/InitialRender.hs` (`footprints` and
  `settlingEffect` both match every constructor, deliberately without a catch-all, so a
  new one shows up as an incomplete-pattern warning). Decide in `settlingEffect`
  whether the new form runs at mount or only arms something for later.
- **New declaration form:** `Types.hs` → `Parse.hs` (`pDecl`, and the `lookAhead`
  keyword set in `parseAnnotatedDeclsOrFail`) → `InferTyEffect.hs`
  (`inferTyEffDeclM`) → `Analysis/InitialRender.hs` (`mountEffect`, if the new form can
  run at mount).
- **New timing `Unit`:** `Types.hs` (`data Unit` + `Pretty Unit`) → `Parse.hs`
  (`pUnit`) → `test/EffectPrettySpec.hs`. `Pretty Unit` must print exactly the
  spelling `pUnit` accepts, or printed delays stop reparsing.
- **Just a new built-in function:** `src/Builtins.hs` only — one name → schema-string
  entry in `builtinFunctionTypes`. The string is parsed by `Parse.pType`, so it must
  use existing syntax. No ripple.

## The paper-conformance tests are load-bearing

`test/PaperRulesSpec.hs` (one test per typing rule) and `test/PaperExamplesSpec.hs`
(the worked examples) are the evidence for the paper's claims, and reviewers run
them.

If one fails, the implementation or the spec is wrong. **Do not relax an assertion,
loosen a string match, or mark a test pending to get green.** Fix the checker, or —
if the *paper* is what's wrong — say so explicitly and stop for a human decision.
`inferTyEffProgramTEST` is exported from `InferTyEffect` specifically for these.

## Public-artifact rules

This repo is read by reviewers and strangers, not just us.

- **Every example must type-check**, and the paper examples' inferred effects must
  match what the paper prints. Each example ends with a comment block recording its
  paper section, the adaptations made to fit Willow's concrete syntax, and the
  cascades it should infer; a new example needs one too.
- **`README.md` is the contract.** If you change a flag, a module name,
  or a printed effect, update the README table in the same change.
  Dangling links in a public artifact read as rot.
- **Keep internal-only material out**: submission venues, review status, internal
  planning docs, private-repo paths, TODO-to-self notes, and references to how the
  work was staged. Prose here should make sense to someone who has only the paper
  and this checkout.
- **No dead surface.** Ship flags, modules, and examples that do something.
