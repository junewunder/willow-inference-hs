{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-pattern-binds #-}

module Analysis.Common
  ( fullEffectVar
  , fullEffect
    -- * Delta operations
  , findDependents
  , cascadeEffect
    -- * Effect utilities
  , hasLoopsInEffect
    -- * Effect transformations
  , simplifyEffect
  , removeRepeatEffects
  , relevantEffect
    -- * Sub-effecting (appendix Fig 15)
  , subEffect
  ) where

import Import
import RIO
import RIO.Map ( (!?) )
import Util
import qualified RIO.Map as Map
import qualified RIO.List as List
import qualified RIO.Text as Text

-- | Full effect of a variable
fullEffectVar :: Delta -> Text -> Effect
fullEffectVar (Delta delta) x =
  let Just (DeltaEntry _ downward) = delta !? x in
  let cascaded = cascadeEffect (Delta delta) downward [] [x] in
  simplifyEffect $ fst $ removeRepeatEffects [] cascaded

-- | Full effect of an effect
fullEffect :: Delta -> Effect -> Effect
fullEffect _ EffNone = EffNone
fullEffect _ (EffLoop x) = EffLoop x
fullEffect delta (EffStateChange x) =
  let cascaded = cascadeEffect delta (EffStateChange x) [] [] in
  simplifyEffect $ fst $ removeRepeatEffects [] cascaded
fullEffect delta (EffAfter t e) = EffAfter t $ fullEffect delta e
fullEffect delta (EffSeq es) =
  let re = map (fullEffect delta) es
   in List.foldr effSeq EffNone re
fullEffect delta (EffBranch e1 e2) = EffBranch (fullEffect delta e1) (fullEffect delta e2)
fullEffect _ (EffVar x) = EffVar x
-- Event-layer leaves do not expand via Delta (like EffVar); modalities recurse.
fullEffect _ (EffEvent lbl) = EffEvent lbl
fullEffect delta (EffAlways lbl e) = EffAlways lbl (fullEffect delta e)
fullEffect delta (EffEventually lbl e) = EffEventually lbl (fullEffect delta e)
fullEffect _ (EffCancel lbl) = EffCancel lbl
fullEffect _ (EffRemove lbl) = EffRemove lbl

-- | Find all state variables that depend on the given state variable
findDependents :: Delta -> Text -> [Text]
findDependents (Delta delta) x =
  Map.keys $ Map.filter (\(DeltaEntry ys _) -> x `elem` ys) delta

-- | Cascade effects through dependencies, tracking visited nodes to detect loops
cascadeEffect :: Delta -> Effect -> [Text] -> [Text] -> Effect
cascadeEffect _ EffNone _ _ = EffNone
cascadeEffect _ (EffLoop x) _ _ = EffLoop x
cascadeEffect (Delta delta) (EffStateChange x) noRepeat visited =
  if List.elem x visited then EffLoop x else
    let Just (DeltaEntry _ downward) = delta !? x in
    let visited' = x : visited in
    let dependents = findDependents (Delta delta) x List.\\ noRepeat in
    let noRepeat' = dependents ++ noRepeat in
    let dependentsEff = seqManyStCh dependents in
    let cascade1 = cascadeEffect (Delta delta) downward noRepeat' visited' in
    let cascade2 = cascadeEffect (Delta delta) dependentsEff noRepeat' visited' in
    effSeq (effSeq (EffStateChange x) cascade2) cascade1
cascadeEffect delta (EffAfter delay f1) _ visited =
  EffAfter delay (cascadeEffect delta f1 [] visited)
cascadeEffect delta (EffSeq effs) noRepeat visited =
  List.foldl effSeq EffNone (map (\f -> cascadeEffect delta f noRepeat visited) effs)
cascadeEffect delta (EffBranch f1 f2) noRepeat visited =
  EffBranch (cascadeEffect delta f1 noRepeat visited) (cascadeEffect delta f2 noRepeat visited)
cascadeEffect _ (EffVar x) _ _ = EffVar x
-- Event-layer leaves do not cascade via Delta (like EffVar); modalities recurse.
cascadeEffect _ (EffEvent lbl) _ _ = EffEvent lbl
cascadeEffect delta (EffAlways lbl f1) _ visited =
  EffAlways lbl (cascadeEffect delta f1 [] visited)
cascadeEffect delta (EffEventually lbl f1) _ visited =
  EffEventually lbl (cascadeEffect delta f1 [] visited)
cascadeEffect _ (EffCancel lbl) _ _ = EffCancel lbl
cascadeEffect _ (EffRemove lbl) _ _ = EffRemove lbl

-- | Check if an effect contains loops
hasLoopsInEffect :: Effect -> Bool
hasLoopsInEffect (EffLoop _) = True
hasLoopsInEffect (EffSeq effs) = any hasLoopsInEffect effs
hasLoopsInEffect (EffBranch e1 e2) = hasLoopsInEffect e1 || hasLoopsInEffect e2
hasLoopsInEffect (EffAfter _ eff) = hasLoopsInEffect eff
hasLoopsInEffect (EffAlways _ eff) = hasLoopsInEffect eff
hasLoopsInEffect (EffEventually _ eff) = hasLoopsInEffect eff
hasLoopsInEffect _ = False

-- | Simplify an effect by flattening sequences
simplifyEffect :: Effect -> Effect
simplifyEffect EffNone = EffNone
simplifyEffect (EffStateChange x) | isCompilerVar x = EffNone
simplifyEffect (EffSeq effs) =
  List.foldl (\s x -> effSeq s (simplifyEffect x)) EffNone effs
simplifyEffect (EffAfter (Time t1 u1) (EffAfter (Time t2 u2) e)) | u1 == u2 =
  simplifyEffect (EffAfter (Time (t1 + t2) u1) e)
simplifyEffect (EffAfter t e) = EffAfter t $ simplifyEffect e
simplifyEffect (EffBranch e1 e2) = EffBranch (simplifyEffect e1) (simplifyEffect e2)
simplifyEffect (EffAlways lbl e) = EffAlways lbl (simplifyEffect e)
simplifyEffect (EffEventually lbl e) = EffEventually lbl (simplifyEffect e)
simplifyEffect e = e

-- | The sub-effecting relation @F ≤ F′@ of appendix Fig 15, as a pure decision
-- procedure. Decides the closure of the printed rules: SE-TRANS is
-- folded into the structural recursion, and SE-SPLIT-L/R are handled up front
-- by 'mergeDelays' (same-unit delay-merge normalization, justified as an
-- equivalence by SE-SPLIT-L/R).
--
-- Wired into inference ONLY as the purity predicate for
-- T-STATE-DECL / T-LET-DECL (@subEffect F EffNone@ — see
-- 'InferTyEffect.enforcePureStateDefault'); the T-ON-DECL causes check is
-- discharged by accumulation in the inferred-Δ prototype, and unification
-- must not become sub-effecting-aware.
subEffect :: Effect -> Effect -> Bool
subEffect f g = go (mergeDelays f) (mergeDelays g)
  where
    -- Clause shapes are disjoint; checked in this order. Each clause is
    -- labelled with the Fig 8 rule(s) it decides.
    go f1 g1
      -- SE-EQ: F = F′ ⇒ F ≤ F′ (structural Eq on the normalized trees)
      | f1 == g1 = True
      -- SE-ZERO-L: F ≤ F′ ⇒ ○⁰F ≤ F′
      | EffAfter (Time 0 _) f1' <- f1 = go f1' g1
      -- SE-ZERO-R: F ≤ F′ ⇒ F ≤ ○⁰F′
      | EffAfter (Time 0 _) g1' <- g1 = go f1 g1'
      -- SE-PLUS-L: F₁ ≤ F′ and F₂ ≤ F′ ⇒ F₁ + F₂ ≤ F′ (+ is a join).
      -- Checked before SE-PLUS-R: this clause is invertible (the join is
      -- the LEAST upper bound), so splitting the left branch first loses
      -- nothing, e.g. F₁ + F₂ ≤ F₂ + F₁.
      | EffBranch f1' f2' <- f1 = go f1' g1 && go f2' g1
      -- SE-PLUS-R: F ≤ Fᵢ for some i ⇒ F ≤ F₁ + F₂ (each arm is below the branch)
      | EffBranch g1' g2' <- g1 = go f1 g1' || go f1 g2'
      -- SE-MULT (n-ary): F ≤ Fᵢ for some i ⇒ F ≤ F₁ * … * Fₙ (* is a join)
      | EffSeq gs <- g1 = any (go f1) gs
      -- SE-DELAY(-EQ) — see the note below
      | EffAfter (Time t u) f1' <- f1
      , EffAfter (Time t' u') g1' <- g1 =
          if u /= u'
            then False -- cross-unit delays: no printed rule
            else case compare t t' of
              EQ -> go f1' g1' -- SE-DELAY-EQ: F ≤ F′ ⇒ ○ᵗF ≤ ○ᵗF′
              LT -> go f1' (EffAfter (Time (t' - t) u) g1') -- SE-DELAY (rebase)
              GT -> False
      -- SE-EVENTUALLY-BODY: F ≤ F′ ⇒ ◇ℓ⟨v⟩(F) ≤ ◇ℓ⟨v⟩(F′)
      | EffEventually l f1' <- f1
      , EffEventually l' g1' <- g1 = l == l' && go f1' g1'
      -- SE-ALWAYS-BODY: F ≤ F′ ⇒ □ℓ⟨v⟩(F) ≤ □ℓ⟨v⟩(F′)
      | EffAlways l f1' <- f1
      , EffAlways l' g1' <- g1 = l == l' && go f1' g1'
      -- SE-SUBEFFECTING family: · refines into any single leaf
      | EffNone <- f1
      , isSubEffectLeaf g1 = True
      -- Anything else: no printed rule (e.g. EffSeq or EffVar on the left,
      -- EffAfter with a Plus/cross-unit grade, EffLoop, mismatched shapes).
      | otherwise = False
    isSubEffectLeaf eff = case eff of
      EffStateChange _ -> True -- SE-SUBEFFECTING: · ≤ @x
      EffEvent _ -> True -- SE-SUBEFFECTING-NSE: · ≤ ℓ⟨v⟩
      EffEventually _ _ -> True -- SE-SUBEFFECTING-EVENTUALLY: · ≤ ◇ℓ⟨v⟩(F)
      EffAlways _ _ -> True -- SE-SUBEFFECTING-ALWAYS: · ≤ □ℓ⟨v⟩(F)
      EffCancel _ -> True -- SE-SUBEFFECTING-CANCEL: · ≤ ⊘ℓ⟨v⟩
      EffRemove _ -> True -- SE-SUBEFFECTING-REMOVE: · ≤ ✗ℓ⟨v⟩
      _ -> False

-- SE-DELAY note (owner-pinned reading): the printed premise really is
-- @(○^(t−t′) F) ≤ F′@ with @t ≤ t′@ (verified against the rendered
-- willow-preprint.pdf page 31, Fig 15) — as printed, the grade @t−t′@ is NEGATIVE,
-- unrepresentable in 'Delay' ('Time' carries @Int@ ≥ 0 surface values).
-- Reading grades as a group, the premise is equivalent — by SE-DELAY-EQ,
-- SE-SPLIT and SE-ZERO — to the positive-rebase form @F ≤ ○^(t′−t) F′@,
-- which is what the @t < t′@ branch above implements. For simple Time grades
-- that branch is observably VACUOUS: its premise only holds when it collapses
-- to SE-EQ, which 'mergeDelays' normalization has already handled, so e.g.
-- @○¹ʳ@x ≤ ○²ʳ@x@ and @○²ʳ@x ≤ ○¹ʳ@x@ are both False (different grades are
-- incomparable beyond equality). The clause is kept to mirror Fig 8.

-- | Normalize an effect tree for 'subEffect': (a) merge nested same-unit Time
-- delays, @EffAfter (Time a u) (EffAfter (Time b u) e)@ becoming
-- @EffAfter (Time (a+b) u) e@ (justified as an equivalence by SE-SPLIT-L/R,
-- same-unit only), and (b) fold same-unit Plus-of-Times,
-- @Plus (Time a u) (Time b u)@ becoming @Time (a+b) u@. Cross-unit nestings
-- and cross-unit Plus stay untouched (the relation is EQ-only on those).
-- Recurses under all constructors.
--
-- NOT the same as 'simplifyEffect': that one drops compiler-generated state
-- variables to ·, which is wrong for the formal relation.
mergeDelays :: Effect -> Effect
mergeDelays eff = case eff of
  EffAfter d e ->
    case (mergeDelay d, mergeDelays e) of
      (Time a u, EffAfter (Time b u') e')
        | u == u' -> EffAfter (Time (a + b) u) e'
      (d', e') -> EffAfter d' e'
  EffSeq es -> EffSeq (map mergeDelays es)
  EffBranch e1 e2 -> EffBranch (mergeDelays e1) (mergeDelays e2)
  EffAlways l e -> EffAlways l (mergeDelays e)
  EffEventually l e -> EffEventually l (mergeDelays e)
  _ -> eff

-- | Fold same-unit Plus-of-Times grades; see 'mergeDelays'.
mergeDelay :: Delay -> Delay
mergeDelay (Plus d1 d2) =
  case (mergeDelay d1, mergeDelay d2) of
    (Time a u, Time b u') | u == u' -> Time (a + b) u
    (d1', d2') -> Plus d1' d2'
mergeDelay d = d

-- | Remove repeated effects to prevent infinite loops
removeRepeatEffects :: [Text] -> Effect -> (Effect, [Text])
removeRepeatEffects _ EffNone = (EffNone, [])
removeRepeatEffects _ (EffAfter u eff) = (EffAfter u (fst $ removeRepeatEffects [] eff), [])
removeRepeatEffects _ (EffAlways lbl eff) = (EffAlways lbl (fst $ removeRepeatEffects [] eff), [])
removeRepeatEffects _ (EffEventually lbl eff) = (EffEventually lbl (fst $ removeRepeatEffects [] eff), [])
removeRepeatEffects noRepeat e@(EffStateChange x) = if x `elem` noRepeat then (EffNone, []) else (e, [x])
removeRepeatEffects noRepeat (EffSeq effs) =
  let f (a, nr0) b =
        let (b', nr1) = removeRepeatEffects (nr0 ++ noRepeat) b in
        (effSeq a b', nr1) in
  List.foldl f (EffNone, []) effs
removeRepeatEffects noRepeat (EffBranch e1 e2) =
  let (e1', nr1) = removeRepeatEffects noRepeat e1 in
  let (e2', nr2) = removeRepeatEffects noRepeat e2 in
  (EffBranch e1' e2', List.union nr1 nr2)
removeRepeatEffects _ e = (e, [])


-- | Drop state changes to sub-component-internal state, so that a cascade
-- printed for one component names only that component's own variables.
--
-- Instantiating a sub-component prefixes its state with the instance name
-- (@slowUsername.slow@), and the dot is what identifies those here. A caller
-- cannot write such a name, so the dot cannot collide with a user variable.
-- Callers that need the unabridged cascade keep the unfiltered effect around:
-- @Run.displayAllEffects@ prints both whenever they differ.
relevantEffect :: Effect -> Effect
relevantEffect EffNone = EffNone
relevantEffect (EffLoop n) = EffLoop n
relevantEffect (EffStateChange n) | '.' `List.elem` Text.unpack n = EffNone
relevantEffect (EffStateChange n) = EffStateChange n
relevantEffect (EffAfter t e) = EffAfter t (relevantEffect e)
relevantEffect (EffSeq es) =
  let re = map relevantEffect es
  in List.foldr effSeq EffNone re
relevantEffect (EffBranch e1 e2) = EffBranch (relevantEffect e1) (relevantEffect e2)
relevantEffect (EffVar x) = EffVar x
relevantEffect (EffEvent lbl) = EffEvent lbl
relevantEffect (EffAlways lbl e) = EffAlways lbl (relevantEffect e)
relevantEffect (EffEventually lbl e) = EffEventually lbl (relevantEffect e)
relevantEffect (EffCancel lbl) = EffCancel lbl
relevantEffect (EffRemove lbl) = EffRemove lbl
