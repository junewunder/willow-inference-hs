-- | The initial-render analysis: what a component does when it mounts.
--
-- Every @on x do { … }@ block runs once at mount, so the mount effect is the
-- sequence of all of them. The event-layer modalities split what that effect
-- means into three parts, and keeping them apart is the whole point of this
-- analysis:
--
--   * effects that SETTLE — state changes and the delays between them. The
--     component keeps re-rendering until these are exhausted, so this is the
--     part that decides how long mounting takes.
--   * handlers that are ARMED — @□ℓ⟨v⟩(F)@ and @◇ℓ⟨v⟩(F)@ register @F@; they do
--     NOT run it at mount. Their bodies are excluded from the settling part
--     precisely because they wait for @ℓ⟨v⟩@ to fire.
--   * events that are SCHEDULED — a promised firing @ℓ⟨v⟩@ reached without
--     passing through a modality, as @setTimeout@'s @○¹⁰⁰ᵐˢ timeout⟨⟩@ is. An
--     armed body will run when it arrives, with no user interaction, so mount
--     is not really over when the settling part finishes.
--
-- A component whose settling part contains a @loop[x]@ never finishes mounting:
-- that is the inter-render loop of §2, reached on the very first render.
module Analysis.InitialRender
  ( InitialRenderInfo (..)
  , analyzeComponentInitialRender
    -- * The three parts of a mount effect
  , mountEffect
  , settlingEffect
  , armedHandlers
  , scheduledEvents
    -- * Derived facts
  , settleTime
  , settleLoops
  , alwaysLoops
    -- * Display
  , describeSettleTime
  ) where

import Import
import RIO
import Util
import qualified RIO.List as List
import qualified RIO.Map as Map
import qualified RIO.Text as Text
import Control.Comonad.Cofree (Cofree (..))
import Prettyprinter (layoutCompact, pretty)
import Prettyprinter.Render.Text (renderStrict)
import Analysis.Common (fullEffect, simplifyEffect)
import Analysis.HandlerCleanup (HandlerKind, cleanupReport, crHandlers)

-- | What one component does when it mounts.
data InitialRenderInfo = InitialRenderInfo
  { iriMountEffect :: Effect
    -- ^ the full cascaded effect of every @on@ block, sequenced
  , iriSettling :: Effect
    -- ^ the part of it that runs to completion at mount ('settlingEffect')
  , iriSettleTime :: [(Int, Unit)]
    -- ^ longest delay chain through the settling part, per unit
  , iriArmed :: [(EventLabel, HandlerKind)]
    -- ^ handlers registered at mount, whose bodies wait for their event
  , iriScheduled :: [(EventLabel, [[(Int, Unit)]])]
    -- ^ events the mount effect itself promises to fire, and when
  , iriLoops :: [Text]
    -- ^ state variables the settling part loops through, if any
  , iriAlwaysLoops :: Bool
    -- ^ True when EVERY path through the settling part reaches a loop, so mount
    -- can never finish; False when some branch escapes and mount only /may/
    -- hang. Same distinction 'Analysis.HandlerCleanup.staleEveryBranch' draws.
  }
  deriving (Eq, Show)

-- | Analyze one component's mount behaviour.
analyzeComponentInitialRender :: Delta -> AnnotatedComponent -> InitialRenderInfo
analyzeComponentInitialRender delta comp =
  InitialRenderInfo
    { iriMountEffect = mounted
    , iriSettling = settling
    , iriSettleTime = settleTime settling
    , iriArmed = armedHandlers mounted
    , iriScheduled = scheduledEvents mounted
    , iriLoops = settleLoops settling
    , iriAlwaysLoops = alwaysLoops settling
    }
  where
    mounted = mountEffect delta comp
    settling = settlingEffect mounted

-- | The effect of mounting: every @on@ block's body, fully cascaded through Δ
-- and sequenced. State and @let@ declarations contribute nothing — their
-- initializers are required to be pure (T-STATE-DECL / T-LET-DECL).
mountEffect :: Delta -> AnnotatedComponent -> Effect
mountEffect delta (_ :< ComponentF _ _ _ decls _ _) =
  simplifyEffect $ List.foldl' effSeq EffNone (concatMap blockEffect decls)
  where
    blockEffect (_ :< DeclEffectF _ (Block stmts)) =
      map (fullEffect delta . getEffect) stmts
    blockEffect _ = []

-- | The part of a mount effect that runs to completion at mount.
--
-- Every event-layer node drops out, each for its own reason: a @□@/@◇@ body
-- waits for its event, a promised firing @ℓ⟨v⟩@ is reported separately as
-- scheduled, and @⊘@/@✗@ only touch the handler table. What survives is state
-- changes, the delays between them, and the branches and loops among them.
--
-- Dropping those nodes leaves delays and branches with nothing under them
-- (@○¹⁰⁰ᵐˢ ·@ from a @setTimeout@, @· + ·@ from a conditional @bind@), so the
-- result is pruned back to @·@ rather than printed as empty scaffolding. A
-- branch keeps both arms as soon as one carries something — @?F + ·@ says the
-- caller's effect may or may not run, which is a real thing to report.
settlingEffect :: Effect -> Effect
settlingEffect = prune . simplifyEffect . go
  where
    go eff = case eff of
      EffNone -> EffNone
      EffLoop x -> EffLoop x
      EffStateChange x -> EffStateChange x
      EffVar v -> EffVar v
      EffAfter d body -> EffAfter d (go body)
      EffSeq es -> List.foldl' effSeq EffNone (map go es)
      EffBranch e1 e2 -> EffBranch (go e1) (go e2)
      EffEvent _ -> EffNone
      EffAlways _ _ -> EffNone
      EffEventually _ _ -> EffNone
      EffCancel _ -> EffNone
      EffRemove _ -> EffNone

    prune eff = case eff of
      EffAfter d body -> case prune body of
        EffNone -> EffNone
        body' -> EffAfter d body'
      EffSeq es -> List.foldl' effSeq EffNone (map prune es)
      EffBranch e1 e2 -> case (prune e1, prune e2) of
        (EffNone, EffNone) -> EffNone
        (e1', e2') -> EffBranch e1' e2'
      _ -> eff

-- | Handlers armed at mount. Shares 'cleanupReport'’s notion of a registration
-- so that @--first@ and @--cleanup@ can never disagree about what was bound.
armedHandlers :: Effect -> [(EventLabel, HandlerKind)]
armedHandlers = crHandlers . cleanupReport

-- | Events the mount effect promises to fire, reached WITHOUT passing through a
-- modality. A firing inside a @□@/@◇@ body is that handler's business, not
-- mount's, so the walk does not descend into one.
--
-- Each event is paired with every distinct delay it can arrive after: branches
-- can issue the same request at different times, and which arrival you get
-- depends on the branch taken, so all of them are reported.
scheduledEvents :: Effect -> [(EventLabel, [[(Int, Unit)]])]
scheduledEvents eff =
  [ (lbl, List.nub [order d | (lbl', d) <- arrivals, lbl' == lbl])
  | lbl <- List.nub (map fst arrivals)
  ]
  where
    arrivals = go Map.empty eff
    go acc e = case e of
      EffEvent lbl -> [(lbl, acc)]
      EffAfter (Time n u) body -> go (Map.insertWith (+) u n acc) body
      EffAfter (Plus d1 d2) body -> go acc (EffAfter d1 (EffAfter d2 body))
      EffSeq es -> concatMap (go acc) es
      EffBranch e1 e2 -> go acc e1 ++ go acc e2
      EffAlways _ _ -> []
      EffEventually _ _ -> []
      _ -> []

-- | How long the settling part takes, as a total per time unit.
--
-- Delays add along a path (@○¹ʳ ○¹ʳ F@ is two renders) and branches take the
-- worst case, so @*@ and @+@ both maximize: their operands start at the same
-- moment, and only nesting under @○@ advances the clock. Units do not convert
-- into one another, so each is accumulated separately.
settleTime :: Effect -> [(Int, Unit)]
settleTime = order . go
  where
    go eff = case eff of
      EffAfter (Time n u) body -> Map.insertWith (+) u n (go body)
      EffAfter (Plus d1 d2) body -> go (EffAfter d1 (EffAfter d2 body))
      EffSeq es -> List.foldl' (Map.unionWith max) Map.empty (map go es)
      EffBranch e1 e2 -> Map.unionWith max (go e1) (go e2)
      -- A loop has no finite settle time; 'iriLoops' reports it instead.
      _ -> Map.empty

-- | A per-unit delay total, in 'Unit' order and without zero entries.
order :: Map Unit Int -> [(Int, Unit)]
order m = [(n, u) | (u, n) <- Map.toAscList m, n > 0]

-- | State variables the settling part loops through — an inter-render loop
-- entered on the first render, so mount may never finish.
settleLoops :: Effect -> [Text]
settleLoops = List.nub . go
  where
    go eff = case eff of
      EffLoop x -> [x]
      EffAfter _ body -> go body
      EffSeq es -> concatMap go es
      EffBranch e1 e2 -> go e1 ++ go e2
      _ -> []

-- | True when no path through the settling part escapes a loop.
--
-- @+@ needs BOTH arms to loop (one that terminates is a way out), while @*@
-- needs only one operand to loop: its operands all happen, so a single
-- non-terminating one hangs the mount regardless of the others.
alwaysLoops :: Effect -> Bool
alwaysLoops eff = case eff of
  EffLoop _ -> True
  EffAfter _ body -> alwaysLoops body
  EffSeq es -> any alwaysLoops es
  EffBranch e1 e2 -> alwaysLoops e1 && alwaysLoops e2
  _ -> False

-- | A settle time in the effect language's own grade syntax, e.g. @1r@, or
-- @100ms + 1r@ when several units are involved.
describeSettleTime :: [(Int, Unit)] -> Text
describeSettleTime [] = "immediate"
describeSettleTime ts =
  Text.intercalate " + " [Text.pack (show n) <> renderUnit u | (n, u) <- ts]
  where
    renderUnit = renderStrict . layoutCompact . pretty
