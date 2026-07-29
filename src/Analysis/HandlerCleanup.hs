-- | The "event handlers cleaned up" analysis (paper §5.4).
--
-- Given the full effect of a variable, walk the effect's graph and check that
-- every event-handler registration is matched by a corresponding @remove@
-- modality. Per the paper, the walk
--
--   * takes the two branches of @+@ SEPARATELY — a handler removed on only one
--     branch is not cleaned up on the other; and
--   * looks INSIDE the @□@ (always) and @◇@ (eventually) modalities — this is
--     what makes @asyncCompute@ come out clean, since each of its one-shot
--     handlers is removed from inside the *other* one's body.
--
-- Two deliberate non-rules, both following the paper's wording:
--
--   * @⊘ℓ⟨v⟩@ (cancel) does NOT discharge a registration. Cancel suppresses one
--     pending firing of the event; @✗ℓ⟨v⟩@ is what unregisters handlers. The
--     paper keeps them separate (§2: "To clean up both, clearTimeout produces
--     cancel and remove effects"), and so does this walk.
--   * A promised firing of @ℓ⟨v⟩@ does NOT discharge a @◇ℓ⟨v⟩@ registration
--     either, even though a one-shot handler is consumed when it fires. Only a
--     @remove@ counts, which is the conservative direction.
--
-- Matching is order-insensitive: a registration is discharged by a @✗@ anywhere
-- on the same path. The remove-then-bind idiom that Willow programs are written
-- in (§2 (ii): "✗click⟨#doc⟩ happens before the new event handler is
-- registered") puts the remove FIRST, so an order-sensitive rule would flag
-- exactly the code the paper holds up as correct.
module Analysis.HandlerCleanup
  ( -- * Results
    HandlerKind (..)
  , StaleHandler (..)
  , CleanupReport (..)
    -- * The check
  , cleanupReport
  , handlersCleanedUp
  , checkComponentCleanup
    -- * Display
  , describeHandler
  , describeStaleHandler
  ) where

import Import
import RIO
import Util
import qualified RIO.List as List
import qualified RIO.Map as Map
import qualified RIO.Set as Set
import Prettyprinter (layoutCompact, pretty)
import Prettyprinter.Render.Text (renderStrict)
import Analysis.Common (fullEffectVar, simplifyEffect)

-- | How a handler was registered: @□ℓ⟨v⟩@ from @bind@ (fires every time the
-- event fires) or @◇ℓ⟨v⟩@ from @once@ / @setTimeout@ (fires once).
data HandlerKind = Persistent | OneShot
  deriving (Eq, Ord, Show)

-- | A handler registration with no matching @remove@.
data StaleHandler = StaleHandler
  { staleLabel :: EventLabel
    -- ^ the event whose handlers are left behind
  , staleKind :: HandlerKind
    -- ^ @□@ or @◇@
  , staleEveryBranch :: Bool
    -- ^ True when EVERY path that registers this handler leaves it behind;
    -- False when some branch does remove it and another does not.
  , staleUnderVar :: Bool
    -- ^ True when a leaking path runs through an effect variable @?e@ or a
    -- @loop[x]@ node, either of which could hide the missing @remove@. The
    -- finding is then "not confirmed clean" rather than "definitely leaked".
  }
  deriving (Eq, Ord, Show)

-- | The verdict for one effect: every handler it registers, and the subset of
-- those that are left behind.
data CleanupReport = CleanupReport
  { crHandlers :: [(EventLabel, HandlerKind)]
    -- ^ every registration the walk found, deduplicated
  , crStale :: [StaleHandler]
    -- ^ those with no matching @remove@ on at least one path
  }
  deriving (Eq, Show)

-- | What one path through the effect graph does to the event layer.
data Footprint = Footprint
  { fpRegistered :: Set (EventLabel, HandlerKind)
  , fpRemoved :: Set EventLabel
  , fpOpaque :: Bool -- ^ the path went through a @?e@ or a @loop[x]@
  }
  deriving (Eq, Ord, Show)

instance Semigroup Footprint where
  Footprint r1 x1 o1 <> Footprint r2 x2 o2 =
    Footprint (Set.union r1 r2) (Set.union x1 x2) (o1 || o2)

instance Monoid Footprint where
  mempty = Footprint Set.empty Set.empty False

-- | The paths through an effect's graph, one 'Footprint' each: @+@ forks into
-- separate paths, @*@ merges footprints, and the body of a @□@/@◇@ is walked
-- as part of the path that registers it.
--
-- The product at @*@ is bounded by deduplication: a path is characterised only
-- by which labels it registers and removes, so the list stays small (a handful
-- of labels) no matter how many @+@ nodes a deep cascade contains.
footprints :: Effect -> [Footprint]
footprints eff = case eff of
  EffNone -> [mempty]
  EffStateChange _ -> [mempty]
  -- An event FIRING is not a registration and not a removal.
  EffEvent _ -> [mempty]
  -- Cancel suppresses a pending firing; it leaves the handlers registered.
  EffCancel _ -> [mempty]
  EffRemove lbl -> [mempty {fpRemoved = Set.singleton lbl}]
  EffAfter _ body -> footprints body
  EffAlways lbl body -> register Persistent lbl (footprints body)
  EffEventually lbl body -> register OneShot lbl (footprints body)
  EffSeq es -> List.foldl' merge [mempty] (map footprints es)
  EffBranch e1 e2 -> dedup (footprints e1 ++ footprints e2)
  -- Both stand for effects the walk cannot see: an uninstantiated effect
  -- variable, and the point where graph expansion cut off a cycle.
  EffVar _ -> [mempty {fpOpaque = True}]
  EffLoop _ -> [mempty {fpOpaque = True}]
  where
    register kind lbl =
      map (\fp -> fp {fpRegistered = Set.insert (lbl, kind) (fpRegistered fp)})
    merge before rest = dedup [b <> r | b <- before, r <- rest]
    dedup = Set.toList . Set.fromList

-- | Walk an effect and report which handlers it registers and which of those
-- are left behind. This is the algorithm of §5.4.
cleanupReport :: Effect -> CleanupReport
cleanupReport eff =
  CleanupReport
    { crHandlers = registrations
    , crStale = mapMaybe staleness registrations
    }
  where
    paths = footprints eff
    registrations = Set.toList (Set.unions (map fpRegistered paths))

    staleness reg@(lbl, kind)
      | null leaking = Nothing
      | otherwise =
          Just
            StaleHandler
              { staleLabel = lbl
              , staleKind = kind
              , staleEveryBranch = length leaking == length registering
              , staleUnderVar = any fpOpaque leaking
              }
      where
        registering = filter (Set.member reg . fpRegistered) paths
        leaking = filter (not . Set.member lbl . fpRemoved) registering

-- | True when every handler the effect registers is matched by a @remove@.
handlersCleanedUp :: Effect -> Bool
handlersCleanedUp = null . crStale . cleanupReport

-- | Run the check over a component's Δ, once per bound variable, on that
-- variable's FULL effect (§5.4: "Given the full effect of a variable…").
-- Variables whose full effect registers no handler at all are dropped: they
-- have nothing to clean up and would only pad the report.
checkComponentCleanup :: Delta -> [(Text, CleanupReport)]
checkComponentCleanup delta =
  [ (x, report)
  | x <- filter (not . isCompilerVar) (keys delta)
  , let report = cleanupReport (simplifyEffect (fullEffectVar delta x))
  , not (null (crHandlers report))
  ]
  where
    keys (Delta d) = Map.keys d

-- | A registration in the effect's own concrete syntax, e.g.
-- @always click\<#doc\>@.
describeHandler :: (EventLabel, HandlerKind) -> Text
describeHandler (lbl, kind) = keyword kind <> " " <> renderLabel lbl
  where
    keyword Persistent = "always"
    keyword OneShot = "eventually"

-- | A one-line explanation of a stale handler, for the CLI report.
describeStaleHandler :: StaleHandler -> Text
describeStaleHandler sh =
  describeHandler (staleLabel sh, staleKind sh)
    <> " — no matching remove "
    <> renderLabel (staleLabel sh)
    <> qualifier
  where
    qualifier
      | staleUnderVar sh =
          " on a path through an unresolved effect (cannot confirm cleanup)"
      | staleEveryBranch sh = " (handler left behind)"
      | otherwise = " on some branches (handler left behind there)"

renderLabel :: EventLabel -> Text
renderLabel = renderStrict . layoutCompact . pretty
