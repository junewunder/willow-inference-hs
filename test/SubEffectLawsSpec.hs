-- | Algebraic laws of the sub-effecting relation, checked as QuickCheck
-- properties over generated effects.
--
-- 'PaperRulesSpec' pins one hand-built instance per printed rule; this suite
-- checks the laws those rules are meant to add up to. In particular + is a
-- JOIN (least upper bound): each arm is below the branch, and the branch is
-- below anything both arms are below.
module SubEffectLawsSpec (spec) where

import Import
import Analysis.Common (subEffect)
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck

spec :: Spec
spec = modifyMaxSuccess (const 2000) $ describe "Sub-effecting laws (Analysis.Common.subEffect)" $ do

  it "reflexivity: F ≤ F" $
    property $ \(Eff f) -> subEffect f f

  it "each arm is below the branch: F₁ ≤ F₁ + F₂" $
    property $ \(Eff f1) (Eff f2) -> subEffect f1 (EffBranch f1 f2)

  it "each arm is below the branch: F₂ ≤ F₁ + F₂" $
    property $ \(Eff f1) (Eff f2) -> subEffect f2 (EffBranch f1 f2)

  it "the branch is the least such: F₁ ≤ F′ and F₂ ≤ F′ imply F₁ + F₂ ≤ F′" $
    forAllShrink genCommonUpper shrinkTriple $ \(f1, f2, g) ->
      subEffect f1 g && subEffect f2 g ==> subEffect (EffBranch f1 f2) g

  it "the old direction is gone: F₁ + F₂ ≤ F₁ fails for some F₁, F₂" $
    expectFailure $ property $ \(Eff f1) (Eff f2) -> subEffect (EffBranch f1 f2) f1

  it "a branch is below one of its arms only if the other arm is too: F₁ + F₂ ≤ F₁ implies F₂ ≤ F₁" $
    forAllShrink genArmPair shrinkPair $ \(f1, f2) ->
      subEffect (EffBranch f1 f2) f1 ==> subEffect f2 f1

  it "transitivity: F ≤ F′ and F′ ≤ F″ imply F ≤ F″" $
    forAllShrink genChain shrinkTriple $ \(f, g, h) ->
      subEffect f g && subEffect g h ==> subEffect f h

-- ---------------------------------------------------------------------------
-- Generators

newtype Eff = Eff Effect
  deriving (Show)

instance Arbitrary Eff where
  arbitrary = Eff <$> sized (genEffect . min 4)
  shrink (Eff e) = Eff <$> shrinkEffect e

eventLabels :: [EventLabel]
eventLabels = [EventLabel "click" ["#doc"], EventLabel "timeout" []]

genLabel :: Gen EventLabel
genLabel = elements eventLabels

genDelay :: Gen Delay
genDelay =
  frequency
    [ (4, genTime)
    , (1, Plus <$> genTime <*> genTime)
    ]
  where
    genTime = Time <$> choose (0, 2) <*> elements [Renders, Millis]

genLeaf :: Gen Effect
genLeaf =
  frequency
    [ (3, pure EffNone)
    , (5, EffStateChange <$> elements ["x", "y", "z"])
    , (2, EffEvent <$> genLabel)
    , (1, EffCancel <$> genLabel)
    , (1, EffRemove <$> genLabel)
    , (1, pure (EffVar (EffVarName "e")))
    , (1, pure (EffLoop "x"))
    ]

-- | Effects of depth at most @n@. Sequences go through 'mkEffSeq', the smart
-- constructor inference uses, so they have the shapes inference produces.
genEffect :: Int -> Gen Effect
genEffect n
  | n <= 0 = genLeaf
  | otherwise =
      frequency
        [ (3, genLeaf)
        , (2, EffAfter <$> genDelay <*> sub)
        , (2, mkEffSeq <$> (choose (2, 3) >>= flip vectorOf sub))
        , (3, EffBranch <$> sub <*> sub)
        , (1, EffAlways <$> genLabel <*> sub)
        , (1, EffEventually <$> genLabel <*> sub)
        ]
  where
    sub = genEffect (n - 1)

shrinkEffect :: Effect -> [Effect]
shrinkEffect eff = case eff of
  EffNone -> []
  EffAfter d e -> e : (EffAfter d <$> shrinkEffect e)
  EffSeq es -> es <> (mkEffSeq <$> shrinkList shrinkEffect es)
  EffBranch a b ->
    [a, b] <> [EffBranch a' b | a' <- shrinkEffect a] <> [EffBranch a b' | b' <- shrinkEffect b]
  EffAlways l e -> e : (EffAlways l <$> shrinkEffect e)
  EffEventually l e -> e : (EffEventually l <$> shrinkEffect e)
  _ -> [EffNone]

shrinkPair :: (Effect, Effect) -> [(Effect, Effect)]
shrinkPair (a, b) = [(a', b) | a' <- shrinkEffect a] <> [(a, b') | b' <- shrinkEffect b]

shrinkTriple :: (Effect, Effect, Effect) -> [(Effect, Effect, Effect)]
shrinkTriple (a, b, c) =
  [(a', b, c) | a' <- shrinkEffect a]
    <> [(a, b', c) | b' <- shrinkEffect b]
    <> [(a, b, c') | c' <- shrinkEffect c]

-- | An effect above @g@, built only from rules the checker has: SE-PLUS-R
-- (add an arm), SE-MULT (sequence it with others), SE-ZERO-R (○⁰), and
-- SE-SUBEFFECTING (· into a leaf), applied at the top or congruently under
-- a delay, a branch arm, or a □/◇ body. Sequence elements are never
-- rewritten: the relation has no *-monotonicity rule.
genAbove :: Effect -> Gen Effect
genAbove g = do
  steps <- choose (0, 2 :: Int)
  foldM (\e _ -> step e) g [1 .. steps]
  where
    other = genEffect 2
    step e =
      oneof $
        [ EffBranch e <$> other
        , flip EffBranch e <$> other
        , do
            before <- choose (0, 2) >>= flip vectorOf other
            after <- choose (0, 1) >>= flip vectorOf other
            pure (EffSeq (before <> [e] <> after))
        , pure (EffAfter (Time 0 Renders) e)
        ]
          <> inside e
    inside e = case e of
      EffNone -> [EffStateChange <$> elements ["x", "y"], EffEvent <$> genLabel]
      EffAfter d e' -> [EffAfter d <$> step e']
      EffBranch a b -> [(`EffBranch` b) <$> step a, EffBranch a <$> step b]
      EffAlways l e' -> [EffAlways l <$> step e']
      EffEventually l e' -> [EffEventually l <$> step e']
      _ -> []

-- | An effect below @g@: the dual of 'genAbove' (take one arm of a branch or
-- one element of a sequence, or refine a leaf to ·), at the top or under a
-- delay, a branch arm, or a □/◇ body.
genBelow :: Effect -> Gen Effect
genBelow g = do
  steps <- choose (0, 2 :: Int)
  foldM (\e _ -> step e) g [1 .. steps]
  where
    step e = case e of
      EffBranch a b -> oneof [pure a, pure b, (`EffBranch` b) <$> step a, EffBranch a <$> step b]
      EffSeq es -> elements es
      EffAfter d e' -> EffAfter d <$> step e'
      EffAlways l e' -> oneof [pure EffNone, EffAlways l <$> step e']
      EffEventually l e' -> oneof [pure EffNone, EffEventually l <$> step e']
      EffStateChange _ -> pure EffNone
      EffEvent _ -> pure EffNone
      EffCancel _ -> pure EffNone
      EffRemove _ -> pure EffNone
      _ -> pure e

-- | Two effects and a common upper bound, which half the time is built to
-- be above both and half the time is arbitrary (so the premise is exercised
-- on shapes the builder would not produce).
genCommonUpper :: Gen (Effect, Effect, Effect)
genCommonUpper = do
  f1 <- genEffect 3
  f2 <- genEffect 3
  g <-
    oneof
      [ genEffect 3
      , genAbove (EffBranch f2 f1)
      , genAbove (EffSeq [f1, f2])
      , genAbove f1 >>= \u -> genAbove (EffBranch u f2)
      ]
  pure (f1, f2, g)

-- | Two arms, the second below the first half the time (so a branch of them
-- can be below the first arm) and arbitrary otherwise.
genArmPair :: Gen (Effect, Effect)
genArmPair = do
  f1 <- genEffect 3
  f2 <- oneof [genBelow f1, genEffect 3]
  pure (f1, f2)

-- | A chain F ≤ F′ ≤ F″, built around a random middle, with an arbitrary
-- end mixed in some of the time.
genChain :: Gen (Effect, Effect, Effect)
genChain = do
  g <- genEffect 3
  f <- frequency [(4, genBelow g), (1, genEffect 3)]
  h <- frequency [(4, genAbove g), (1, genEffect 3)]
  pure (f, g, h)
