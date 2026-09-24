-- | Laws of the effect-variable machinery in "InferTyEffect" (instantiation,
-- unification, generalisation, substitution), checked as QuickCheck
-- properties over generated types and effects.
--
-- These are the textbook Hindley–Milner invariants with rigid (written) and
-- flexible (unification) variables. "EffectPolymorphismSpec" pins the same
-- behaviour on whole programs.
module EffectVariableLawsSpec (spec) where

import Import
import InferenceMonad (InferenceError, InferenceM, runInferenceWithContext)
import InferTyEffect
  ( EffSubst
  , freeEffVarsEffect
  , freeEffVarsType
  , generalizeEffect
  , instantiateSchema
  , substType
  , unifyEffect
  , unifyType
  , writtenNamesType
  )
import RIO.Process (mkDefaultProcessContext)
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck
import qualified RIO.Map as Map
import qualified RIO.Set as Set
import qualified RIO.Text as Text

spec :: Spec
spec = modifyMaxSuccess (const 1000) $ describe "Effect-variable laws (InferTyEffect)" $ do

  describe "instantiation" $ do
    it "replaces every binder by a unification variable, never by a written one" $
      property $ \(Ty ty) -> ioProperty $ do
        inst <- runInference (instantiateSchema ty)
        pure $ case (ty, inst) of
          (TArrow {}, TArrow vs _ _ _) ->
            counterexample (show inst) $
              null vs .&&. writtenFree inst === writtenFree ty
          _ -> inst === ty

    it "draws variables that occur nowhere in the schema" $
      property $ \(Ty ty) -> ioProperty $ do
        inst <- runInference (instantiateSchema ty)
        let new = freeEffVarsType inst Set.\\ freeEffVarsType ty
        pure $ counterexample (show inst) $
          all isUnif new .&&. Set.null (Set.map (\case Unif n -> n; Written _ -> -1) new `Set.intersection` unifIdsIn ty)

  describe "unification" $ do
    it "binds unification variables only" $
      property $ \(Eff e1) (Eff e2) -> ioProperty $ do
        result <- tryInference (unifyEffect e1 e2)
        pure $ case result of
          Left _ -> property True
          Right s -> counterexample (show s) $ all isUnif (Map.keys s)

    it "never unifies two different written variables" $
      forAll (distinctPair writtenNames) $ \(a, b) -> ioProperty $ do
        result <- tryInference (unifyEffect (EffVar a) (EffVar b))
        pure (isLeft result)

    it "unifies a schema with a renaming of its binders, binding nothing" $
      property $ \(Ty ty) -> ioProperty $ do
        let renamed = renameBinders ty
        result <- tryInference (unifyType ty renamed)
        pure $ counterexample (show renamed) $ case result of
          Left err -> counterexample (show err) False
          Right s -> s === Map.empty

  describe "generalisation" $ do
    -- fev(gen(Γ, τ)) = fev(τ) ∩ fev(Γ): what the context owns stays free, and
    -- everything else is bound.
    it "never quantifies a variable free in the context, and quantifies all others" $
      property $ \(Ctx ctx) (Ty ty) ->
        let gen = generalizeEffect ctx ty
         in counterexample (show gen) $
              freeEffVarsType gen === (freeEffVarsType ty `Set.intersection` arrowOnly ty ctx)

    it "quantifies everything else, so the generalised type is an instance of itself" $
      property $ \(Ctx ctx) (Ty ty) -> ioProperty $ do
        let gen = generalizeEffect ctx ty
        result <- tryInference (instantiateSchema gen >>= unifyType (stripBinders ty))
        pure $ counterexample (show gen) (isRight result)

  describe "substitution" $ do
    it "never touches a variable bound by the arrow's binder list" $
      forAll genSchema $ \ty -> property $ \(Eff e) ->
        let s = Map.fromList [(Written v, e) | v <- binders ty]
         in substType s ty === ty

    it "is capture-avoiding: the free variables of θ(τ) are those of θ's images of fev(τ)" $
      property $ \(Ty ty) (Subst s) ->
        let image k = maybe (Set.singleton k) freeEffVarsEffect (Map.lookup k s)
         in freeEffVarsType (substType s ty) === Set.unions (map image (toList (freeEffVarsType ty)))

-- ---------------------------------------------------------------------------
-- Running inference

-- | Run an inference action with the fresh-variable counter starting at 1000,
-- above every unification variable the generators produce, as if those had
-- been drawn earlier in the same run.
tryInference :: InferenceM a -> IO (Either InferenceError a)
tryInference action = do
  logOptions <- logOptionsHandle stderr False
  withLogFunc logOptions $ \logFunc -> do
    processContext <- mkDefaultProcessContext
    varCounter <- newIORef 1000
    let app = RIOApp logFunc processContext testOptions varCounter
    runRIO app $ runInferenceWithContext Nothing "law" action

runInference :: InferenceM a -> IO a
runInference action = tryInference action >>= either (error . show) pure

-- ---------------------------------------------------------------------------
-- Helpers

isUnif :: EffVarKey -> Bool
isUnif (Unif _) = True
isUnif (Written _) = False

writtenFree :: Type -> Set EffVarName
writtenFree ty = Set.fromList [v | Written v <- toList (freeEffVarsType ty)]

-- | Every unification variable number in a type, free or not.
unifIdsIn :: Type -> Set Int
unifIdsIn ty = case ty of
  TArrow _ a r e -> unifIdsIn a <> unifIdsIn r <> Set.fromList [n | Unif n <- toList (freeEffVarsEffect e)]
  TPair a b -> unifIdsIn a <> unifIdsIn b
  _ -> Set.empty

stripBinders :: Type -> Type
stripBinders (TArrow _ a r e) = TArrow [] a r e
stripBinders ty = ty

-- | Generalisation only binds on an arrow; any other type keeps all of its
-- free variables, so the expected survivors are all of them.
arrowOnly :: Type -> Set EffVarKey -> Set EffVarKey
arrowOnly (TArrow {}) ctx = ctx
arrowOnly ty _ = freeEffVarsType ty

-- | Rename a schema's binders to names that occur nowhere in it.
renameBinders :: Type -> Type
renameBinders ty@(TArrow vs a r e) =
  let taken = writtenNamesType ty
      fresh = take (length vs) [n | k <- [0 :: Int ..], let n = EffVarName ("R" <> Text.pack (show k)), n `Set.notMember` taken]
      s = Map.fromList (zip (map Written vs) (map EffVar fresh))
      TArrow _ a' r' e' = substType s (TArrow [] a r e)
   in TArrow fresh a' r' e'
renameBinders ty = ty

distinctPair :: [EffVarName] -> Gen (EffVarName, EffVarName)
distinctPair names = do
  a <- elements names
  b <- elements (filter (/= a) names)
  pure (a, b)

-- ---------------------------------------------------------------------------
-- Generators

-- | Written names include e0 and e1, the names fresh variables used to take.
writtenNames :: [EffVarName]
writtenNames = map EffVarName ["F", "G", "e", "e0", "e1"]

genKey :: Gen EffVarKey
genKey = oneof [Written <$> elements writtenNames, Unif <$> choose (0, 3)]

newtype Eff = Eff Effect
  deriving (Show)

instance Arbitrary Eff where
  arbitrary = Eff <$> sized (genEffect . min 3)
  shrink (Eff e) = Eff <$> shrinkEffect e

newtype Ty = Ty Type
  deriving (Show)

instance Arbitrary Ty where
  arbitrary = Ty <$> sized (genType . min 3)
  shrink (Ty t) = Ty <$> shrinkType t

newtype Ctx = Ctx (Set EffVarKey)
  deriving (Show)

instance Arbitrary Ctx where
  arbitrary = Ctx . Set.fromList <$> listOf genKey

newtype Subst = Subst EffSubst
  deriving (Show)

instance Arbitrary Subst where
  arbitrary = Subst . Map.fromList <$> listOf ((,) <$> genKey <*> (genEffect 2))

genLeaf :: Gen Effect
genLeaf =
  frequency
    [ (2, pure EffNone)
    , (3, EffStateChange <$> elements ["x", "y"])
    , (1, EffEvent <$> pure (EventLabel "timeout" []))
    , (4, effVarKeyEffect <$> genKey)
    ]

genEffect :: Int -> Gen Effect
genEffect n
  | n <= 0 = genLeaf
  | otherwise =
      frequency
        [ (3, genLeaf)
        , (1, EffAfter (Time 1 Renders) <$> sub)
        , (2, mkEffSeq <$> (choose (2, 3) >>= flip vectorOf sub))
        , (2, EffBranch <$> sub <*> sub)
        , (1, EffAlways (EventLabel "click" ["#doc"]) <$> sub)
        ]
  where
    sub = genEffect (n - 1)

genType :: Int -> Gen Type
genType n
  | n <= 0 = elements [TInt, TUnit, TBool]
  | otherwise =
      frequency
        [ (1, elements [TInt, TUnit, TBool])
        , (1, TPair <$> sub <*> sub)
        , (4, TArrow <$> genBinders <*> sub <*> sub <*> genEffect 2)
        ]
  where
    sub = genType (n - 1)
    genBinders = frequency [(2, pure []), (3, sublistOf writtenNames)]

-- | An arrow with at least one binder.
genSchema :: Gen Type
genSchema = do
  vs <- sublistOf writtenNames `suchThat` (not . null)
  TArrow vs <$> genType 2 <*> genType 2 <*> genEffect 2

binders :: Type -> [EffVarName]
binders (TArrow vs _ _ _) = vs
binders _ = []

shrinkEffect :: Effect -> [Effect]
shrinkEffect eff = case eff of
  EffNone -> []
  EffAfter d e -> e : (EffAfter d <$> shrinkEffect e)
  EffSeq es -> es <> (mkEffSeq <$> shrinkList shrinkEffect es)
  EffBranch a b -> [a, b] <> [EffBranch a' b | a' <- shrinkEffect a] <> [EffBranch a b' | b' <- shrinkEffect b]
  EffAlways l e -> e : (EffAlways l <$> shrinkEffect e)
  _ -> [EffNone]

shrinkType :: Type -> [Type]
shrinkType ty = case ty of
  TArrow vs a r e ->
    [a, r]
      <> [TArrow vs' a r e | vs' <- shrinkList (const []) vs]
      <> [TArrow vs a' r e | a' <- shrinkType a]
      <> [TArrow vs a r' e | r' <- shrinkType r]
      <> [TArrow vs a r e' | e' <- shrinkEffect e]
  TPair a b -> [a, b] <> [TPair a' b | a' <- shrinkType a] <> [TPair a b' | b' <- shrinkType b]
  _ -> []
