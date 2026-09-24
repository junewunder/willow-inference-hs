{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module InferTyEffect
  ( inferTyEffProgram
  , inferTyEffProgramTEST
  , inferTyEffProgramWithEventsTEST
  , buildSigmaE
  , lookupEventPayload
  , module InferenceMonad
  , EffSubst
  , substEffect
  , substType
  , instantiateSchema
  , unifyEffect
  , unifyType
  , generalizeEffect
  , freeEffVarsEffect
  , freeEffVarsType
  , writtenNamesType
  , enforcePureStateDefault
  , enforcePureLetRHS
  ) where

import Import
import Prettyprinter
import Data.Functor.Foldable (cata, Recursive(..))
import Control.Comonad.Cofree (Cofree (..))
import InferenceMonad
import Builtins (removeLibFns, tyLibraryFunctions)
import ErrorDisplay (handleInferenceError)
import Analysis.Common (subEffect)

import Control.Monad.Trans.Except (catchE)
import qualified Control.Comonad.Trans.Cofree as CFT
import qualified RIO.List as List
import qualified RIO.Map as Map
import qualified RIO.Set as Set
import qualified RIO.Text as Text

type TyEnv = Map Text Type

-- | Fold top-level @event ℓ⟨v⟩ : τ;@ declarations into the event signature
-- Σ_E. Duplicate event declarations are a type error.
buildSigmaE :: [AnnotatedEventDecl] -> InferenceM SigmaE
buildSigmaE = fmap SigmaE . foldM step Map.empty
  where
    step m (_ :< EventDeclF lbl ty)
      | Map.member lbl m = fail $ "Duplicate event declaration: " <> show (pretty lbl)
      | otherwise = return (Map.insert lbl ty m)

-- | Strict Σ_E lookup: using an undeclared event label in
-- bind/once/cancel/remove is a type error.
lookupEventPayload :: SigmaE -> EventLabel -> InferenceM Type
lookupEventPayload (SigmaE m) lbl = case Map.lookup lbl m of
  Just ty -> return ty
  Nothing -> fail $ "Unknown event label: " <> show (pretty lbl)

-- | Test entry for programs WITHOUT event declarations (empty Σ_E).
inferTyEffProgramTEST :: Sigma -> [Component] -> InferenceM (Sigma, [([AnnotatedDeclaration], AnnotatedNode)])
inferTyEffProgramTEST sigma = inferTyEffProgramM sigma emptySigmaE

-- | Test entry for programs WITH event declarations (the paper harness).
inferTyEffProgramWithEventsTEST :: Sigma -> SigmaE -> [Component] -> InferenceM (Sigma, [([AnnotatedDeclaration], AnnotatedNode)])
inferTyEffProgramWithEventsTEST = inferTyEffProgramM

-- | Pure InferenceM version for type+effect inference (for tests and internal use)
inferTyEffProgramM :: Sigma -> SigmaE -> [Component] -> InferenceM (Sigma, [([AnnotatedDeclaration], AnnotatedNode)])
inferTyEffProgramM sigma0 sigmaE comps = go sigma0 comps []
  where
    go sigma [] acc = return (sigma, reverse acc)
    go sigma (c : cs) acc = do
      (result, sigma') <- inferTyEffComponentM sigma sigmaE c
      go sigma' cs (result : acc)

-- | RIO wrapper for type+effect inference (for app use)
inferTyEffProgram :: Sigma -> AnnotatedProgram -> RIO RIOApp (Sigma, [([AnnotatedDeclaration], AnnotatedNode)])
inferTyEffProgram sigma prog@(SourceAnnotation s :< _) = do
  options <- appOptions <$> ask
  let inputFile = optionsInputFile options
  progStr <- case inputFile of
    Just file -> liftIO $ readFileUtf8 file
    Nothing -> pure ""
  let comps = getComponents prog
      eventDecls = getEventDecls prog
  result <- runInferenceWithContext (Just s) progStr (do
    sigmaE <- buildSigmaE eventDecls
    inferTyEffProgramM sigma sigmaE comps)
  case result of
    Left err -> do
      -- The diagnostic is rendered here, where the source text is in hand, and
      -- then the error itself is rethrown: callers catch 'InferenceError' to
      -- tell "the program does not check" from "the checker fell over", and a
      -- 'throwString' in its place would make every type error look internal.
      handleInferenceError progStr err
      throwIO err
    Right val -> return val

-- | Context-aware component inference
inferTyEffComponentM :: Sigma -> SigmaE -> Component -> InferenceM (([AnnotatedDeclaration], AnnotatedNode), Sigma)
inferTyEffComponentM sigma sigmaE compNode@(_ :< ComponentF name effParams args decls ret retSchema) = do
  let span = getComponentSpan compNode
      componentText = Text.pack $ "Component " <> Text.unpack name
  withSourceContext (Just span) componentText $ do
    let env0 = Map.union (Map.fromList args) tyLibraryFunctions
        effEnv0 = Delta (Map.fromList (List.map (\(x, _) -> (x, DeltaEntry [] EffNone)) args))
        -- The component's declared effect parameters are bound by @comp C<F>@,
        -- so they belong to the context even where no argument type mentions
        -- them: generalisation must not quantify them.
        scope = Set.fromList (map Written effParams)
        -- What a λ-parameter annotation may refer to rigidly: the declared
        -- parameters and the variables the argument types mention, which the
        -- component treats as parameters too (see 'DeclSubCompF').
        scoped = Set.fromList effParams
          <> Set.fromList [v | (_, t) <- args, Written v <- toList (freeEffVarsType t)]
    (env1, effEnv1, tdecls) <- local (\ctx -> ctx {scopedEffVars = scoped}) $
      inferTyEffDeclsM sigma sigmaE scope env0 effEnv0 decls
    -- Find the source location for the return variable from its declaration
    let findRetVarLocation :: Text -> [Declaration] -> Maybe SourceAnnotation
        findRetVarLocation _ [] = Nothing
        findRetVarLocation varName ((sAnnot :< DeclLetF declVar _ _) : rest)
          | declVar == varName = Just sAnnot
          | otherwise = findRetVarLocation varName rest
        findRetVarLocation varName (_ : rest) = findRetVarLocation varName rest

        retVarAnnotation = findRetVarLocation ret decls
        retVarNode = case retVarAnnotation of
          Just sAnnot -> let nAnnot = NodeAnnotation (annSourceSpan sAnnot) TUnit EffNone
                         in nAnnot :< LangFExpr (EVarF ret)
          Nothing -> mkVar Nothing ret

    tret <- inferTyEffExprTypedM sigmaE env1 effEnv1 retVarNode
    let actualRetSchema = getType tret
    -- Use the source context from the return variable for better error reporting
    _ <- case retVarAnnotation of
      Just sAnnot ->
        withSourceContext (Just (annSourceSpan sAnnot)) (Text.pack $ "Return type of " <> Text.unpack name) $
          unifyType retSchema actualRetSchema
      Nothing ->
        withSourceContext (Just span) (Text.pack $ "Return type of " <> Text.unpack name) $
          unifyType retSchema actualRetSchema
    let newEntry = SigmaEntry (mkComponent name effParams args tdecls ret retSchema) effEnv1
        sigma' = case sigma of Sigma m -> Sigma (Map.insert name newEntry m)
    pure ((tdecls, tret), sigma')

-- | Context-aware declaration list inference
inferTyEffDeclsM :: Sigma -> SigmaE -> Set EffVarKey -> TyEnv -> Delta -> [Declaration] -> InferenceM (TyEnv, Delta, [AnnotatedDeclaration])
inferTyEffDeclsM _ _ _ tyEnv delta [] = return (tyEnv, delta, [])
inferTyEffDeclsM sigma sigmaE scope tyEnv delta (d : ds) = do
  (tyEnv', delta', texpr) <- inferTyEffDeclM sigma sigmaE scope tyEnv delta d
  (tyEnv'', delta'', texprs) <- inferTyEffDeclsM sigma sigmaE scope tyEnv' delta' ds
  return (tyEnv'', delta'', texpr : texprs)

-- | Enforce the paper's purity premises
-- — T-STATE-DECL's @Γ ⊢ e : τ ∣ ·@ on the default expression and
-- T-LET-DECL's on the right-hand side — as REJECTIONS.
--
-- @subEffect F EffNone@ on the RAW inferred effect is the right purity
-- predicate (NOT structural equality, NOT 'simplifyEffect'):
--
--   * SE-EQ accepts @EffNone@ itself;
--   * SE-PLUS-L accepts @EffBranch EffNone EffNone@ — a pure ternary's
--     effect, which the impl never simplifies to @·@ (the @· + ·@ gotcha),
--     so a structural equality check would falsely reject it. @· + · ≤ ·@
--     holds because BOTH arms are @≤ ·@; a ternary with an impure arm
--     (e.g. @○¹ʳ\@x + ·@) is rejected, because @+@ is a join and the
--     impure arm is not below @·@;
--   * SE-ZERO-L accepts grade-0 delays of pure effects (@○⁰ F ≤ F@).
--
-- An effect variable (@EffVar@ or @EffUnif@) is SE-EQ-only, so an
-- effect-variable RHS is conservatively REJECTED: it may instantiate to an impure effect, and the paper has no
-- effect polymorphism. NEVER route this through 'simplifyEffect': its
-- @isCompilerVar → ·@ clause is an analysis-view shortcut that would wrongly
-- ACCEPT effects.
--
-- Placement contract: call these IMMEDIATELY after the RHS is inferred,
-- BEFORE env/effEnv updates and BEFORE 'unifyType' against an annotation, so
-- genuine RHS inference errors (unknown event label, type mismatch) thrown
-- inside 'inferTyEffExprTypedM' keep precedence over the purity check.

-- | T-STATE-DECL purity premise: reject an impure state default.
enforcePureStateDefault :: Text -> Effect -> InferenceM ()
enforcePureStateDefault var eff =
  unless (subEffect eff EffNone) $
    fail $ "Impure state default for '" <> Text.unpack var
        <> "': T-STATE-DECL requires Gamma |- e : tau | . , but the default expression has effect "
        <> show (pretty eff)

-- | T-LET-DECL purity premise: reject an impure let right-hand side.
enforcePureLetRHS :: Text -> Effect -> InferenceM ()
enforcePureLetRHS var eff =
  unless (subEffect eff EffNone) $
    fail $ "Impure let right-hand side for '" <> Text.unpack var
        <> "': T-LET-DECL requires Gamma |- e : tau | . , but the bound expression has effect "
        <> show (pretty eff)

-- | Context-aware declaration inference. @scope@ holds the component's
-- declared effect parameters, which are part of the context for
-- generalisation (see 'contextFreeVars').
inferTyEffDeclM :: Sigma -> SigmaE -> Set EffVarKey -> TyEnv -> Delta -> Declaration -> InferenceM (TyEnv, Delta, AnnotatedDeclaration)
inferTyEffDeclM (Sigma sigma) sigmaE scope tyEnv effEnv declNode@(_ :< declF) = do
  let span = getDeclarationSpan declNode
      declText = Text.pack (show (pretty declNode))
  withSourceContext (Just span) declText $ case declF of
    DeclStateF var setter expr -> do
      texpr <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-STATE-DECL purity premise: the default must be pure.
      enforcePureStateDefault var (getEffect texpr)
      let ty = getType texpr
          setterTy = TArrow [] (TArrow [] ty ty EffNone) TUnit (EffAfter (Time 1 Renders) (EffStateChange var))
          env' = Map.insert var ty $ Map.insert setter setterTy tyEnv
          effEnv' = Delta (Map.insert var (DeltaEntry [] EffNone) (unDelta effEnv))
      pure (env', effEnv', SourceAnnotation span :< DeclStateF var setter texpr)
    DeclEffectF deps (Block exprs) -> do
      -- T-ON-DECL: each watched name must have a Δ entry. Without this
      -- check an unknown name is skipped by the update below and the block's
      -- effect is lost.
      forM_ deps $ \x -> unless (Map.member x (unDelta effEnv)) $
        fail $ if Map.member x tyEnv
          then "Cannot watch " <> Text.unpack x <> " in `on`: it is not an argument, state variable, let or instance"
          else "Variable not in scope: " <> Text.unpack x
      texprs <- mapM (inferTyEffExprTypedM sigmaE tyEnv effEnv) exprs
      let blockEffects = map getEffect texprs
          combinedEffect = seqMany blockEffects
          f casc x = Map.update (\(DeltaEntry d e) -> Just $ DeltaEntry d (effSeq e combinedEffect)) x casc
          effEnv' = List.foldl f (unDelta effEnv) deps
      pure (tyEnv, Delta effEnv', SourceAnnotation span :< DeclEffectF deps (Block texprs))
    -- Both kinds of let are generalised, as in Hindley–Milner: the purity
    -- premise already makes the right-hand side a value-like expression, so
    -- no value restriction is needed.
    DeclLetF var (Just sch) expr -> do
      texpr <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-LET-DECL purity premise: before env/effEnv updates AND
      -- before the check against the annotation (see the placement contract
      -- on 'enforcePureStateDefault').
      enforcePureLetRHS var (getEffect texpr)
      let ctx = contextFreeVars scope tyEnv
          inferred = generalizeEffect ctx (getType texpr)
      checkAnnotation var ctx sch inferred
      -- The declared type is the binding's type.
      let env' = Map.insert var sch tyEnv
          deps = toList $ freeVars expr
          newEntry = DeltaEntry deps EffNone
          effEnv' = Delta (Map.insert var newEntry (unDelta effEnv))
      pure (env', effEnv', SourceAnnotation span :< DeclLetF var (Just sch) texpr)
    DeclLetF var Nothing expr -> do
      texpr <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-LET-DECL purity premise.
      enforcePureLetRHS var (getEffect texpr)
      let ty = generalizeEffect (contextFreeVars scope tyEnv) (getType texpr)
          env' = Map.insert var ty tyEnv
          deps = toList $ freeVars expr
          newEntry = DeltaEntry deps EffNone
          effEnv' = Delta (Map.insert var newEntry (unDelta effEnv))
      pure (env', effEnv', SourceAnnotation span :< DeclLetF var Nothing texpr)
    (DeclSubCompF instName compName effAnnots argNames) -> do
      case Map.lookup compName sigma of
        Just (SigmaEntry (_ :< subComp) (Delta subCompDelta0)) -> do
          let ComponentF {compFArgs = args0, compFReturn = retName, compFReturnType = retTy0, compFEffectParams = effParams} = subComp

          -- Rename the component's effect variables apart, as instantiating
          -- a schema does: a component is closed, so every effect variable
          -- free in its interface (its declared parameters, and whatever its
          -- argument types, return type and Δ mention) is quantified, and
          -- each instance gets fresh unification variables for them.
          let interfaceVars = Set.unions
                [ Set.fromList (map Written effParams)
                , Set.unions (map (freeEffVarsType . snd) args0)
                , freeEffVarsType retTy0
                , Set.unions [freeEffVarsEffect e | DeltaEntry _ e <- Map.elems subCompDelta0]
                ]
          renaming <- Map.fromList <$> mapM (\k -> (\n -> (k, EffUnif n)) <$> freshUnifVar) (toList interfaceVars)
          let args = [(n, substType renaming t) | (n, t) <- args0]
              retTy = substType renaming retTy0
              subCompDelta = Map.map (substDeltaEntry renaming) subCompDelta0
              effParams' = map (\p -> Map.findWithDefault (EffVar p) (Written p) renaming) effParams

          -- Validate and build substitutions
          validateArgumentCount args compName
          effSubst <- buildEffectSubstitution effParams'
          unificationSubst <- validateArgumentTypes args tyEnv effSubst
          let finalSubst = Map.union unificationSubst effSubst

          -- Apply substitutions and build environment
          let env' = buildTypeEnvironment retTy args tyEnv
              effEnv' = buildEffectEnvironment retName args subCompDelta effEnv
              env'' = Map.map (substType finalSubst) env'
              effEnv'' = Map.map (substDeltaEntry finalSubst) effEnv'

          return (env'', Delta effEnv'', SourceAnnotation span :< declF)
        _ -> fail $ "Component " <> Text.unpack compName <> " not found in environment"
      where
        validateArgumentCount args compName =
          when (length args /= length argNames) $
            fail $ "Component " <> Text.unpack compName <> " expects " <> show (length args) <> " arguments, got " <> show (length argNames)

        buildEffectSubstitution effParams = do
          let effsList = fromMaybe (replicate (length effParams) Nothing) effAnnots
          return $ Map.fromList [(Unif u, effVal) | (EffUnif u, Just effVal) <- zip effParams effsList]

        validateArgumentTypes args env effSubst = do
          let argPairs = zip argNames (map snd args)
          foldM validateSingleArgument Map.empty argPairs
          where
            validateSingleArgument subst (argName, expectedTy) =
              case Map.lookup argName env of
                Just actualSch -> do
                  -- An argument is an occurrence of a variable, so its type
                  -- is instantiated as at 'EVarF' — unless the parameter
                  -- is itself a schema, which the argument's schema must
                  -- then match up to renaming (see 'unifyType').
                  actualTy <- case expectedTy of
                    TArrow (_ : _) _ _ _ -> pure actualSch
                    _ -> instantiateSchema actualSch
                  let expectedTy' = substType effSubst (substType subst expectedTy)
                  s <- unifyType expectedTy' actualTy
                  return (Map.union subst s)
                Nothing ->
                  fail $ "Argument " <> Text.unpack argName <> " not in scope for subcomponent " <> Text.unpack instName

        substDeltaEntry subst (DeltaEntry deps eff) = DeltaEntry deps (substEffect subst eff)

        buildTypeEnvironment retTy args env =
          let retTy' = prefixStateChangeVarsTy instName retTy
              envWithInst = Map.insert instName retTy' env
              renamedArgs = [(prefixName n, prefixStateChangeVarsTy instName t) | (n, t) <- args]
          in List.foldl' (\e (n, t) -> Map.insert n t e) envWithInst renamedArgs

        buildEffectEnvironment retName args' subCompDelta' effEnv =
          let renamedDelta = renameComponentDelta subCompDelta'
              baseEffEnv = Map.unions [unDelta effEnv, renamedDelta]
              withArgs = addArgumentEffects args' baseEffEnv
              withReturn = addReturnEffect retName withArgs
          in withReturn

        addArgumentEffects args' effEnv =
          let argPairs = zip argNames (map (prefixName . fst) args')
              updateArg effEnv' (localName, hiddenName) =
                Map.update (\(DeltaEntry deps eff) ->
                  Just (DeltaEntry deps (effSeq eff (EffStateChange hiddenName)))) localName effEnv'
          in List.foldl updateArg effEnv argPairs

        addReturnEffect retName effEnv =
          let compRetName = prefixName retName
              newEntry = DeltaEntry [compRetName] EffNone
          in Map.insert instName newEntry effEnv

        renameComponentDelta subCompDelta' =
          Map.mapKeys prefixName (Map.map renameDeltaEntry subCompDelta')

        renameDeltaEntry (DeltaEntry deps eff) =
          DeltaEntry (map prefixName deps) (prefixStateChangeVars instName eff)

        prefixName name = instName <> Text.pack "." <> name

-- | Context-aware inference for expressions
inferTyEffExprTypedM :: SigmaE -> TyEnv -> Delta -> AnnotatedNode -> InferenceM AnnotatedNode
inferTyEffExprTypedM sigmaE env effEnv inputNode@(_ :< langF) = do
  -- Update context with current node information
  let span = getNodeSpan inputNode
      exprText = Text.pack (show (pretty inputNode))
  withSourceContext (Just span) exprText $ case langF of
    LangFExpr exprF -> case exprF of
      EVarF x ->
        case Map.lookup x env of
          Just ty -> do
            instantiatedTy <- instantiateSchema ty
            return $ NodeAnnotation span instantiatedTy EffNone :< LangFExpr (EVarF x)
          Nothing -> fail $ "Variable not in scope: " <> Text.unpack x
      ELitIntF n -> return $ mkSimpleTypedExpr span TInt (ELitIntF n)
      ELitStringF s -> return $ mkSimpleTypedExpr span TString (ELitStringF s)
      ELitBoolF b -> return $ mkSimpleTypedExpr span TBool (ELitBoolF b)
      EJSXNodeF node -> do
        tnode <- inferTyEffJSXNodeTypedM sigmaE env effEnv node
        return $ mkTypedExpr span THtml (getEffect tnode) (EJSXNodeF tnode)
      EArrowF vs param mTy body -> do
        paramTy <- maybe (pure TAny) flexibleParamAnnotation mTy
        let env' = Map.insert param paramTy env
        tbody <- inferTyEffExprTypedM sigmaE env' effEnv body
        let bodyTy = getType tbody
            bodyEff = getEffect tbody
        return $ mkSimpleTypedExpr span
          (TArrow vs paramTy (ensureMono bodyTy) bodyEff)
          (EArrowF vs param mTy tbody)

      EAppF f x -> do
        tf <- inferTyEffExprTypedM sigmaE env effEnv f
        let tfSch = getType tf
        let tfEff = getEffect tf
        tfTy <- case tfSch of
              TArrow {} -> instantiateSchema tfSch
              _ -> fail ""
        case tfTy of
          TArrow _ argTy retTy callEff -> do
            tx <- inferTyEffExprTypedWithExpectedM sigmaE env effEnv (Just argTy) x
            let txSch = getType tx
                txTy = txSch
                txEff = getEffect tx
            subst <- unifyType argTy txTy
            let retTy' = substType subst retTy
                callEff' = substEffect subst callEff
                appEff = tfEff `effSeq` txEff `effSeq` callEff'
            return $ mkTypedExpr span retTy' appEff (EAppF tf tx)
          _ -> fail "Type error: applying non-function"
      EIfF cond bThen bElse -> do
        tCond <- inferTyEffExprTypedM sigmaE env effEnv cond
        tThen <- inferTyEffExprTypedM sigmaE env effEnv bThen
        tElse <- inferTyEffExprTypedM sigmaE env effEnv bElse
        condSubst <- unifyType TBool (getType tCond)
        branchSubst <- unifyType (getType tThen) (getType tElse)
        let finalSubst = Map.union condSubst branchSubst
            resultSch = substType finalSubst (getType tThen)
            condEff' = substEffect finalSubst (getEffect tCond)
            thenEff' = substEffect finalSubst (getEffect tThen)
            elseEff' = substEffect finalSubst (getEffect tElse)
            eff = effSeq condEff' (EffBranch thenEff' elseEff')
        return $ mkTypedExpr span resultSch eff (EIfF tCond tThen tElse)
      EEffectF eff -> return $ mkTypedExpr span TUnit eff (EEffectF eff)
      EPairF e1 e2 -> do
        te1 <- inferTyEffExprTypedM sigmaE env effEnv e1
        te2 <- inferTyEffExprTypedM sigmaE env effEnv e2
        let eff = effSeq (getEffect te1) (getEffect te2)
        let pairTy = TPair (getType te1) (getType te2)
        return $ mkTypedExpr span pairTy eff (EPairF te1 te2)
      EPairAccessF e ix -> do
        te <- inferTyEffExprTypedM sigmaE env effEnv e
        case getType te of
          TPair t0 t1 ->
            let resultTy = if ix == 0 then t0 else t1
            in return $ mkTypedExpr span resultTy (getEffect te) (EPairAccessF te ix)
          _ -> fail "Type error: pair access on non-pair"
      -- T-CANCEL (paper TY CANCEL): cancel ℓ⟨v⟩ : unit ∣ ⊘ℓ⟨v⟩. Strict: the
      -- label must be declared in Σ_E.
      ECancelF lbl -> do
        _ <- lookupEventPayload sigmaE lbl
        return $ mkTypedExpr span TUnit (EffCancel lbl) (ECancelF lbl)
      -- T-REMOVE (paper TY REMOVE): remove ℓ⟨v⟩ : unit ∣ ✗ℓ⟨v⟩.
      ERemoveF lbl -> do
        _ <- lookupEventPayload sigmaE lbl
        return $ mkTypedExpr span TUnit (EffRemove lbl) (ERemoveF lbl)
      -- T-BIND (paper TY BIND): bind ℓ⟨v⟩ e : unit ∣ F_e * □ℓ⟨v⟩(F), where the
      -- handler e must be a closure (τ → unit | F) with τ = Σ_E(ℓ⟨v⟩).
      EBindF lbl e -> do
        payload <- lookupEventPayload sigmaE lbl
        -- WithExpected pushes the payload type into UNANNOTATED inline lambdas
        -- (EArrowF defaults param to TAny otherwise, which would satisfy the
        -- paper's τ = Σ_E(ℓ⟨v⟩) premise vacuously); annotated handlers fall
        -- through to plain inference. Mirrors EAppF's argument discipline.
        te <- inferTyEffExprTypedWithExpectedM sigmaE env effEnv (Just (TArrow [] payload TUnit EffNone)) e
        -- Mirror EAppF's instantiation discipline: instantiate schemas.
        teFnTy <- case getType te of
          sch@(TArrow {}) -> instantiateSchema sch
          _ -> fail "bind expects a function (τ → unit | F)"
        case teFnTy of
          TArrow _ argTy retTy latent -> do
            sArg <- unifyType argTy payload
            sRet <- unifyType retTy TUnit
            let subst = Map.union sArg sRet
                eff = effSeq (substEffect subst (getEffect te)) (EffAlways lbl (substEffect subst latent))
            return $ mkTypedExpr span TUnit eff (EBindF lbl te)
          _ -> fail "bind expects a function (τ → unit | F)"
      -- T-ONCE (paper TY ONCE): as T-BIND, but a one-shot listener → ◇ℓ⟨v⟩(F).
      EOnceF lbl e -> do
        payload <- lookupEventPayload sigmaE lbl
        -- See EBindF: WithExpected so unannotated handlers receive the payload type.
        te <- inferTyEffExprTypedWithExpectedM sigmaE env effEnv (Just (TArrow [] payload TUnit EffNone)) e
        teFnTy <- case getType te of
          sch@(TArrow {}) -> instantiateSchema sch
          _ -> fail "once expects a function (τ → unit | F)"
        case teFnTy of
          TArrow _ argTy retTy latent -> do
            sArg <- unifyType argTy payload
            sRet <- unifyType retTy TUnit
            let subst = Map.union sArg sRet
                eff = effSeq (substEffect subst (getEffect te)) (EffEventually lbl (substEffect subst latent))
            return $ mkTypedExpr span TUnit eff (EOnceF lbl te)
          _ -> fail "once expects a function (τ → unit | F)"
    -- JSX has one inference path, in 'inferTyEffJSXNodeTypedM'. Do not inline a
    -- second copy here: the effect a node propagates is what T-LET-DECL's
    -- purity premise checks, and two copies drift.
    LangFJSXNode _ -> inferTyEffJSXNodeTypedM sigmaE env effEnv inputNode
    LangFJSXChild _ -> inferTyEffJSXNodeTypedM sigmaE env effEnv inputNode

-- | Type inference for JSX attributes, handling expressions in attribute values
inferTyEffJSXAttrsM :: SigmaE -> TyEnv -> Delta -> [JSXAttr] -> InferenceM [JSXAttr]
inferTyEffJSXAttrsM sigmaE env effEnv = mapM (inferTyEffJSXAttrM sigmaE env effEnv)

-- | Type inference for a single JSX attribute
inferTyEffJSXAttrM :: SigmaE -> TyEnv -> Delta -> JSXAttr -> InferenceM JSXAttr
inferTyEffJSXAttrM sigmaE env effEnv (JSXAttr (name, value)) = case value of
  JSXAttrString text -> return $ JSXAttr (name, JSXAttrString text)
  -- A JSX attribute is an ordinary expression: listeners are registered with
  -- @bind@/@once@, never by an attribute, so no attribute name is special.
  JSXAttrExpr expr -> do
    typedExpr <- inferTyEffExprTypedM sigmaE env effEnv expr
    return $ JSXAttr (name, JSXAttrExpr typedExpr)

-- | Context-aware inference for expressions with expected type
inferTyEffExprTypedWithExpectedM :: SigmaE -> TyEnv -> Delta -> Maybe Type -> AnnotatedNode -> InferenceM AnnotatedNode
inferTyEffExprTypedWithExpectedM sigmaE env effEnv mExpected inputNode@(_ :< langF) =
  let span = getNodeSpan inputNode
      exprText = Text.pack (show (pretty inputNode))
  in withSourceContext (Just span) exprText $ case langF of
    LangFExpr (EArrowF vs param Nothing body) -> case mExpected of
      Just (TArrow vs' argTy _ _) | length vs == length vs' -> do
        let env' = Map.insert param argTy env
        tbody <- inferTyEffExprTypedM sigmaE env' effEnv body
        let bodyTy = getType tbody
        let bodyEff = getEffect tbody
        return $ mkSimpleTypedExpr span (TArrow vs argTy (ensureMono bodyTy) bodyEff) (EArrowF vs param Nothing tbody)
      _ ->
        -- Fallback to regular inference if no expected type or wrong expected type
        inferTyEffExprTypedM sigmaE env effEnv inputNode
    _ ->
      -- For all other expressions, use regular inference
      inferTyEffExprTypedM sigmaE env effEnv inputNode

-- | Context-aware JSX node inference
--
-- A node's effect is the sequence of its attributes' and children's effects, in
-- source order. Rendering itself does nothing, so that effect is @·@ for every
-- well-written program — but it must be PROPAGATED rather than discarded, since
-- all JSX in a Willow component is either bound by a @let@ or returned (and
-- @return e@ desugars to @let returnVar = e@). T-LET-DECL's purity premise is
-- therefore what rejects an effectful expression inside JSX, and it can only do
-- that if the effect reaches it.
inferTyEffJSXNodeTypedM :: SigmaE -> TyEnv -> Delta -> AnnotatedNode -> InferenceM AnnotatedNode
inferTyEffJSXNodeTypedM sigmaE env effEnv node@(_ :< langF) = do
  let span = getNodeSpan node
      typedNode eff = (NodeAnnotation span THtml eff :<)
  withSourceContext (Just span) (Text.pack $ show $ pretty node) $ case langF of
    LangFJSXNode jsxF -> case jsxF of
      JSXElementNodeF tag attrs children -> do
        tChildren <- mapM (inferTyEffExprTypedM sigmaE env effEnv) children
        tAttrs <- inferTyEffJSXAttrsM sigmaE env effEnv attrs
        let eff = seqMany (jsxAttrEffects tAttrs ++ map getEffect tChildren)
        return $ typedNode eff (LangFJSXNode (JSXElementNodeF tag tAttrs tChildren))
      JSXSelfClosingNodeF tag attrs -> do
        tAttrs <- inferTyEffJSXAttrsM sigmaE env effEnv attrs
        let eff = seqMany (jsxAttrEffects tAttrs)
        return $ typedNode eff (LangFJSXNode (JSXSelfClosingNodeF tag tAttrs))
    LangFJSXChild childF -> case childF of
      ChildTextF text ->
        return $ typedNode EffNone (LangFJSXChild (ChildTextF text))
      ChildExprF expr -> do
        texpr <- inferTyEffExprTypedM sigmaE env effEnv expr
        return $ typedNode (getEffect texpr) (LangFJSXChild (ChildExprF texpr))
      ChildNodeF childNode -> do
        tnode <- inferTyEffExprTypedM sigmaE env effEnv childNode
        return $ typedNode (getEffect tnode) (LangFJSXChild (ChildNodeF tnode))
    _ ->
      -- For non-JSX nodes, delegate to regular expression inference
      inferTyEffExprTypedM sigmaE env effEnv node

-- | The effects of a JSX element's attribute expressions. String-literal
-- attributes are inert.
jsxAttrEffects :: [JSXAttr] -> [Effect]
jsxAttrEffects attrs =
  [getEffect expr | JSXAttr (_, JSXAttrExpr expr) <- attrs]

-- | Compute the set of free variables in an AnnotatedNode expression using recursion-schemes.
freeVars :: AnnotatedNode -> Set Text
freeVars = Set.fromList . removeLibFns . toList . cata freeVarsAlg
  where
    freeVarsAlg (_ann CFT.:< langF) = case langF of
      LangFExpr exprF -> case exprF of
        EVarF x -> Set.singleton x
        EJSXNodeF node -> node
        EArrowF _ param _ body -> Set.delete param body
        EAppF f x -> f `Set.union` x
        EIfF cond t e -> cond `Set.union` t `Set.union` e
        EPairF e1 e2 -> e1 `Set.union` e2
        EPairAccessF e _ -> e
        EBindF _ e -> e
        EOnceF _ e -> e
        ECancelF _ -> Set.empty
        ERemoveF _ -> Set.empty
        _ -> Set.empty
      LangFJSXNode jsxF -> case jsxF of
        JSXElementNodeF _ attrs children ->
          Set.unions (map freeVarsJSXAttr attrs) `Set.union` Set.unions children
        JSXSelfClosingNodeF _ attrs ->
          Set.unions (map freeVarsJSXAttr attrs)
      LangFJSXChild childF -> case childF of
        ChildTextF _ -> Set.empty
        ChildExprF e -> e
        ChildNodeF n -> n
    freeVarsJSXAttr (JSXAttr (_, v)) = case v of
      JSXAttrString _ -> Set.empty
      JSXAttrExpr e -> freeVars e

ensureMono :: Type -> Type
ensureMono t@(TArrow [] _ _ _) = t
ensureMono t@(TArrow {}) = error $ "Expected monomorphic type, got schema: " ++ show t
ensureMono t = t

-- ---------------------------------------------------------------------------
-- Effect variables
--
-- There are two kinds, as in Hindley–Milner with rigid and flexible
-- variables. A written variable ('EffVar': a component's effect parameter, a
-- @forall@ binder, an effect variable in an annotation) is rigid: unification
-- never binds it. A unification variable ('EffUnif') is created by inference,
-- when a schema or a component instance is instantiated, and is the only kind
-- unification binds. The two cannot collide, whatever names a program uses.
--
-- Only written variables are bound by an arrow's binder list. Generalisation
-- turns the unification variables it quantifies into written, bound ones.
-- ---------------------------------------------------------------------------

-- | A substitution over effect variables of both kinds.
type EffSubst = Map EffVarKey Effect

-- | Substitute effect variables in an effect
substEffect :: EffSubst -> Effect -> Effect
substEffect subst eff = case eff of
  EffNone -> EffNone
  EffVar v -> Map.findWithDefault (EffVar v) (Written v) subst
  EffUnif n -> Map.findWithDefault (EffUnif n) (Unif n) subst
  EffSeq effs -> mkEffSeq (map (substEffect subst) effs)
  EffBranch e1 e2 -> EffBranch (substEffect subst e1) (substEffect subst e2)
  EffAfter d e -> EffAfter d (substEffect subst e)
  EffLoop n -> EffLoop n
  EffStateChange n -> EffStateChange n
  EffEvent lbl -> EffEvent lbl
  EffAlways lbl e -> EffAlways lbl (substEffect subst e)
  EffEventually lbl e -> EffEventually lbl (substEffect subst e)
  EffCancel lbl -> EffCancel lbl
  EffRemove lbl -> EffRemove lbl

-- | Draw a fresh unification variable from the counter in 'RIOApp'.
freshUnifVar :: InferenceM Int
freshUnifVar = do
  ref <- asksRIO appVarCounter
  liftIO $ atomicModifyIORef' ref (\x -> (x+1, x))

-- | Instantiate a schema: each binder becomes a fresh unification variable.
instantiateSchema :: Type -> InferenceM Type
instantiateSchema sch = go sch Map.empty
  where
    go t@(TArrow [] _ _ _) s =
      return (substType s t)
    go (TArrow (v:vs) i o e) s = do
      n <- freshUnifVar
      let s' = Map.insert (Written v) (EffUnif n) s
      go (TArrow vs i o e) s'
    go t s = return (substType s t)

-- | Substitute effect variables in a type (recursively). Capture-avoiding: a
-- variable bound by an arrow's binder list is not touched under that arrow,
-- and a binder that would capture a variable the substitution brings in is
-- renamed first.
substType :: EffSubst -> Type -> Type
substType s ty = case ty of
  TArrow vs t1 t2 eff ->
    let s' = List.foldl' (flip (Map.delete . Written)) s vs
        body = TArrow [] t1 t2 eff
        incoming = Set.unions
          [freeEffVarsEffect e | (k, e) <- Map.toList s', k `Set.member` freeEffVarsType body]
        clashing = [v | v <- vs, Written v `Set.member` incoming]
    in if null clashing
         then TArrow vs (substType s' t1) (substType s' t2) (substEffect s' eff)
         else
           let avoid = writtenNamesType ty <> Set.fromList [v | Written v <- toList incoming]
               fresh = freshNames avoid clashing
               rename = Map.fromList [(Written v, EffVar v') | (v, v') <- zip clashing fresh]
               vs' = [Map.findWithDefault v v (Map.fromList (zip clashing fresh)) | v <- vs]
           in substType s (TArrow vs' (substType rename t1) (substType rename t2) (substEffect rename eff))
  TPair t1 t2 -> TPair (substType s t1) (substType s t2)
  other -> other

-- | Names for new written variables, one per given base name, avoiding the
-- given set and each other. A base name is kept when it is free, and
-- otherwise gets the first numeric suffix that is.
freshNames :: Set EffVarName -> [EffVarName] -> [EffVarName]
freshNames _ [] = []
freshNames avoid (EffVarName b : bs) =
  let candidates = EffVarName b : [EffVarName (b <> Text.pack (show k)) | k <- [1 :: Int ..]]
      v = pick candidates
  in v : freshNames (Set.insert v avoid) bs
  where
    pick (c : cs) = if c `Set.member` avoid then pick cs else c
    pick [] = EffVarName b -- unreachable: the candidates are infinite

-- | Every written variable name in a type, free or bound, binders included.
writtenNamesType :: Type -> Set EffVarName
writtenNamesType ty = case ty of
  TArrow vs t1 t2 eff ->
    Set.unions [Set.fromList vs, writtenNamesType t1, writtenNamesType t2, writtenNamesEffect eff]
  TPair t1 t2 -> writtenNamesType t1 <> writtenNamesType t2
  _ -> Set.empty
  where
    writtenNamesEffect e = Set.fromList [v | Written v <- toList (freeEffVarsEffect e)]

-- | Unification for effects
-- | When relevant: Expected effect comes first then actual effect
--
-- Only a unification variable is bound. A written variable is rigid: it
-- unifies with itself, or with a unification variable, which is then bound
-- to it.
unifyEffect :: Effect -> Effect -> InferenceM EffSubst
unifyEffect e1 e2 = case (e1, e2) of
  (EffUnif u1, EffUnif u2) | u1 == u2 -> return Map.empty
  (EffUnif u, eff) -> return (Map.singleton (Unif u) eff)
  (eff, EffUnif u) -> return (Map.singleton (Unif u) eff)
  (EffVar v1, EffVar v2) | v1 == v2 -> return Map.empty
  (EffNone, EffNone) -> return Map.empty
  (EffSeq s1, EffSeq s2) | length s1 == length s2 ->
    foldM (\subst (a, b) -> do
      s <- unifyEffect (substEffect subst a) (substEffect subst b)
      return (Map.union subst s)) Map.empty (zip s1 s2)
  (eff, EffSeq s2) -> do
    case s2 of
      [] -> unifyEffect eff EffNone
      eff1 : rest -> do
        s1 <- unifyEffect eff eff1
        ss <- mapM (unifyEffect EffNone) rest
        return $ List.foldl Map.union s1 ss
  (EffSeq s2, eff) -> do
    case s2 of
      [] -> unifyEffect eff EffNone
      eff1 : rest -> do
        s1 <- unifyEffect eff eff1
        ss <- mapM (unifyEffect EffNone) rest
        return $ List.foldl Map.union s1 ss
  (EffBranch a1 b1, EffBranch a2 b2) -> do
    s1 <- unifyEffect a1 a2
    s2 <- unifyEffect (substEffect s1 b1) (substEffect s1 b2)
    return (Map.union s1 s2)
  (EffBranch a1 b1, eff) -> do
    s1 <- unifyEffect a1 eff
    s2 <- unifyEffect (substEffect s1 b1) (substEffect s1 eff)
    return (Map.union s1 s2)
  (eff, EffBranch a1 b1) -> do
    s1 <- unifyEffect a1 eff
    s2 <- unifyEffect (substEffect s1 b1) (substEffect s1 eff)
    return (Map.union s1 s2)
  (EffAfter d1 e1', EffAfter d2 e2') | d1 == d2 -> unifyEffect e1' e2'
  (EffLoop n1, EffLoop n2) | n1 == n2 -> return Map.empty
  (EffStateChange n1, EffStateChange n2) | n1 == n2 -> return Map.empty
  (EffEvent l1, EffEvent l2) | l1 == l2 -> return Map.empty
  (EffCancel l1, EffCancel l2) | l1 == l2 -> return Map.empty
  (EffRemove l1, EffRemove l2) | l1 == l2 -> return Map.empty
  (EffAlways l1 a1, EffAlways l2 a2) | l1 == l2 -> unifyEffect a1 a2
  (EffEventually l1 a1, EffEventually l2 a2) | l1 == l2 -> unifyEffect a1 a2
  _ -> fail $ "Cannot unify effects: " <> fromString (show (pretty e1)) <> " and " <> fromString (show (pretty e2))
         <> rigidNote
  where
    rigidNote
      | isWritten e1 || isWritten e2 =
          " (a written effect variable is rigid: it unifies only with itself or a unification variable)"
      | otherwise = ""
    isWritten (EffVar _) = True
    isWritten _ = False

-- | Strict unification for types (structure must match exactly, effects unified)
-- | Expected type comes first then actual type
--
-- Two schemas unify up to renaming of their binders: both binder lists are
-- renamed to the same fresh written variables, which are rigid, and a
-- binding that would let one escape its schema is rejected.
unifyType :: Type -> Type -> InferenceM EffSubst
unifyType t1 t2 = case (t1, t2) of
  (TAny, _) -> return Map.empty
  (_, TAny) -> return Map.empty
  (TInt, TInt) -> return Map.empty
  (TBool, TBool) -> return Map.empty
  (TString, TString) -> return Map.empty
  (TUnit, TUnit) -> return Map.empty
  (THtml, THtml) -> return Map.empty
  (TPair a1 b1, TPair a2 b2) -> do
    s1 <- unifyType a1 a2
    s2 <- unifyType (substType s1 b1) (substType s1 b2)
    return (Map.union s1 s2)
  (TArrow [] a1 r1 e1, TArrow [] a2 r2 e2) -> do
    s1 <- unifyType a1 a2
    s2 <- unifyType (substType s1 r1) (substType s1 r2)
    s3 <- unifyEffect (substEffect s2 (substEffect s1 e1)) (substEffect s2 (substEffect s1 e2))
    return (Map.unions [s1, s2, s3])
  (TArrow vs1 a1 r1 e1, TArrow vs2 a2 r2 e2) | length vs1 == length vs2 -> do
    let common = freshNames (writtenNamesType t1 <> writtenNamesType t2) vs1
        rename vs = Map.fromList (zip (map Written vs) (map EffVar common))
        TArrow _ a1' r1' e1' = substType (rename vs1) (TArrow [] a1 r1 e1)
        TArrow _ a2' r2' e2' = substType (rename vs2) (TArrow [] a2 r2 e2)
    s <- unifyType (TArrow [] a1' r1' e1') (TArrow [] a2' r2' e2')
    let escaping = [ v | e <- Map.elems s, Written v <- toList (freeEffVarsEffect e), v `elem` common ]
    unless (null escaping) $
      fail $ "Type mismatch: a bound effect variable would escape its schema"
        <> "\n  Expected " <> fromString (show (pretty t1))
        <> " \n  Actual   " <> fromString (show (pretty t2))
    return s
  _ -> fail $ "Type mismatch: \n  Expected " <> fromString (show (pretty t1)) <> " \n  Actual   " <> fromString (show (pretty t2))

-- | Collect all free effect variables in an Effect
freeEffVarsEffect :: Effect -> Set EffVarKey
freeEffVarsEffect eff = case eff of
  EffVar v -> Set.singleton (Written v)
  EffUnif n -> Set.singleton (Unif n)
  EffSeq effs -> Set.unions (map freeEffVarsEffect effs)
  EffBranch e1 e2 -> freeEffVarsEffect e1 `Set.union` freeEffVarsEffect e2
  EffAfter _ e -> freeEffVarsEffect e
  EffLoop _ -> Set.empty
  EffStateChange _ -> Set.empty
  EffNone -> Set.empty
  EffEvent _ -> Set.empty
  EffAlways _ e -> freeEffVarsEffect e
  EffEventually _ e -> freeEffVarsEffect e
  EffCancel _ -> Set.empty
  EffRemove _ -> Set.empty

-- | Collect all free effect variables in a Type
freeEffVarsType :: Type -> Set EffVarKey
freeEffVarsType ty = case ty of
  TArrow vs t1 t2 eff ->
    (freeEffVarsType t1 `Set.union` freeEffVarsType t2 `Set.union` freeEffVarsEffect eff)
      Set.\\ Set.fromList (map Written vs)
  TPair t1 t2 -> freeEffVarsType t1 `Set.union` freeEffVarsType t2
  _ -> Set.empty

-- | The effect variables free in the context: those of every type in Γ,
-- plus the component's declared effect parameters (@scope@).
contextFreeVars :: Set EffVarKey -> TyEnv -> Set EffVarKey
contextFreeVars scope env = Set.unions (scope : map freeEffVarsType (Map.elems env))

-- | Hindley–Milner generalisation, @gen(Γ, τ) = ∀(fev(τ) ∖ fev(Γ)). τ@, given
-- @fev(Γ)@. A written variable keeps its name as the binder. A unification
-- variable is replaced by a new written one (@e3@ for @?_e3@, renamed if
-- that name is taken), since binders bind written variables only. Only an
-- arrow carries binders, so any other type is returned unchanged.
generalizeEffect :: Set EffVarKey -> Type -> Type
generalizeEffect ctx ty@(TArrow vs i o e) =
  let quantified = toList (freeEffVarsType ty Set.\\ ctx)
      written = [v | Written v <- quantified]
      unifs = [n | Unif n <- quantified]
      names = freshNames (writtenNamesType ty) [EffVarName ("e" <> Text.pack (show n)) | n <- unifs]
      s = Map.fromList (zip (map Unif unifs) (map EffVar names))
      TArrow _ i' o' e' = substType s (TArrow [] i o e)
  in TArrow (vs ++ written ++ names) i' o' e'
generalizeEffect _ ty = ty

-- | Check an annotated @let x : σ = e@ in the Damas–Milner way: the
-- annotation must be an instance of the right-hand side's generalised type.
-- σ's binders are made rigid (renamed to written variables fresh for
-- everything in sight), the inferred schema is instantiated, and the two are
-- unified. A unification variable of the context may not be bound to one of
-- σ's binders, which would let it escape.
checkAnnotation :: Text -> Set EffVarKey -> Type -> Type -> InferenceM ()
checkAnnotation var ctx sch inferred = do
  let (skolems, annBody) = case sch of
        TArrow vs i o e ->
          let avoid = writtenNamesType sch <> writtenNamesType inferred
                <> Set.fromList [v | Written v <- toList ctx]
              sk = freshNames avoid vs
              rename = Map.fromList (zip (map Written vs) (map EffVar sk))
          in (sk, substType rename (TArrow [] i o e))
        _ -> ([], sch)
  actual <- instantiateSchema inferred
  s <- unifyType annBody actual `catchInference` \err ->
    fail $ "The definition of '" <> Text.unpack var <> "' does not have its annotated type"
      <> "\n  Annotation " <> show (pretty sch)
      <> "\n  Inferred   " <> show (pretty inferred)
      <> "\n  " <> Text.unpack (errorMessage err)
  let escaping = [ v | (k, e) <- Map.toList s, k `Set.member` ctx
                     , Written v <- toList (freeEffVarsEffect e), v `elem` skolems ]
  unless (null escaping) $
    fail $ "The annotation of '" <> Text.unpack var <> "' quantifies an effect variable that the context fixes"
      <> "\n  Annotation " <> show (pretty sch)
      <> "\n  Inferred   " <> show (pretty inferred)

-- | A λ-parameter annotation, as in OCaml's @fun (f : 'a -> unit) -> …@ or a
-- Haskell pattern signature: a written variable that no enclosing scope binds
-- stands for whatever effect it meets, so it becomes a fresh unification
-- variable for this λ (one per name, shared by its occurrences in the
-- annotation). Variables the component binds stay rigid, and a @forall@
-- inside the annotation keeps its own binders ('substType' skips them).
flexibleParamAnnotation :: Type -> InferenceM Type
flexibleParamAnnotation ty = do
  scoped <- asks scopedEffVars
  let unbound = [v | Written v <- toList (freeEffVarsType ty), v `Set.notMember` scoped]
  fresh <- mapM (\v -> (\n -> (Written v, EffUnif n)) <$> freshUnifVar) unbound
  pure (substType (Map.fromList fresh) ty)

-- | Recover from an inference failure.
catchInference :: InferenceM a -> (InferenceError -> InferenceM a) -> InferenceM a
catchInference (InferenceM m) handler = InferenceM (catchE m (runInferenceM . handler))
