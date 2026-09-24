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
  , substEffect
  , substType
  , instantiateSchema
  , unifyEffect
  , unifyType
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
    (env1, effEnv1, tdecls) <- inferTyEffDeclsM sigma sigmaE env0 effEnv0 decls
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
inferTyEffDeclsM :: Sigma -> SigmaE -> TyEnv -> Delta -> [Declaration] -> InferenceM (TyEnv, Delta, [AnnotatedDeclaration])
inferTyEffDeclsM _ _ tyEnv delta [] = return (tyEnv, delta, [])
inferTyEffDeclsM sigma sigmaE tyEnv delta (d : ds) = do
  (tyEnv', delta', texpr) <- inferTyEffDeclM sigma sigmaE tyEnv delta d
  (tyEnv'', delta'', texprs) <- inferTyEffDeclsM sigma sigmaE tyEnv' delta' ds
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
-- @EffVar@ is SE-EQ-only, so an effect-variable RHS is conservatively
-- REJECTED: it may instantiate to an impure effect, and the paper has no
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

-- | Context-aware declaration inference
inferTyEffDeclM :: Sigma -> SigmaE -> TyEnv -> Delta -> Declaration -> InferenceM (TyEnv, Delta, AnnotatedDeclaration)
inferTyEffDeclM (Sigma sigma) sigmaE tyEnv effEnv declNode@(_ :< declF) = do
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
      texprs <- mapM (inferTyEffExprTypedM sigmaE tyEnv effEnv) exprs
      let blockEffects = map getEffect texprs
          combinedEffect = seqMany blockEffects
          f casc x = Map.update (\(DeltaEntry d e) -> Just $ DeltaEntry d (effSeq e combinedEffect)) x casc
          effEnv' = List.foldl f (unDelta effEnv) deps
      pure (tyEnv, Delta effEnv', SourceAnnotation span :< DeclEffectF deps (Block texprs))
    DeclLetF var (Just sch) expr -> do
      texpr <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-LET-DECL purity premise: before env/effEnv updates AND
      -- before unifyType against the annotation (see the placement contract
      -- on 'enforcePureStateDefault').
      enforcePureLetRHS var (getEffect texpr)
      let ty = getType texpr
          ty' = generalizeEffect ty
          env' = Map.insert var ty' tyEnv
          deps = toList $ freeVars expr
          newEntry = DeltaEntry deps EffNone
          effEnv' = Delta (Map.insert var newEntry (unDelta effEnv))
      _ <- unifyType ty' sch
      pure (env', effEnv', SourceAnnotation span :< DeclLetF var (Just sch) texpr)
    DeclLetF var Nothing expr -> do
      texpr <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-LET-DECL purity premise.
      enforcePureLetRHS var (getEffect texpr)
      let ty = getType texpr
          env' = Map.insert var ty tyEnv
          deps = toList $ freeVars expr
          newEntry = DeltaEntry deps EffNone
          effEnv' = Delta (Map.insert var newEntry (unDelta effEnv))
      pure (env', effEnv', SourceAnnotation span :< DeclLetF var Nothing texpr)
    (DeclSubCompF instName compName effAnnots argNames) -> do
      case Map.lookup compName sigma of
        Just (SigmaEntry (_ :< subComp) (Delta subCompDelta)) -> do
          let ComponentF {compFArgs = args, compFReturn = retName, compFReturnType = retTy, compFEffectParams = effParams} = subComp

          -- Validate and build substitutions
          validateArgumentCount args compName
          effSubst <- buildEffectSubstitution effParams
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
          return $ Map.fromList [(effParam, effVal) | (effParam, Just effVal) <- zip effParams effsList]

        validateArgumentTypes args env effSubst = do
          let argPairs = zip argNames (map snd args)
          foldM validateSingleArgument Map.empty argPairs
          where
            validateSingleArgument subst (argName, expectedTy) =
              case Map.lookup argName env of
                Just actualTy -> do
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
        let paramTy = fromMaybe TAny mTy
            env' = Map.insert param paramTy env
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

-- | Substitute effect variables in an effect
type EffSubst = Map EffVarName Effect
substEffect :: EffSubst -> Effect -> Effect
substEffect subst eff = case eff of
  EffNone -> EffNone
  EffVar v -> Map.findWithDefault (EffVar v) v subst
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

-- | Generate a fresh, globally unique effect variable name using RIOApp state
freshEffVarName :: InferenceM EffVarName
freshEffVarName = do
  ref <- asksRIO appVarCounter
  n <- liftIO $ atomicModifyIORef' ref (\x -> (x+1, x))
  return $ EffVarName ("e" <> fromString (show n))

-- | Instantiate a schema by replacing effect variables with fresh, globally unique ones (RIO version)
instantiateSchema :: Type -> InferenceM Type
instantiateSchema sch = go sch Map.empty
  where
    go t@(TArrow [] _ _ _) s =
      return (substType s t)
    go (TArrow (v:vs) i o e) s = do
      freshVar <- freshEffVarName
      let s' = Map.insert v (EffVar freshVar) s
      go (TArrow vs i o e) s'
    go t s = return (substType s t)

-- | Substitute effect variables in a type (recursively)
substType :: EffSubst -> Type -> Type
substType s ty = case ty of
  TArrow vs t1 t2 eff -> TArrow vs (substType s t1) (substType s t2) (substEffect s eff)
  TPair t1 t2 -> TPair (substType s t1) (substType s t2)
  other -> other

-- | Unification for effects
-- | When relevant: Expected effect comes first then actual effect
unifyEffect :: Effect -> Effect -> InferenceM EffSubst
unifyEffect e1 e2 = case (e1, e2) of
  (EffVar v, eff) -> return (Map.singleton v eff)
  (eff, EffVar v) -> return (Map.singleton v eff)
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

-- | Strict unification for types (structure must match exactly, effects unified)
-- | Expected type comes first then actual type
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
  (TArrow vs1 a1 r1 e1, TArrow vs2 a2 r2 e2) | length vs1 == length vs2 -> do
    s1 <- unifyType a1 a2
    s2 <- unifyType (substType s1 r1) (substType s1 r2)
    s3 <- unifyEffect (substEffect s2 (substEffect s1 e1)) (substEffect s2 (substEffect s1 e2))
    return (Map.unions [s1, s2, s3])
  _ -> fail $ "Type mismatch: \n  Expected " <> fromString (show (pretty t1)) <> " \n  Actual   " <> fromString (show (pretty t2))

-- | Collect all free effect variables in an Effect
freeEffVarsEffect :: Effect -> Set EffVarName
freeEffVarsEffect eff = case eff of
  EffVar v -> Set.singleton v
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
freeEffVarsType :: Type -> Set EffVarName
freeEffVarsType ty = case ty of
  TArrow vs t1 t2 eff ->
    (freeEffVarsType t1 `Set.union` freeEffVarsType t2 `Set.union` freeEffVarsEffect eff) Set.\\ Set.fromList vs
  TPair t1 t2 -> freeEffVarsType t1 `Set.union` freeEffVarsType t2
  _ -> Set.empty

-- | Generalize all free effect variables in a type into a schema
-- | Wraps the type in SForall for each free effect variable (in sorted order for determinism)
generalizeEffect :: Type -> Type
generalizeEffect (TArrow vs i o e) =
  let effVars = toList
        ((freeEffVarsType i `Set.union` freeEffVarsType o `Set.union` freeEffVarsEffect e) Set.\\ Set.fromList vs)
      sortedVars = List.sort effVars
  in TArrow (vs ++ sortedVars) i o e
generalizeEffect ty = ty