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
  , composeSubst
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
    (sDecls, env1, effEnv1, tdecls) <- local (\ctx -> ctx {scopedEffVars = scoped}) $
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

    (sRet, tret) <- inferTyEffExprTypedM sigmaE env1 effEnv1 retVarNode
    let actualRetSchema = getType tret
        retSpan = maybe span annSourceSpan retVarAnnotation
    -- Use the source context from the return variable for better error reporting
    sAnn <- withSourceContext (Just retSpan) (Text.pack $ "Return type of " <> Text.unpack name) $
      unifyType retSchema actualRetSchema
    -- The component's substitution, applied once more to everything built
    -- under an earlier, partial one: every annotation in the typed tree and
    -- every cascade in Δ.
    let s = composeSubsts [sAnn, sRet, sDecls]
        tdecls' = map (substDeclaration s) tdecls
        tret' = substNode s tret
        effEnv' = substDelta s effEnv1
        newEntry = SigmaEntry (mkComponent name effParams args tdecls' ret retSchema) effEnv'
        sigma' = case sigma of Sigma m -> Sigma (Map.insert name newEntry m)
    pure ((tdecls', tret'), sigma')

-- | Context-aware declaration list inference. Each declaration is inferred
-- under Γ and Δ with the substitution so far already applied, and the
-- declarations' substitutions are composed.
inferTyEffDeclsM :: Sigma -> SigmaE -> Set EffVarKey -> TyEnv -> Delta -> [Declaration] -> InferenceM (EffSubst, TyEnv, Delta, [AnnotatedDeclaration])
inferTyEffDeclsM _ _ _ tyEnv delta [] = return (Map.empty, tyEnv, delta, [])
inferTyEffDeclsM sigma sigmaE scope tyEnv delta (d : ds) = do
  (s1, tyEnv', delta', texpr) <- inferTyEffDeclM sigma sigmaE scope tyEnv delta d
  (s2, tyEnv'', delta'', texprs) <- inferTyEffDeclsM sigma sigmaE scope tyEnv' delta' ds
  return (composeSubst s2 s1, tyEnv'', delta'', texpr : texprs)

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
--
-- Returns the declaration's substitution θ together with Γ′ and Δ′, which
-- are already under θ, as Algorithm W returns θΓ.
inferTyEffDeclM :: Sigma -> SigmaE -> Set EffVarKey -> TyEnv -> Delta -> Declaration -> InferenceM (EffSubst, TyEnv, Delta, AnnotatedDeclaration)
inferTyEffDeclM (Sigma sigma) sigmaE scope tyEnv effEnv declNode@(_ :< declF) = do
  let span = getDeclarationSpan declNode
      declText = Text.pack (show (pretty declNode))
  withSourceContext (Just span) declText $ case declF of
    DeclStateF var setter expr -> do
      (s, texpr) <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-STATE-DECL purity premise: the default must be pure.
      enforcePureStateDefault var (getEffect texpr)
      let ty = getType texpr
          setterTy = TArrow [] (TArrow [] ty ty EffNone) TUnit (EffAfter (Time 1 Renders) (EffStateChange var))
          env' = Map.insert var ty $ Map.insert setter setterTy (substEnv s tyEnv)
          effEnv' = Delta (Map.insert var (DeltaEntry [] EffNone) (unDelta (substDelta s effEnv)))
      pure (s, env', effEnv', SourceAnnotation span :< DeclStateF var setter texpr)
    DeclEffectF deps (Block exprs) -> do
      -- T-ON-DECL: each watched name must have a Δ entry. Without this
      -- check an unknown name is skipped by the update below and the block's
      -- effect is lost.
      forM_ deps $ \x -> unless (Map.member x (unDelta effEnv)) $
        fail $ if Map.member x tyEnv
          then "Cannot watch " <> Text.unpack x <> " in `on`: it is not an argument, state variable, let or instance"
          else "Variable not in scope: " <> Text.unpack x
      (s, texprs) <- inferTyEffExprsM sigmaE tyEnv effEnv exprs
      let blockEffects = map (substEffect s . getEffect) texprs
          combinedEffect = seqMany blockEffects
          f casc x = Map.update (\(DeltaEntry d e) -> Just $ DeltaEntry d (effSeq e combinedEffect)) x casc
          effEnv' = List.foldl f (unDelta (substDelta s effEnv)) deps
      pure (s, substEnv s tyEnv, Delta effEnv', SourceAnnotation span :< DeclEffectF deps (Block texprs))
    -- Both kinds of let are generalised, as in Hindley–Milner: the purity
    -- premise already makes the right-hand side a value-like expression, so
    -- no value restriction is needed. Generalisation sees Γ under the
    -- right-hand side's substitution, so a variable the right-hand side has
    -- tied to the context is not quantified.
    DeclLetF var (Just sch) expr -> do
      (s1, texpr) <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-LET-DECL purity premise: before env/effEnv updates AND
      -- before the check against the annotation (see the placement contract
      -- on 'enforcePureStateDefault').
      enforcePureLetRHS var (getEffect texpr)
      let ctx = contextFreeVars scope (substEnv s1 tyEnv)
          inferred = generalizeEffect ctx (getType texpr)
      -- What the annotation fixes about the context is kept, like any
      -- other unifier.
      s2 <- checkAnnotation var ctx sch inferred
      let s = composeSubst s2 s1
      -- The declared type is the binding's type.
          env' = Map.insert var sch (substEnv s tyEnv)
          deps = toList $ freeVars expr
          newEntry = DeltaEntry deps EffNone
          effEnv' = Delta (Map.insert var newEntry (unDelta (substDelta s effEnv)))
      pure (s, env', effEnv', SourceAnnotation span :< DeclLetF var (Just sch) texpr)
    DeclLetF var Nothing expr -> do
      (s, texpr) <- inferTyEffExprTypedM sigmaE tyEnv effEnv expr
      -- T-LET-DECL purity premise.
      enforcePureLetRHS var (getEffect texpr)
      let env1 = substEnv s tyEnv
          ty = generalizeEffect (contextFreeVars scope env1) (getType texpr)
          env' = Map.insert var ty env1
          deps = toList $ freeVars expr
          newEntry = DeltaEntry deps EffNone
          effEnv' = Delta (Map.insert var newEntry (unDelta (substDelta s effEnv)))
      pure (s, env', effEnv', SourceAnnotation span :< DeclLetF var Nothing texpr)
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
              subCompDelta = unDelta (substDelta renaming (Delta subCompDelta0))
              effParams' = map (\p -> Map.findWithDefault (EffVar p) (Written p) renaming) effParams

          -- Validate and build substitutions. The explicit effect
          -- arguments are the first substitution; each argument's unifier
          -- is composed onto it in turn.
          validateArgumentCount args compName
          effSubst <- buildEffectSubstitution compName effParams'
          finalSubst <- validateArgumentTypes args tyEnv effSubst

          -- Apply substitutions and build environment
          let env' = buildTypeEnvironment retTy args tyEnv
              effEnv' = buildEffectEnvironment retName args subCompDelta effEnv
              env'' = substEnv finalSubst env'
              Delta effEnv'' = substDelta finalSubst (Delta effEnv')

          return (finalSubst, env'', Delta effEnv'', SourceAnnotation span :< declF)
        _ -> fail $ "Component " <> Text.unpack compName <> " not found in environment"
      where
        validateArgumentCount args compName =
          when (length args /= length argNames) $
            fail $ "Component " <> Text.unpack compName <> " expects " <> show (length args) <> " arguments, got " <> show (length argNames)

        -- @A⟨F̂⟩@ must give one effect argument (or @?@) per effect
        -- parameter; with no @⟨…⟩@ at all, every parameter is inferred.
        buildEffectSubstitution compName effParams = do
          effsList <- case effAnnots of
            Nothing -> pure (replicate (length effParams) Nothing)
            Just es
              | length es == length effParams -> pure es
              | otherwise ->
                  fail $ "Component " <> Text.unpack compName <> " takes " <> show (length effParams)
                    <> " effect argument(s), got " <> show (length es)
          return $ Map.fromList [(Unif u, effVal) | (EffUnif u, Just effVal) <- zip effParams effsList]

        validateArgumentTypes args env effSubst = do
          let argPairs = zip argNames (map snd args)
          foldM validateSingleArgument effSubst argPairs
          where
            validateSingleArgument subst (argName, expectedTy) =
              case Map.lookup argName env of
                Just actualSch -> do
                  -- An argument is an occurrence of a variable, so its type
                  -- is instantiated as at 'EVarF' — unless the parameter
                  -- is itself a schema, which the argument's schema must
                  -- then match up to renaming (see 'unifyType').
                  actualTy <- case expectedTy of
                    TArrow (_ : _) _ _ _ -> pure (substType subst actualSch)
                    _ -> instantiateSchema (substType subst actualSch)
                  s <- unifyType (substType subst expectedTy) actualTy
                  return (composeSubst s subst)
                Nothing ->
                  fail $ "Argument " <> Text.unpack argName <> " not in scope for subcomponent " <> Text.unpack instName

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

-- | Context-aware inference for expressions: Algorithm W. Returns the
-- substitution θ the expression's unifications produced, and the typed
-- node, whose own type and effect are under θ. Subterms are inferred left to
-- right, each under Γ with the substitution so far applied, and the effects
-- already built are brought under the final θ before they are combined.
-- Annotations inside the tree may lag behind: the component applies its final
-- substitution to the whole tree (see 'substNode').
inferTyEffExprTypedM :: SigmaE -> TyEnv -> Delta -> AnnotatedNode -> InferenceM (EffSubst, AnnotatedNode)
inferTyEffExprTypedM sigmaE env effEnv inputNode@(_ :< langF) = do
  -- Update context with current node information
  let span = getNodeSpan inputNode
      exprText = Text.pack (show (pretty inputNode))
      noSubst node = return (Map.empty, node)
  withSourceContext (Just span) exprText $ case langF of
    LangFExpr exprF -> case exprF of
      EVarF x ->
        case Map.lookup x env of
          Just ty -> do
            instantiatedTy <- instantiateSchema ty
            noSubst $ NodeAnnotation span instantiatedTy EffNone :< LangFExpr (EVarF x)
          Nothing -> fail $ "Variable not in scope: " <> Text.unpack x
      ELitIntF n -> noSubst $ mkSimpleTypedExpr span TInt (ELitIntF n)
      ELitStringF s -> noSubst $ mkSimpleTypedExpr span TString (ELitStringF s)
      ELitBoolF b -> noSubst $ mkSimpleTypedExpr span TBool (ELitBoolF b)
      EJSXNodeF node -> do
        (s, tnode) <- inferTyEffJSXNodeTypedM sigmaE env effEnv node
        return (s, mkTypedExpr span THtml (getEffect tnode) (EJSXNodeF tnode))
      EArrowF vs param mTy body -> do
        paramTy <- maybe (pure TAny) flexibleParamAnnotation mTy
        let env' = Map.insert param paramTy env
        (s, tbody) <- inferTyEffExprTypedM sigmaE env' effEnv body
        let bodyTy = getType tbody
            bodyEff = getEffect tbody
        return (s, mkSimpleTypedExpr span
          (TArrow vs (substType s paramTy) (ensureMono bodyTy) bodyEff)
          (EArrowF vs param mTy tbody))

      EAppF f x -> do
        (s1, tf) <- inferTyEffExprTypedM sigmaE env effEnv f
        tfTy <- case getType tf of
          tfSch@(TArrow {}) -> instantiateSchema tfSch
          TAny ->
            fail $ "Cannot apply " <> show (pretty f) <> ": its type is any"
              <> " (an unannotated λ parameter, or null), which is not known to be a function."
              <> " Annotate it with a function type."
          other ->
            fail $ "Type error: applying " <> show (pretty f) <> ", which is not a function: it has type "
              <> show (pretty other)
        let (argTy, retTy, callEff) = case tfTy of
              TArrow _ a r e -> (a, r, e)
              _ -> error "EAppF: instantiating an arrow gave a non-arrow"
        (s2, tx, s3) <- case argTy of
          -- A schema parameter takes an argument the Damas–Milner way, as an
          -- annotated let does: the argument's type is generalised, and the
          -- parameter's schema must be an instance of it. Unifying the
          -- schema with the argument's (instantiated or binder-free) type
          -- would compare binder lists that cannot match.
          TArrow (_ : _) _ _ _ -> do
            scoped <- asks scopedEffVars
            let env1 = substEnv s1 env
                ctx0 = contextFreeVars (Set.map Written scoped) env1
                (_, expected) = skolemise (Set.fromList [v | Written v <- toList ctx0]) argTy
            (s2, tx) <- inferTyEffExprTypedWithExpectedM sigmaE env1 effEnv (Just expected) x
            -- Besides Γ, the argument's own effect and the parameter's free
            -- variables (the function's, instantiated) belong to the context.
            let ctx = Set.unions
                  [ contextFreeVars (Set.map Written scoped) (substEnv s2 env1)
                  , freeEffVarsEffect (getEffect tx)
                  , freeEffVarsType (substType s2 argTy)
                  ]
                inferred = generalizeEffect ctx (getType tx)
            s3 <- checkInstance ctx (substType s2 argTy) inferred
              (\err -> "The argument " <> show (pretty x) <> " is not as polymorphic as the parameter of "
                 <> show (pretty f)
                 <> "\n  Parameter " <> show (pretty (substType s2 argTy))
                 <> "\n  Argument  " <> show (pretty inferred)
                 <> "\n  " <> Text.unpack (errorMessage err))
              ("The parameter of " <> show (pretty f) <> " quantifies an effect variable that the context fixes"
                 <> "\n  Parameter " <> show (pretty (substType s2 argTy))
                 <> "\n  Argument  " <> show (pretty inferred))
            pure (s2, tx, s3)
          _ -> do
            (s2, tx) <- inferTyEffExprTypedWithExpectedM sigmaE (substEnv s1 env) effEnv (Just argTy) x
            s3 <- unifyType (substType s2 argTy) (getType tx)
            pure (s2, tx, s3)
        let s = composeSubsts [s3, s2, s1]
            appEff = substEffect s (getEffect tf) `effSeq` substEffect s (getEffect tx) `effSeq` substEffect s callEff
        return (s, mkTypedExpr span (substType s retTy) appEff (EAppF tf tx))
      EIfF cond bThen bElse -> do
        (s1, tCond) <- inferTyEffExprTypedM sigmaE env effEnv cond
        (s2, tThen) <- inferTyEffExprTypedM sigmaE (substEnv s1 env) effEnv bThen
        let s12 = composeSubst s2 s1
        (s3, tElse) <- inferTyEffExprTypedM sigmaE (substEnv s12 env) effEnv bElse
        let s123 = composeSubst s3 s12
        condSubst <- unifyType TBool (substType s123 (getType tCond))
        let s1234 = composeSubst condSubst s123
        branchSubst <- unifyType (substType s1234 (getType tThen)) (substType s1234 (getType tElse))
        let s = composeSubst branchSubst s1234
            resultSch = substType s (getType tThen)
            condEff' = substEffect s (getEffect tCond)
            thenEff' = substEffect s (getEffect tThen)
            elseEff' = substEffect s (getEffect tElse)
            eff = effSeq condEff' (EffBranch thenEff' elseEff')
        return (s, mkTypedExpr span resultSch eff (EIfF tCond tThen tElse))
      EEffectF eff -> noSubst $ mkTypedExpr span TUnit eff (EEffectF eff)
      EPairF e1 e2 -> do
        (s, tes) <- inferTyEffExprsM sigmaE env effEnv [e1, e2]
        let (te1, te2) = case tes of
              [a, b] -> (a, b)
              _ -> error "EPairF: two components inferred as a different number"
            eff = effSeq (substEffect s (getEffect te1)) (substEffect s (getEffect te2))
            pairTy = TPair (substType s (getType te1)) (substType s (getType te2))
        return (s, mkTypedExpr span pairTy eff (EPairF te1 te2))
      EPairAccessF e ix -> do
        (s, te) <- inferTyEffExprTypedM sigmaE env effEnv e
        case getType te of
          TPair t0 t1 ->
            let resultTy = if ix == 0 then t0 else t1
            in return (s, mkTypedExpr span resultTy (getEffect te) (EPairAccessF te ix))
          _ -> fail "Type error: pair access on non-pair"
      -- T-CANCEL (paper TY CANCEL): cancel ℓ⟨v⟩ : unit ∣ ⊘ℓ⟨v⟩. Strict: the
      -- label must be declared in Σ_E.
      ECancelF lbl -> do
        _ <- lookupEventPayload sigmaE lbl
        noSubst $ mkTypedExpr span TUnit (EffCancel lbl) (ECancelF lbl)
      -- T-REMOVE (paper TY REMOVE): remove ℓ⟨v⟩ : unit ∣ ✗ℓ⟨v⟩.
      ERemoveF lbl -> do
        _ <- lookupEventPayload sigmaE lbl
        noSubst $ mkTypedExpr span TUnit (EffRemove lbl) (ERemoveF lbl)
      -- T-BIND (paper TY BIND): bind ℓ⟨v⟩ e : unit ∣ F_e * □ℓ⟨v⟩(F), where the
      -- handler e must be a closure (τ → unit | F) with τ = Σ_E(ℓ⟨v⟩).
      EBindF lbl e -> do
        (s, te, latent) <- inferListener "bind" lbl e
        let eff = effSeq (getEffect te) (EffAlways lbl latent)
        return (s, mkTypedExpr span TUnit eff (EBindF lbl te))
      -- T-ONCE (paper TY ONCE): as T-BIND, but a one-shot listener → ◇ℓ⟨v⟩(F).
      EOnceF lbl e -> do
        (s, te, latent) <- inferListener "once" lbl e
        let eff = effSeq (getEffect te) (EffEventually lbl latent)
        return (s, mkTypedExpr span TUnit eff (EOnceF lbl te))
    -- JSX has one inference path, in 'inferTyEffJSXNodeTypedM'. Do not inline a
    -- second copy here: the effect a node propagates is what T-LET-DECL's
    -- purity premise checks, and two copies drift.
    LangFJSXNode _ -> inferTyEffJSXNodeTypedM sigmaE env effEnv inputNode
    LangFJSXChild _ -> inferTyEffJSXNodeTypedM sigmaE env effEnv inputNode
  where
    -- The handler of a @bind@ or @once@: its substitution, the typed handler
    -- with its effect under that substitution, and its latent effect.
    inferListener :: String -> EventLabel -> AnnotatedNode -> InferenceM (EffSubst, AnnotatedNode, Effect)
    inferListener kw lbl e = do
      payload <- lookupEventPayload sigmaE lbl
      -- WithExpected pushes the payload type into UNANNOTATED inline lambdas
      -- (EArrowF defaults param to TAny otherwise, which would satisfy the
      -- paper's τ = Σ_E(ℓ⟨v⟩) premise vacuously); annotated handlers fall
      -- through to plain inference. Mirrors EAppF's argument discipline.
      (s1, te) <- inferTyEffExprTypedWithExpectedM sigmaE env effEnv (Just (TArrow [] payload TUnit EffNone)) e
      -- Mirror EAppF's instantiation discipline: instantiate schemas.
      teFnTy <- case getType te of
        sch@(TArrow {}) -> instantiateSchema sch
        _ -> fail $ kw <> " expects a function (τ → unit | F)"
      case teFnTy of
        TArrow _ argTy retTy latent -> do
          s2 <- unifyType argTy payload
          s3 <- unifyType (substType s2 retTy) TUnit
          let s = composeSubsts [s3, s2, s1]
              te' = substNode s te
          return (s, te', substEffect s latent)
        _ -> fail $ kw <> " expects a function (τ → unit | F)"

-- | Infer a list of expressions left to right, threading the substitution:
-- each is inferred under Γ with the substitution so far applied. The
-- expressions' own types and effects are under their own substitutions only;
-- apply the returned one to bring them up to date.
inferTyEffExprsM :: SigmaE -> TyEnv -> Delta -> [AnnotatedNode] -> InferenceM (EffSubst, [AnnotatedNode])
inferTyEffExprsM sigmaE env effEnv = go Map.empty []
  where
    go s acc [] = return (s, reverse acc)
    go s acc (e : es) = do
      (s', te) <- inferTyEffExprTypedM sigmaE (substEnv s env) effEnv e
      go (composeSubst s' s) (te : acc) es

-- | Type inference for JSX attributes, handling expressions in attribute
-- values, left to right as 'inferTyEffExprsM' does.
inferTyEffJSXAttrsM :: SigmaE -> TyEnv -> Delta -> [JSXAttr] -> InferenceM (EffSubst, [JSXAttr])
inferTyEffJSXAttrsM sigmaE env effEnv = go Map.empty []
  where
    go s acc [] = return (s, reverse acc)
    go s acc (a : as) = do
      (s', ta) <- inferTyEffJSXAttrM sigmaE (substEnv s env) effEnv a
      go (composeSubst s' s) (ta : acc) as

-- | Type inference for a single JSX attribute
inferTyEffJSXAttrM :: SigmaE -> TyEnv -> Delta -> JSXAttr -> InferenceM (EffSubst, JSXAttr)
inferTyEffJSXAttrM sigmaE env effEnv (JSXAttr (name, value)) = case value of
  JSXAttrString text -> return (Map.empty, JSXAttr (name, JSXAttrString text))
  -- A JSX attribute is an ordinary expression: listeners are registered with
  -- @bind@/@once@, never by an attribute, so no attribute name is special.
  JSXAttrExpr expr -> do
    (s, typedExpr) <- inferTyEffExprTypedM sigmaE env effEnv expr
    return (s, JSXAttr (name, JSXAttrExpr typedExpr))

-- | Context-aware inference for expressions with expected type
inferTyEffExprTypedWithExpectedM :: SigmaE -> TyEnv -> Delta -> Maybe Type -> AnnotatedNode -> InferenceM (EffSubst, AnnotatedNode)
inferTyEffExprTypedWithExpectedM sigmaE env effEnv mExpected inputNode@(_ :< langF) =
  let span = getNodeSpan inputNode
      exprText = Text.pack (show (pretty inputNode))
  in withSourceContext (Just span) exprText $ case langF of
    LangFExpr (EArrowF vs param Nothing body) -> case mExpected of
      Just (TArrow vs' argTy _ _) | length vs == length vs' -> do
        let env' = Map.insert param argTy env
        (s, tbody) <- inferTyEffExprTypedM sigmaE env' effEnv body
        let bodyTy = getType tbody
        let bodyEff = getEffect tbody
        return (s, mkSimpleTypedExpr span (TArrow vs (substType s argTy) (ensureMono bodyTy) bodyEff) (EArrowF vs param Nothing tbody))
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
inferTyEffJSXNodeTypedM :: SigmaE -> TyEnv -> Delta -> AnnotatedNode -> InferenceM (EffSubst, AnnotatedNode)
inferTyEffJSXNodeTypedM sigmaE env effEnv node@(_ :< langF) = do
  let span = getNodeSpan node
      typedNode eff = (NodeAnnotation span THtml eff :<)
  withSourceContext (Just span) (Text.pack $ show $ pretty node) $ case langF of
    LangFJSXNode jsxF -> case jsxF of
      JSXElementNodeF tag attrs children -> do
        (s1, tChildren) <- inferTyEffExprsM sigmaE env effEnv children
        (s2, tAttrs) <- inferTyEffJSXAttrsM sigmaE (substEnv s1 env) effEnv attrs
        let s = composeSubst s2 s1
            eff = seqMany (map (substEffect s) (jsxAttrEffects tAttrs ++ map getEffect tChildren))
        return (s, typedNode eff (LangFJSXNode (JSXElementNodeF tag tAttrs tChildren)))
      JSXSelfClosingNodeF tag attrs -> do
        (s, tAttrs) <- inferTyEffJSXAttrsM sigmaE env effEnv attrs
        let eff = seqMany (map (substEffect s) (jsxAttrEffects tAttrs))
        return (s, typedNode eff (LangFJSXNode (JSXSelfClosingNodeF tag tAttrs)))
    LangFJSXChild childF -> case childF of
      ChildTextF text ->
        return (Map.empty, typedNode EffNone (LangFJSXChild (ChildTextF text)))
      ChildExprF expr -> do
        (s, texpr) <- inferTyEffExprTypedM sigmaE env effEnv expr
        return (s, typedNode (getEffect texpr) (LangFJSXChild (ChildExprF texpr)))
      ChildNodeF childNode -> do
        (s, tnode) <- inferTyEffExprTypedM sigmaE env effEnv childNode
        return (s, typedNode (getEffect tnode) (LangFJSXChild (ChildNodeF tnode)))
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

-- | Composition of substitutions: @composeSubst s2 s1@ applies @s1@ first,
-- then @s2@, so @substEffect (composeSubst s2 s1) = substEffect s2 .
-- substEffect s1@. Where both bind a variable, @s1@'s binding (under @s2@)
-- is the one that counts; inference never produces that case, since @s2@ is
-- always computed on terms @s1@ has already been applied to.
composeSubst :: EffSubst -> EffSubst -> EffSubst
composeSubst s2 s1
  | Map.null s2 = s1
  | otherwise = Map.map (substEffect s2) s1 `Map.union` s2

-- | Compose a list of substitutions, the last applied first:
-- @composeSubsts [s3, s2, s1] = s3 ∘ s2 ∘ s1@.
composeSubsts :: [EffSubst] -> EffSubst
composeSubsts = foldr composeSubst Map.empty

-- | Apply a substitution to every type in Γ.
substEnv :: EffSubst -> TyEnv -> TyEnv
substEnv s env
  | Map.null s = env
  | otherwise = Map.map (substType s) env

-- | Apply a substitution to every cascade in Δ.
substDelta :: EffSubst -> Delta -> Delta
substDelta s (Delta m)
  | Map.null s = Delta m
  | otherwise = Delta (Map.map (\(DeltaEntry deps eff) -> DeltaEntry deps (substEffect s eff)) m)

-- | Apply a substitution to every inferred type and effect in a typed tree,
-- including the expressions inside JSX attributes. Types and effects written
-- in the program (a λ-parameter annotation, an effect literal) are syntax and
-- are left alone.
substNode :: EffSubst -> AnnotatedNode -> AnnotatedNode
substNode s node@(NodeAnnotation sp ty eff :< langF)
  | Map.null s = node
  | otherwise = NodeAnnotation sp (substType s ty) (substEffect s eff) :< langF'
  where
    langF' = case langF of
      LangFJSXNode (JSXElementNodeF tag attrs children) ->
        LangFJSXNode (JSXElementNodeF tag (map attr attrs) (map (substNode s) children))
      LangFJSXNode (JSXSelfClosingNodeF tag attrs) ->
        LangFJSXNode (JSXSelfClosingNodeF tag (map attr attrs))
      other -> fmap (substNode s) other
    attr (JSXAttr (n, JSXAttrExpr e)) = JSXAttr (n, JSXAttrExpr (substNode s e))
    attr a = a

-- | 'substNode' over the expressions of a typed declaration.
substDeclaration :: EffSubst -> AnnotatedDeclaration -> AnnotatedDeclaration
substDeclaration s (ann :< declF) = ann :< case declF of
  DeclStateF var setter e -> DeclStateF var setter (substNode s e)
  DeclEffectF deps (Block es) -> DeclEffectF deps (Block (map (substNode s) es))
  DeclLetF var mTy e -> DeclLetF var mTy (substNode s e)
  DeclSubCompF {} -> declF

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
-- to it. A unification variable is not bound to an effect it occurs in (the
-- occurs check). The result is idempotent: no variable it binds occurs in
-- what it binds any variable to.
--
-- A rule with several premises solves them left to right, each under the
-- substitution so far, and composes the results (see 'unifyEffectPairs').
unifyEffect :: Effect -> Effect -> InferenceM EffSubst
unifyEffect e1 e2 = case (e1, e2) of
  (EffUnif u1, EffUnif u2) | u1 == u2 -> return Map.empty
  (EffUnif u, eff) -> bindUnif u eff
  (eff, EffUnif u) -> bindUnif u eff
  (EffVar v1, EffVar v2) | v1 == v2 -> return Map.empty
  (EffNone, EffNone) -> return Map.empty
  (EffSeq s1, EffSeq s2) | length s1 == length s2 ->
    unifyEffectPairs (zip s1 s2)
  (eff, EffSeq s2) -> do
    case s2 of
      [] -> unifyEffect eff EffNone
      eff1 : rest -> unifyEffectPairs ((eff, eff1) : map (\r -> (EffNone, r)) rest)
  (EffSeq s2, eff) -> do
    case s2 of
      [] -> unifyEffect eff EffNone
      eff1 : rest -> unifyEffectPairs ((eff, eff1) : map (\r -> (EffNone, r)) rest)
  (EffBranch a1 b1, EffBranch a2 b2) -> unifyEffectPairs [(a1, a2), (b1, b2)]
  (EffBranch a1 b1, eff) -> unifyEffectPairs [(a1, eff), (b1, eff)]
  (eff, EffBranch a1 b1) -> unifyEffectPairs [(a1, eff), (b1, eff)]
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

-- | Bind a unification variable, after the occurs check: @?e ≐ F@ with @?e@
-- free in @F@ (and @F ≠ ?e@) has no solution, since the binding would be
-- cyclic.
bindUnif :: Int -> Effect -> InferenceM EffSubst
bindUnif u eff
  | Unif u `Set.member` freeEffVarsEffect eff =
      fail $ "Cannot unify effects: " <> show (pretty (EffUnif u)) <> " and " <> show (pretty eff)
        <> " (occurs check: the variable occurs in the effect it would be bound to)"
  | otherwise = return (Map.singleton (Unif u) eff)

-- | Solve a list of effect equations left to right: each is unified under
-- the substitution the earlier ones produced, and the results are composed.
unifyEffectPairs :: [(Effect, Effect)] -> InferenceM EffSubst
unifyEffectPairs = foldM step Map.empty
  where
    step s (a, b) = do
      s' <- unifyEffect (substEffect s a) (substEffect s b)
      return (composeSubst s' s)

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
    return (composeSubst s2 s1)
  (TArrow [] a1 r1 e1, TArrow [] a2 r2 e2) -> do
    s1 <- unifyType a1 a2
    s2 <- unifyType (substType s1 r1) (substType s1 r2)
    let s12 = composeSubst s2 s1
    s3 <- unifyEffect (substEffect s12 e1) (substEffect s12 e2)
    return (composeSubst s3 s12)
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
-- annotation must be an instance of the right-hand side's generalised type
-- (see 'checkInstance').
checkAnnotation :: Text -> Set EffVarKey -> Type -> Type -> InferenceM EffSubst
checkAnnotation var ctx sch inferred =
  checkInstance ctx sch inferred
    (\err -> "The definition of '" <> Text.unpack var <> "' does not have its annotated type"
      <> "\n  Annotation " <> show (pretty sch)
      <> "\n  Inferred   " <> show (pretty inferred)
      <> "\n  " <> Text.unpack (errorMessage err))
    ("The annotation of '" <> Text.unpack var <> "' quantifies an effect variable that the context fixes"
      <> "\n  Annotation " <> show (pretty sch)
      <> "\n  Inferred   " <> show (pretty inferred))

-- | Check that a schema σ is an instance of an inferred, generalised schema.
-- σ's binders are made rigid (see 'skolemise'), the inferred schema is
-- instantiated, and the two are unified. A unification variable of the
-- context (@ctx@) may not be bound to one of σ's binders, which would let it
-- escape. The unifier is returned: what it says about the context's
-- unification variables holds from here on. The two messages are for a
-- failed unification and for an escape.
checkInstance :: Set EffVarKey -> Type -> Type -> (InferenceError -> String) -> String -> InferenceM EffSubst
checkInstance ctx sch inferred mismatch escape = do
  let (skolems, annBody) =
        skolemise (writtenNamesType inferred <> Set.fromList [v | Written v <- toList ctx]) sch
  actual <- instantiateSchema inferred
  s <- unifyType annBody actual `catchInference` (fail . mismatch)
  let escaping = [ v | (k, e) <- Map.toList s, k `Set.member` ctx
                     , Written v <- toList (freeEffVarsEffect e), v `elem` skolems ]
  unless (null escaping) $ fail escape
  return s

-- | Strip a schema's binders, renaming them to written variables fresh for
-- the schema and for @avoid@. Written variables are rigid, so the result
-- stands for the schema at an arbitrary instance.
skolemise :: Set EffVarName -> Type -> ([EffVarName], Type)
skolemise avoid sch = case sch of
  TArrow vs i o e ->
    let sk = freshNames (avoid <> writtenNamesType sch) vs
        rename = Map.fromList (zip (map Written vs) (map EffVar sk))
    in (sk, substType rename (TArrow [] i o e))
  _ -> ([], sch)

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
