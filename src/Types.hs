{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Types
  ( Options (..),
    RIOApp (..),
    -- New Cofree-based types
    Program,               -- Alias for AnnotatedProgram
    Component,             -- Alias for AnnotatedComponent
    Declaration,           -- Alias for AnnotatedDeclaration
    Expr,                  -- Alias for AnnotatedNode
    JSXNode,               -- Alias for AnnotatedNode
    JSXChild,              -- Alias for AnnotatedNode
    Block (..),            -- List of AnnotatedNode
    -- Annotation types
    SourceAnnotation (..),
    NodeAnnotation (..),
    Span (..),
    -- Core annotated types
    AnnotatedProgram,
    AnnotatedEventDecl,
    AnnotatedComponent,
    AnnotatedDeclaration,
    AnnotatedNode,
    -- F-algebras
    ProgramF (..),
    EventDeclF (..),
    ComponentF (..),
    DeclarationF (..),
    LangF (..),
    ExprF (..),
    JSXNodeF (..),
    JSXChildF (..),
    -- JSX attribute types (non-recursive)
    JSXAttr (..),
    JSXAttrValue (..),
    -- Type system
    Type (..),
    Effect (..),
    EventLabel (..),
    EffectSummary (..),
    Delay (..),
    Unit (..),
    Delta (..),
    DeltaEntry (..),
    Sigma (..),
    SigmaEntry (..),
    SigmaE (..),
    emptySigma,
    emptySigmaE,
    EffVarName (..),
    -- Helper functions
    getSpanFromSourceAnn,
    getSpanFromNodeAnn,
    getType,
    getEffect,
    prettySpan,
    commaSep,
    prettyArgs,
    prettyType,
    -- Effect printing (see the note above 'prettyEffect')
    prettyEffect,
    prettyEffectReadable,
    renderEffect,
    renderEffectSummary,
    effectsEqual,
    unSigma,
    unDeltaEntry,
    testOptions,
    mkEffSeq,
    isIdempotentEffect,
    -- Migration helper functions
    mkVar, mkLitInt, mkLitString, mkLitBool,
    mkApp, mkIf, mkArrow, mkEffect, mkPair, mkPairAccess,
    mkJSXElement, mkJSXSelfClosing, mkChildText, mkChildExpr, mkChildNode, mkJSXNode,
    mkDeclState, mkDeclEffect, mkDeclLet, mkDeclSubComp,
    mkComponent, mkEventDecl, mkProgram, mkTypedExpr,
    -- AST accessors
    getComponents, getEventDecls, getComponentName, getComponentArgs,
    dummyNodeAnnotation, dummySourceAnn, dummySpan, unDelta, mkSimpleTypedNode, mkSimpleTypedExpr, getDeclarationSpan, getComponentSpan, getNodeSpan,
    -- Debug/Show helper for the annotated AST
    showAnnotatedNode
  )
where

import RIO
import qualified RIO.Map as Map
import qualified RIO.Text as Text
import RIO.Process
import qualified Data.Set.Ordered as OSet
import Text.Megaparsec (SourcePos (..), unPos, mkPos, sepBy)
import Control.Comonad.Cofree (Cofree (..))
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import Data.Functor.Foldable (Recursive(..), Corecursive(..), Base)
import Data.Functor.Classes (Show1(..), Eq1(..), Ord1(..), showsPrec1, eq1, compare1)
import Text.Show
import Data.List (intercalate)


data Span = Span
  { spanStart :: SourcePos
  , spanEnd   :: SourcePos
  } deriving (Show, Eq, Ord)

instance Semigroup Span where
  (Span s1 e1) <> (Span s2 e2) =
    Span (min s1 s2) (max e1 e2)

prettySpan :: Span -> String
prettySpan (Span s e) =
  sourcePosPretty s ++ "-" ++
  (if sourceName s == sourceName e && sourceLine s == sourceLine e
   then show (unPos $ sourceColumn e)
   else sourcePosPretty e)

sourcePosPretty :: SourcePos -> String
sourcePosPretty (SourcePos name lineNum col) =
  name ++ ":" ++ show (unPos lineNum) ++ ":" ++ show (unPos col)

-- Annotation for top-level constructs (Program, Component, Declaration)
data SourceAnnotation = SourceAnnotation
  { annSourceSpan :: Span
  } deriving (Show, Eq, Ord)

-- Helper to get Span from SourceAnnotation
getSpanFromSourceAnn :: Cofree f SourceAnnotation -> Span
getSpanFromSourceAnn (ann :< _) = annSourceSpan ann

-- Enriched Annotation Type for Expression Nodes
data NodeAnnotation = NodeAnnotation
  { annNodeSpan :: Span
  , annType :: Type  -- The inferred Type for this node
  , annEffect :: Effect  -- The inferred effect for this node
  } deriving (Show, Eq, Ord)

-- Helper to get Span from NodeAnnotation
getSpanFromNodeAnn :: Cofree f NodeAnnotation -> Span
getSpanFromNodeAnn (ann :< _) = annNodeSpan ann

-- Helper to get Type from NodeAnnotation
getType :: Cofree f NodeAnnotation -> Type
getType (ann :< _) = annType ann

-- Helper to get Effect from NodeAnnotation
getEffect :: Cofree f NodeAnnotation -> Effect
getEffect (ann :< _) = annEffect ann

data Options = Options
  { optionsVerbose :: !Bool
  , optionsInitialRenderAnalysis :: !Bool
  , optionsHandlerCleanupAnalysis :: !Bool
  , optionsInputFile :: !(Maybe FilePath)
  }
testOptions :: Options
testOptions = Options False False False Nothing

data RIOApp = RIOApp
  { appLogFunc :: !LogFunc
  , appProcessContext :: !ProcessContext
  , appOptions :: !Options
  , appVarCounter :: !(IORef Int)
  }

instance HasLogFunc RIOApp where
  logFuncL = lens appLogFunc (\x y -> x {appLogFunc = y})

instance HasProcessContext RIOApp where
  processContextL = lens appProcessContext (\x y -> x {appProcessContext = y})

-- F-algebra for event declarations (@event ℓ⟨v⟩ : τ;@).
-- The recursive parameter is phantom; event declarations have no children.
data EventDeclF r
  = EventDeclF EventLabel Type -- event label, payload type
  deriving (Functor)

-- Annotated event declaration type
type AnnotatedEventDecl = Cofree EventDeclF SourceAnnotation

-- F-algebra for Program
data ProgramF r
  = ProgramF [AnnotatedEventDecl] [AnnotatedComponent] -- event declarations, then components
  deriving (Functor)

-- Annotated Program type
type AnnotatedProgram = Cofree ProgramF SourceAnnotation

-- Alias for user-facing Program type
type Program = AnnotatedProgram

-- F-algebra for Component
data ComponentF r
  = ComponentF
    { compFName :: Text,
      compFEffectParams :: [EffVarName],
      compFArgs :: [(Text, Type)],
      compFDecls :: [AnnotatedDeclaration],
      compFReturn :: Text,
      compFReturnType :: Type
    }
  deriving (Functor)

-- Annotated Component type
type AnnotatedComponent = Cofree ComponentF SourceAnnotation

-- Alias for user-facing Component type
type Component = AnnotatedComponent

-- F-algebra for Declaration
data DeclarationF r
  = DeclStateF Text Text AnnotatedNode -- state var, setter, initial value
  | DeclEffectF [Text] Block -- effect deps, block of statements
  | DeclLetF Text (Maybe Type) AnnotatedNode -- let var = expr
  | DeclSubCompF Text Text (Maybe [Maybe Effect]) [Text] -- instance name, component name, args
  deriving (Functor)

-- Annotated Declaration type
type AnnotatedDeclaration = Cofree DeclarationF SourceAnnotation

-- Alias for user-facing Declaration type
type Declaration = AnnotatedDeclaration

-- Block of statements - contents are AnnotatedNode
newtype Block = Block [AnnotatedNode]

-- F-algebra for Expression types
data ExprF r
  = EVarF Text
  | ELitIntF Integer
  | ELitStringF Text
  | ELitBoolF Bool
  | EJSXNodeF r
  | EArrowF [EffVarName] Text (Maybe Type) r
  | EAppF r r
  | EIfF r r r
  | EEffectF Effect
  | EPairF r r
  | EPairAccessF r Int
  | EBindF EventLabel r   -- ^ @bind ℓ⟨v⟩ e@ — register a persistent listener
  | EOnceF EventLabel r   -- ^ @once ℓ⟨v⟩ e@ — register a one-shot listener
  | ECancelF EventLabel   -- ^ @cancel ℓ⟨v⟩@ — suppress one pending firing
  | ERemoveF EventLabel   -- ^ @remove ℓ⟨v⟩@ — unregister every listener for ℓ⟨v⟩
  deriving (Functor, Show, Eq, Ord)

-- F-algebra for JSX node types
data JSXNodeF r
  = JSXElementNodeF Text [JSXAttr] [r]
  | JSXSelfClosingNodeF Text [JSXAttr]
  deriving (Functor, Show, Eq, Ord)

-- JSXAttr (unchanged, as its value can be AnnotatedNode)
newtype JSXAttr = JSXAttr (Text, JSXAttrValue)

-- JSXAttrValue (now refers to AnnotatedNode for expressions)
data JSXAttrValue
  = JSXAttrString Text
  | JSXAttrExpr AnnotatedNode

-- F-algebra for JSX child types
data JSXChildF r
  = ChildTextF Text
  | ChildExprF r
  | ChildNodeF r
  deriving (Functor, Show, Eq, Ord)

-- Universal Language Functor for the expression AST
data LangF r
  = LangFExpr !(ExprF r)
  | LangFJSXNode !(JSXNodeF r)
  | LangFJSXChild !(JSXChildF r)
  deriving (Functor, Show, Eq, Ord)

-- Universal Annotated Node type for expressions
type AnnotatedNode = Cofree LangF NodeAnnotation

-- Aliases for clarity (internally they are all AnnotatedNode)
type Expr = AnnotatedNode
type JSXNode = AnnotatedNode
type JSXChild = AnnotatedNode

-- Type system definitions
data Type
  = TString
  | TInt
  | TBool
  | TUnit
  | THtml
  | TArrow [EffVarName] Type Type Effect
  | TDelay Delay Type
  | TComponent [Type] Type
  | TPair Type Type
  | TAny
  deriving (Eq, Show, Ord)

newtype EffVarName = EffVarName Text
  deriving (Eq, Show, Ord)

-- | An event label ℓ⟨v⟩: an event-kind name plus a tuple of statically-known
-- base values (stored verbatim, e.g. "#doc" keeps its '#'; empty tuple allowed,
-- e.g. timeout<>).
data EventLabel = EventLabel Text [Text]
  deriving (Eq, Show, Ord)

data Effect
  = EffNone
  | EffLoop Text
  | EffStateChange Text
  | EffAfter Delay Effect
  | EffSeq [Effect]
  | EffBranch Effect Effect
  | EffVar EffVarName
  | EffEvent EventLabel                 -- ^ event effect ℓ⟨v⟩
  | EffAlways EventLabel Effect         -- ^ □ modality (bind/always)
  | EffEventually EventLabel Effect     -- ^ ◇ modality (once/eventually)
  | EffCancel EventLabel                -- ^ ⊘ modality
  | EffRemove EventLabel                -- ^ ✗ modality
  deriving (Eq, Show, Ord)

-- | True iff the effect tree contains NO event-layer constructor
-- (EffEvent/EffAlways/EffEventually/EffCancel/EffRemove) and NO EffVar
-- anywhere. Only such trees are idempotent under sequencing (owner ruling
-- 2026-07-17: @x * @x = @x, but ℓ⟨v⟩ * ℓ⟨v⟩ ≠ ℓ⟨v⟩, and ?e may instantiate
-- to an event effect, so it is conservatively not idempotent).
isIdempotentEffect :: Effect -> Bool
isIdempotentEffect eff = case eff of
  EffNone -> True
  EffLoop _ -> True
  EffStateChange _ -> True
  EffAfter _ e -> isIdempotentEffect e
  EffSeq es -> all isIdempotentEffect es
  EffBranch e1 e2 -> isIdempotentEffect e1 && isIdempotentEffect e2
  EffVar _ -> False
  EffEvent _ -> False
  EffAlways _ _ -> False
  EffEventually _ _ -> False
  EffCancel _ -> False
  EffRemove _ -> False

-- | Smart constructor for 'EffSeq': dedups elements whose ENTIRE effect tree
-- is idempotent (preserving first-occurrence order); the empty list becomes
-- 'EffNone' and a singleton collapses to the bare element.
mkEffSeq :: [Effect] -> Effect
mkEffSeq effs = case go [] effs of
  [] -> EffNone
  [e] -> e
  es -> EffSeq es
  where
    go _ [] = []
    go seen (e : rest)
      | isIdempotentEffect e && e `elem` seen = go seen rest
      | isIdempotentEffect e = e : go (e : seen) rest
      | otherwise = e : go seen rest

data EffectSummary
  = EffSNone
  | EffSLoop
  | EffSItem
  | EffSAfter Delay EffectSummary
  | EffSSeq (OSet.OSet EffectSummary)
  | EffSBranch EffectSummary EffectSummary
  | EffSVar EffVarName
  | EffSEvent EventLabel
  | EffSAlways EventLabel EffectSummary
  | EffSEventually EventLabel EffectSummary
  | EffSCancel EventLabel
  | EffSRemove EventLabel
  deriving (Eq, Show, Ord)

data EffectType
  = ESMono Type
  | ESForall EffVarName EffectType
  deriving (Eq, Show, Ord)

data Delay
  = Plus Delay Delay
  | Time Int Unit
  deriving (Eq, Show, Ord)

data Unit
  = Renders
  | NetworkReq
  | Millis
  | Debounce
  | Interval
  | Compute
  deriving (Eq, Show, Ord)

data DeltaEntry = DeltaEntry
  { dependencies :: [Text],
    cascade :: Effect
  }
  deriving (Show, Eq, Ord)

newtype Delta = Delta (Map Text DeltaEntry)
  deriving (Show, Eq, Ord)

data SigmaEntry = SigmaEntry
  { component :: Component,
    effects :: Delta
  }

newtype Sigma = Sigma (Map Text SigmaEntry)

-- | Event signature Σ_E: event label ℓ⟨v⟩ → the payload type carried when it
-- fires. Populated from top-level @event ℓ⟨v⟩ : τ;@ declarations.
newtype SigmaE = SigmaE (Map EventLabel Type)
  deriving (Show, Eq)

-- | The starting program signature: Willow ships no library components, so a
-- program is checked against nothing but itself.
emptySigma :: Sigma
emptySigma = Sigma Map.empty

emptySigmaE :: SigmaE
emptySigmaE = SigmaE Map.empty

unSigma :: Sigma -> Map Text SigmaEntry
unSigma (Sigma m) = m

unDeltaEntry :: DeltaEntry -> ([Text], Effect)
unDeltaEntry (DeltaEntry deps eff) = (deps, eff)

effectsEqual :: Sigma -> Sigma -> Bool
effectsEqual sigma1 sigma2 =
  Map.keysSet (unSigma sigma1) == Map.keysSet (unSigma sigma2) &&
  all (\k -> effectsEqual' (getEffects sigma1 k) (getEffects sigma2 k)) (Map.keys (unSigma sigma1)) &&
  all (\k -> effectsEqual' (getEffects sigma1 k) (getEffects sigma2 k)) (Map.keys (unSigma sigma2))
  where
    unSigma (Sigma m) = m
    getEffects s k = case Map.lookup k (unSigma s) of
      Just entry -> effects entry
      Nothing -> Delta Map.empty

    effectsEqual' (Delta d1) (Delta d2) =
      Map.keysSet d1 == Map.keysSet d2 &&
      all (\k -> case (d1 Map.!? k, d2 Map.!? k) of
                   (Just de1, Just de2) -> dependenciesMatch de1 de2
                   _ -> False
          ) (Map.keys d1)

    dependenciesMatch (DeltaEntry deps1 eff1) (DeltaEntry deps2 eff2) =
      deps1 == deps2 && eff1 == eff2


-- Helper functions
commaSep :: [Doc ann] -> Doc ann
commaSep = hsep . punctuate comma

prettyArgs :: [(Text, Type)] -> Doc ann
prettyArgs args = parens $ commaSep [pretty n <+> ":" <+> pretty t | (n, t) <- args]

prettyType :: Type -> Doc ann
prettyType TString = "string"
prettyType TInt = "int"
prettyType TBool = "bool"
prettyType TUnit = "unit"
prettyType THtml = "html"
prettyType TAny = "any"
prettyType (TArrow (ev:effVars) arg ret eff) =
  "∀" <+> commaSep (map pretty (ev:effVars)) <>
  parens (prettyType arg) <+> "->" <+> prettyType ret <+> "|" <+> pretty eff
prettyType (TArrow [] arg@(TArrow {}) ret EffNone) = parens (prettyType arg) <+> "->" <+> prettyType ret
prettyType (TArrow [] arg ret EffNone) = parens $ prettyType arg <+> "->" <+> prettyType ret
prettyType (TArrow [] arg@(TArrow {}) ret eff) = parens (prettyType arg) <+> "->" <+> prettyType ret <+> "|" <+> pretty eff
prettyType (TArrow [] arg ret eff) = parens $ prettyType arg <+> "->" <+> prettyType ret <+> "|" <+> pretty eff
prettyType (TDelay delay inner) = "delay" <+> pretty delay <+> prettyType inner
prettyType (TComponent args ret) = "comp" <> parens (commaSep (map prettyType args)) <+> "->" <+> prettyType ret
prettyType (TPair t1 t2) = parens (pretty t1 <+> "*" <+> pretty t2)

-- Pretty instances

-- | Δ, one row per bound variable: @name [deps] | F@. The cascade is printed
-- with the readable effect printer, so a long one breaks into an indented
-- block under its row instead of running off the right-hand side.
instance Pretty Delta where
  pretty (Delta entries) = vsep $ map prettyDeltaRow (Map.toList entries)

prettyDeltaRow :: (Text, DeltaEntry) -> Doc ann
prettyDeltaRow (name, DeltaEntry deps eff) =
  group $ nest 4 $ pretty name <> prettyDeps <+> "|" <> line <> prettyEffectReadable eff
  where
    -- 'fillSep', not 'commaSep': a component with many bindings can watch more
    -- dependencies than fit on a line, and one-per-line would be wasteful.
    prettyDeps
      | null deps = mempty
      | otherwise = space <> brackets (align (fillSep (punctuate comma (map pretty deps))))

instance Pretty DeltaEntry where
  pretty (DeltaEntry deps sideEff) =
    brackets (commaSep (map pretty deps)) <+> "|" <+> pretty sideEff

instance Pretty EventLabel where
  pretty (EventLabel name values) =
    pretty name <> angles (mconcat (intercalate [","] (map (pure . pretty) values)))

-- ---------------------------------------------------------------------------
-- Effect printing
--
-- There are two effect printers, because the two jobs really are different:
--
--   * 'prettyEffect' — the CANONICAL form, and the 'Pretty' instance. Always
--     one line, minimal parentheses, and in exactly the concrete syntax
--     'Parse.pEffect' accepts, so a printed effect can be pasted back into a
--     program. Use it inline, where the effect is one field of a larger line
--     (@x : F@, error messages, traces).
--
--   * 'prettyEffectReadable' — the READABLE form. Same notation, but laid out
--     as a tree: it stays on one line while it fits the page, and otherwise
--     breaks one operand per line with the operator in a gutter to the left,
--     and turns modality bodies into indented blocks. Use it wherever a whole
--     inferred cascade is the thing being displayed — those routinely run to
--     several hundred characters, at which point one line is unreadable and
--     the structure is the only thing worth seeing.
--
-- The two agree on notation, so the renderings of an effect differ only in
-- where the line breaks fall. 'renderEffect' wraps the readable one at a
-- given width.
--
-- On parentheses: in the grammar @*@ binds LOOSER than @+@ ('Parse.pEffect' is
-- a @*@-separated list of @+@-chains), which is the opposite of the arithmetic
-- precedence a reader brings to @*@ and @+@ — @F * G + H@ means @F * (G + H)@.
-- Rather than print the minimal parenthesization and rely on the reader knowing
-- that, both printers make every mixed grouping explicit: an operand of @*@ or
-- @+@ that is itself a @*@ or @+@ is always parenthesized. Runs of one operator
-- are still flattened, so nothing gains a redundant @((…))@. The precedence
-- argument threaded through both printers is:
--
--   0 = the whole effect, or a brace/paren body   1 = an operand
-- ---------------------------------------------------------------------------

instance Pretty Effect where
  pretty = prettyEffect

-- | The canonical one-line rendering of an effect. See the note above.
prettyEffect :: Effect -> Doc ann
prettyEffect = prettyEffectPrec 0

prettyEffectPrec :: Int -> Effect -> Doc ann
prettyEffectPrec d eff = case eff of
  EffNone -> "none"
  EffLoop n -> "loop[" <> pretty n <> "]"
  EffStateChange n -> "@" <> pretty n
  EffVar v -> pretty v
  EffEvent lbl -> pretty lbl
  EffCancel lbl -> "cancel" <+> pretty lbl
  EffRemove lbl -> "remove" <+> pretty lbl
  EffAfter delay body -> "after" <+> pretty delay <+> braces (prettyEffectPrec 0 body)
  EffAlways lbl body -> "always" <+> pretty lbl <+> braces (prettyEffectPrec 0 body)
  EffEventually lbl body -> "eventually" <+> pretty lbl <+> braces (prettyEffectPrec 0 body)
  EffSeq [] -> "none"
  EffSeq [e] -> prettyEffectPrec d e
  EffSeq es -> parensIf (d > 0) $ hsep $ punctuate " *" $ map (prettyEffectPrec 1) es
  EffBranch _ _ ->
    parensIf (d > 0) $ hsep $ punctuate " +" $ map (prettyEffectPrec 1) (branchOperands eff)

-- | The readable, line-broken rendering of an effect. See the note above.
prettyEffectReadable :: Effect -> Doc ann
prettyEffectReadable = readableEffectPrec 0

readableEffectPrec :: Int -> Effect -> Doc ann
readableEffectPrec d eff = case eff of
  EffAfter delay body -> readableBlock ("after" <+> pretty delay) (readableEffectPrec 0 body)
  EffAlways lbl body -> readableBlock ("always" <+> pretty lbl) (readableEffectPrec 0 body)
  EffEventually lbl body -> readableBlock ("eventually" <+> pretty lbl) (readableEffectPrec 0 body)
  EffSeq [] -> "none"
  EffSeq [e] -> readableEffectPrec d e
  EffSeq es -> opList (d > 0) "*" $ map (readableEffectPrec 1) es
  EffBranch _ _ ->
    opList (d > 0) "+" $ map (readableEffectPrec 1) (branchOperands eff)
  -- Leaves have no interesting structure; the canonical printer already
  -- renders them in their shortest form.
  _ -> prettyEffectPrec d eff

-- | Render an effect in readable form, wrapped to @width@ columns. Note the
-- ribbon fraction of 1.0: the library's 0.4 default gives up on lines that are
-- already deeply indented, which is exactly the case here.
renderEffect :: Int -> Effect -> Text
renderEffect width =
  renderStrict
    . layoutPretty (LayoutOptions (AvailablePerLine (max 20 width) 1.0))
    . prettyEffectReadable

-- | The operands of a @+@ chain. Only the right spine is flattened, which is
-- the shape the parser and inference build, so a left-nested branch keeps its
-- parentheses and the printed form reparses to the same tree.
branchOperands :: Effect -> [Effect]
branchOperands (EffBranch e1 e2) = e1 : branchOperands e2
branchOperands e = [e]

-- | @F₁ op F₂ op F₃@, parenthesized when @paren@: one line while it fits,
-- otherwise one operand per line with the operator in a two-column gutter to
-- the left of the operands. When parenthesized, the brackets take the gutter
-- too, so the operands stay in one column either way:
--
-- >   cancel timeout<>                              ( after 1r {@status}
-- > * remove timeout<>                              * after 1n {req<check,suc>}
-- > * eventually timeout<> {after 1r {@slow}}       * remove req<check,err> )
opList :: Bool -> Doc ann -> [Doc ann] -> Doc ann
opList _ _ [] = "none"
opList paren _ [d] = if paren then parens d else d
opList paren op (d : ds) =
  group $ align $ open <> d <> mconcat [line <> op <+> x | x <- ds] <> close
  where
    open = if paren then flatAlt "( " "(" else flatAlt "  " mempty
    close = if paren then flatAlt " )" ")" else mempty

-- | @header {body}@: one line while it fits, otherwise an indented block with
-- the closing brace back under the start of the header.
readableBlock :: Doc ann -> Doc ann -> Doc ann
readableBlock header body =
  align $ group $ header <+> "{" <> nest 2 (line' <> body) <> line' <> "}"

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

-- | 'EffectSummary' is the shape of an effect with the state names erased. It
-- gets the same pair of printers for the same reason: erasing the names of a
-- deep cascade barely shortens it.
instance Pretty EffectSummary where
  pretty = prettyEffectSummaryPrec 0

-- | The readable, line-broken rendering of an effect summary, wrapped to
-- @width@ columns. The 'Effect' counterpart is 'renderEffect'.
renderEffectSummary :: Int -> EffectSummary -> Text
renderEffectSummary width =
  renderStrict
    . layoutPretty (LayoutOptions (AvailablePerLine (max 20 width) 1.0))
    . readableSummaryPrec 0

readableSummaryPrec :: Int -> EffectSummary -> Doc ann
readableSummaryPrec d eff = case eff of
  EffSAfter delay body -> readableBlock ("after" <+> pretty delay) (readableSummaryPrec 0 body)
  EffSAlways lbl body -> readableBlock ("always" <+> pretty lbl) (readableSummaryPrec 0 body)
  EffSEventually lbl body -> readableBlock ("eventually" <+> pretty lbl) (readableSummaryPrec 0 body)
  EffSSeq effs -> case toList effs of
    [] -> "none"
    [e] -> readableSummaryPrec d e
    es -> opList (d > 0) "*" $ map (readableSummaryPrec 1) es
  EffSBranch _ _ ->
    opList (d > 0) "+" $ map (readableSummaryPrec 1) (summaryBranchOperands eff)
  _ -> prettyEffectSummaryPrec d eff

prettyEffectSummaryPrec :: Int -> EffectSummary -> Doc ann
prettyEffectSummaryPrec d eff = case eff of
  EffSNone -> "none"
  EffSLoop -> "loop"
  EffSItem -> "@"
  EffSVar v -> pretty v
  EffSEvent lbl -> pretty lbl
  EffSCancel lbl -> "cancel" <+> pretty lbl
  EffSRemove lbl -> "remove" <+> pretty lbl
  EffSAfter delay body -> "after" <+> pretty delay <+> braces (prettyEffectSummaryPrec 0 body)
  EffSAlways lbl body -> "always" <+> pretty lbl <+> braces (prettyEffectSummaryPrec 0 body)
  EffSEventually lbl body -> "eventually" <+> pretty lbl <+> braces (prettyEffectSummaryPrec 0 body)
  EffSSeq effs -> case toList effs of
    [] -> "none"
    [e] -> prettyEffectSummaryPrec d e
    es -> parensIf (d > 0) $ hsep $ punctuate " *" $ map (prettyEffectSummaryPrec 1) es
  EffSBranch _ _ ->
    parensIf (d > 0) $ hsep $ punctuate " +" $ map (prettyEffectSummaryPrec 1) (summaryBranchOperands eff)

summaryBranchOperands :: EffectSummary -> [EffectSummary]
summaryBranchOperands (EffSBranch e1 e2) = e1 : summaryBranchOperands e2
summaryBranchOperands e = [e]

instance Pretty Delay where
  pretty (Plus d1 d2) = pretty d1 <+> "+" <+> pretty d2
  pretty (Time i unit) = pretty i <> pretty unit

-- | The surface spellings 'Parse.pUnit' accepts, so a printed delay reparses.
instance Pretty Unit where
  pretty Renders = "r"
  pretty NetworkReq = "n"
  pretty Millis = "ms"
  pretty Debounce = "db"
  pretty Interval = "i"
  pretty Compute = "u"

instance Pretty Type where
  pretty = prettyType

instance Pretty EffVarName where
  pretty (EffVarName n) = "?" <> pretty n

-- Pretty instances for Cofree-based types
instance Pretty Program where
  pretty (_ :< ProgramF eventDecls components) = vsep (map pretty eventDecls ++ map pretty components)

instance Pretty AnnotatedEventDecl where
  pretty (_ :< EventDeclF lbl ty) = "event" <+> pretty lbl <+> ":" <+> pretty ty <> ";"

instance Pretty Component where
  pretty (_ :< ComponentF n [] args decls ret _) =
    vsep
      [ "comp" <+> pretty n <+> prettyArgs args <+> "{",
        indent 2 (vsep (map pretty decls)),
        indent 2 $ "return" <+> pretty ret <> ";",
        "}"
      ]
  pretty (_ :< ComponentF n params args decls ret _) =
    vsep
      [ "comp" <+> pretty n <> angles (commaSep (map pretty params)) <+> prettyArgs args <+> "{",
        indent 2 (vsep (map pretty decls)),
        indent 2 $ "return" <+> pretty ret <> ";",
        "}"
      ]

instance Pretty Declaration where
  pretty (_ :< DeclStateF var setter expr) =
    "state" <+> pretty var <> "," <+> pretty setter <+> "default" <+> pretty expr <> ";"
  pretty (_ :< DeclEffectF deps block) =
    "on" <+> commaSep (map pretty deps) <+> "do" <+> pretty block <> ";"
  pretty (_ :< DeclLetF var (Just sch) expr) =
    "let" <+> pretty var <+> ":" <+> pretty sch <+> "=" <+> pretty expr <> ";"
  pretty (_ :< DeclLetF var Nothing expr) =
    "let" <+> pretty var <+> "=" <+> pretty expr <> ";"
  pretty (_ :< DeclSubCompF instName subCompName Nothing args) =
    "comp" <+> pretty instName <+> "=" <+> pretty subCompName <> parens (commaSep $ map pretty args) <> ";"
  pretty (_ :< DeclSubCompF instName subCompName (Just effs) args) =
    "comp" <+> pretty instName <+> "=" <+> pretty subCompName <> angles (commaSep (map prettyEffs effs)) <> parens (commaSep $ map pretty args) <> ";"
    where
      prettyEffs Nothing = "?"
      prettyEffs (Just e) = pretty e


instance Pretty Block where
  pretty (Block stmts) = braces (line <> indent 2 (vsep (map pretty stmts)) <> line)

-- Pretty instance for AnnotatedNode (expressions, JSX nodes, JSX children)
instance Pretty AnnotatedNode where
  pretty (_ :< LangFExpr expr) = prettyExprF expr
  pretty (_ :< LangFJSXNode jsx) = prettyJSXNodeF jsx
  pretty (_ :< LangFJSXChild child) = prettyJSXChildF child

-- Helper functions for pretty printing F-algebras

prettyExprF :: ExprF AnnotatedNode -> Doc ann
-- Special case for infix operators
prettyExprF (EAppF (_ :< LangFExpr (EAppF (_ :< LangFExpr (EVarF op)) x)) y)
  | isInfixOp (Text.unpack op) = parens $ pretty x <+> pretty op <+> pretty y
  where
    isInfixOp n = n `elem` infixOps
    infixOps = ["+","-","*","/","==","!=","===","!==","<","<=",">",">=","&&","||","++","mod","xor","or","and", ";;"]
prettyExprF (EVarF n) = pretty n
prettyExprF (ELitIntF n) = viaShow n
prettyExprF (ELitStringF s) = dquotes (pretty s)
prettyExprF (ELitBoolF True) = "true"
prettyExprF (ELitBoolF False) = "false"
prettyExprF (EJSXNodeF node) = pretty node
prettyExprF (EArrowF _ param Nothing body) =
  parens $ pretty param <+> "=>" <+> pretty body
prettyExprF (EArrowF _ param (Just sch) body) =
  parens $ pretty param <> ":" <+> pretty sch <+> "=>" <+> pretty body
prettyExprF (EAppF f x) = pretty f <+> pretty x
prettyExprF (EIfF cond thenExpr elseExpr) =
  pretty cond <+> "?" <+> pretty thenExpr <+> ":" <+> pretty elseExpr
prettyExprF (EEffectF eff) = "effect" <+> pretty eff
prettyExprF (EPairF e1 e2) = pretty e1 <+> "," <+> pretty e2
prettyExprF (EPairAccessF e ix) = pretty e <> "." <> pretty ix
prettyExprF (EBindF lbl e) = "bind" <+> pretty lbl <+> pretty e
prettyExprF (EOnceF lbl e) = "once" <+> pretty lbl <+> pretty e
prettyExprF (ECancelF lbl) = "cancel" <+> pretty lbl
prettyExprF (ERemoveF lbl) = "remove" <+> pretty lbl

prettyJSXNodeF :: JSXNodeF AnnotatedNode -> Doc ann
prettyJSXNodeF (JSXElementNodeF tag [] children) =
  "<"
    <> pretty tag
    <> ">"
    <> line
    <> indent 2 (vsep (map pretty children))
    <> line
    <> "</"
    <> pretty tag
    <> ">"
prettyJSXNodeF (JSXElementNodeF tag attrs children) =
  "<"
    <> pretty tag
    <+> hsep (map pretty attrs)
    <> ">"
    <> line
    <> indent 2 (vsep (map pretty children))
    <> line
    <> "</"
    <> pretty tag
    <> ">"
prettyJSXNodeF (JSXSelfClosingNodeF tag []) =
  "<" <> pretty tag <> "/>"
prettyJSXNodeF (JSXSelfClosingNodeF tag attrs) =
  "<" <> pretty tag <+> hsep (map pretty attrs) <> "/>"

prettyJSXChildF :: JSXChildF AnnotatedNode -> Doc ann
prettyJSXChildF (ChildTextF text) = dquotes (pretty text)
prettyJSXChildF (ChildExprF expr) = braces (pretty expr)
prettyJSXChildF (ChildNodeF node) = pretty node

instance Pretty JSXAttr where
  pretty (JSXAttr (n, value)) = pretty n <> "=" <> pretty value

instance Pretty JSXAttrValue where
  pretty (JSXAttrString s) = dquotes (pretty s)
  pretty (JSXAttrExpr e) = braces (pretty e)

-- First, we need Show, Eq, Ord instances for AnnotatedNode (Cofree LangF NodeAnnotation)
-- These are derived automatically but we need to ensure they exist before using them

-- Standalone functions for JSXAttr and JSXAttrValue instances

-- JSXAttr functions
showJSXAttr :: JSXAttr -> String
showJSXAttr (JSXAttr (n, v)) = "JSXAttr (" ++ show n ++ "," ++ show v ++ ")"

eqJSXAttr :: JSXAttr -> JSXAttr -> Bool
eqJSXAttr (JSXAttr (n1, v1)) (JSXAttr (n2, v2)) = n1 == n2 && v1 == v2

compareJSXAttr :: JSXAttr -> JSXAttr -> Ordering
compareJSXAttr (JSXAttr (n1, v1)) (JSXAttr (n2, v2)) = compare (n1, v1) (n2, v2)

-- JSXAttrValue functions (depends on AnnotatedNode having Show/Eq/Ord)
showJSXAttrValue :: JSXAttrValue -> String
showJSXAttrValue (JSXAttrString s) = "JSXAttrString " ++ show s
showJSXAttrValue (JSXAttrExpr e) = "JSXAttrExpr (" ++ showAnnotatedNode e ++ ")"

eqJSXAttrValue :: JSXAttrValue -> JSXAttrValue -> Bool
eqJSXAttrValue (JSXAttrString s1) (JSXAttrString s2) = s1 == s2
eqJSXAttrValue (JSXAttrExpr e1) (JSXAttrExpr e2) = eqAnnotatedNode e1 e2
eqJSXAttrValue _ _ = False

compareJSXAttrValue :: JSXAttrValue -> JSXAttrValue -> Ordering
compareJSXAttrValue (JSXAttrString s1) (JSXAttrString s2) = compare s1 s2
compareJSXAttrValue (JSXAttrExpr e1) (JSXAttrExpr e2) = compareAnnotatedNode e1 e2
compareJSXAttrValue (JSXAttrString _) (JSXAttrExpr _) = LT
compareJSXAttrValue (JSXAttrExpr _) (JSXAttrString _) = GT

-- Block functions (depends on AnnotatedNode having Show)
showBlock :: Block -> String
showBlock (Block stmts) = "Block [" ++ intercalate "," (map showAnnotatedNode stmts) ++ "]"

eqBlock :: Block -> Block -> Bool
eqBlock (Block stmts1) (Block stmts2) = length stmts1 == length stmts2 && all (uncurry eqAnnotatedNode) (zip stmts1 stmts2)

compareBlock :: Block -> Block -> Ordering
compareBlock (Block stmts1) (Block stmts2) = compareAnnotatedNodeList stmts1 stmts2
  where
    compareAnnotatedNodeList [] [] = EQ
    compareAnnotatedNodeList [] _ = LT
    compareAnnotatedNodeList _ [] = GT
    compareAnnotatedNodeList (x:xs) (y:ys) =
      case compareAnnotatedNode x y of
        EQ -> compareAnnotatedNodeList xs ys
        other -> other

-- AnnotatedNode functions (Cofree LangF NodeAnnotation)
showAnnotatedNode :: AnnotatedNode -> String
showAnnotatedNode (ann :< langF) = "(" ++ show ann ++ " :< " ++ showLangF langF ++ ")"

eqAnnotatedNode :: AnnotatedNode -> AnnotatedNode -> Bool
eqAnnotatedNode (ann1 :< langF1) (ann2 :< langF2) = ann1 == ann2 && eqLangF langF1 langF2

compareAnnotatedNode :: AnnotatedNode -> AnnotatedNode -> Ordering
compareAnnotatedNode (ann1 :< langF1) (ann2 :< langF2) =
  compare ann1 ann2 <> compareLangF langF1 langF2

-- LangF functions
showLangF :: LangF AnnotatedNode -> String
showLangF (LangFExpr e) = "LangFExpr (" ++ showExprF e ++ ")"
showLangF (LangFJSXNode n) = "LangFJSXNode (" ++ showJSXNodeF n ++ ")"
showLangF (LangFJSXChild c) = "LangFJSXChild (" ++ showJSXChildF c ++ ")"

eqLangF :: LangF AnnotatedNode -> LangF AnnotatedNode -> Bool
eqLangF (LangFExpr e1) (LangFExpr e2) = eqExprF e1 e2
eqLangF (LangFJSXNode n1) (LangFJSXNode n2) = eqJSXNodeF n1 n2
eqLangF (LangFJSXChild c1) (LangFJSXChild c2) = eqJSXChildF c1 c2
eqLangF _ _ = False

compareLangF :: LangF AnnotatedNode -> LangF AnnotatedNode -> Ordering
compareLangF (LangFExpr e1) (LangFExpr e2) = compareExprF e1 e2
compareLangF (LangFJSXNode n1) (LangFJSXNode n2) = compareJSXNodeF n1 n2
compareLangF (LangFJSXChild c1) (LangFJSXChild c2) = compareJSXChildF c1 c2
compareLangF a b = compare (tagLangF a) (tagLangF b)
  where
    tagLangF (LangFExpr{}) = 0 :: Int
    tagLangF (LangFJSXNode{}) = 1
    tagLangF (LangFJSXChild{}) = 2

-- ExprF functions
showExprF :: ExprF AnnotatedNode -> String
showExprF (EVarF n) = "EVarF " ++ show n
showExprF (ELitIntF i) = "ELitIntF " ++ show i
showExprF (ELitStringF s) = "ELitStringF " ++ show s
showExprF (ELitBoolF b) = "ELitBoolF " ++ show b
showExprF (EJSXNodeF n) = "EJSXNodeF (" ++ showAnnotatedNode n ++ ")"
showExprF (EArrowF effs p mt b) = "EArrowF " ++ show effs ++ " " ++ show p ++ " " ++ show mt ++ " (" ++ showAnnotatedNode b ++ ")"
showExprF (EAppF f x) = "EAppF (" ++ showAnnotatedNode f ++ ") (" ++ showAnnotatedNode x ++ ")"
showExprF (EIfF c t e) = "EIfF (" ++ showAnnotatedNode c ++ ") (" ++ showAnnotatedNode t ++ ") (" ++ showAnnotatedNode e ++ ")"
showExprF (EEffectF eff) = "EEffectF " ++ show eff
showExprF (EPairF a b) = "EPairF (" ++ showAnnotatedNode a ++ ") (" ++ showAnnotatedNode b ++ ")"
showExprF (EPairAccessF e ix) = "EPairAccessF (" ++ showAnnotatedNode e ++ ") " ++ show ix
showExprF (EBindF lbl e) = "EBindF " ++ show lbl ++ " (" ++ showAnnotatedNode e ++ ")"
showExprF (EOnceF lbl e) = "EOnceF " ++ show lbl ++ " (" ++ showAnnotatedNode e ++ ")"
showExprF (ECancelF lbl) = "ECancelF " ++ show lbl
showExprF (ERemoveF lbl) = "ERemoveF " ++ show lbl

eqExprF :: ExprF AnnotatedNode -> ExprF AnnotatedNode -> Bool
eqExprF (EVarF n1) (EVarF n2) = n1 == n2
eqExprF (ELitIntF i1) (ELitIntF i2) = i1 == i2
eqExprF (ELitStringF s1) (ELitStringF s2) = s1 == s2
eqExprF (ELitBoolF b1) (ELitBoolF b2) = b1 == b2
eqExprF (EJSXNodeF n1) (EJSXNodeF n2) = eqAnnotatedNode n1 n2
eqExprF (EArrowF effs1 p1 mt1 b1) (EArrowF effs2 p2 mt2 b2) = effs1 == effs2 && p1 == p2 && mt1 == mt2 && eqAnnotatedNode b1 b2
eqExprF (EAppF f1 x1) (EAppF f2 x2) = eqAnnotatedNode f1 f2 && eqAnnotatedNode x1 x2
eqExprF (EIfF c1 t1 e1) (EIfF c2 t2 e2) = eqAnnotatedNode c1 c2 && eqAnnotatedNode t1 t2 && eqAnnotatedNode e1 e2
eqExprF (EEffectF eff1) (EEffectF eff2) = eff1 == eff2
eqExprF (EPairF a1 b1) (EPairF a2 b2) = eqAnnotatedNode a1 a2 && eqAnnotatedNode b1 b2
eqExprF (EPairAccessF e1 ix1) (EPairAccessF e2 ix2) = eqAnnotatedNode e1 e2 && ix1 == ix2
eqExprF (EBindF l1 e1) (EBindF l2 e2) = l1 == l2 && eqAnnotatedNode e1 e2
eqExprF (EOnceF l1 e1) (EOnceF l2 e2) = l1 == l2 && eqAnnotatedNode e1 e2
eqExprF (ECancelF l1) (ECancelF l2) = l1 == l2
eqExprF (ERemoveF l1) (ERemoveF l2) = l1 == l2
eqExprF _ _ = False

compareExprF :: ExprF AnnotatedNode -> ExprF AnnotatedNode -> Ordering
compareExprF (EVarF n1) (EVarF n2) = compare n1 n2
compareExprF (ELitIntF i1) (ELitIntF i2) = compare i1 i2
compareExprF (ELitStringF s1) (ELitStringF s2) = compare s1 s2
compareExprF (ELitBoolF b1) (ELitBoolF b2) = compare b1 b2
compareExprF (EJSXNodeF n1) (EJSXNodeF n2) = compareAnnotatedNode n1 n2
compareExprF (EArrowF effs1 p1 mt1 b1) (EArrowF effs2 p2 mt2 b2) =
  compare (effs1, p1, mt1) (effs2, p2, mt2) <> compareAnnotatedNode b1 b2
compareExprF (EAppF f1 x1) (EAppF f2 x2) = compareAnnotatedNode f1 f2 <> compareAnnotatedNode x1 x2
compareExprF (EIfF c1 t1 e1) (EIfF c2 t2 e2) = compareAnnotatedNode c1 c2 <> compareAnnotatedNode t1 t2 <> compareAnnotatedNode e1 e2
compareExprF (EEffectF eff1) (EEffectF eff2) = compare eff1 eff2
compareExprF (EPairF a1 b1) (EPairF a2 b2) = compareAnnotatedNode a1 a2 <> compareAnnotatedNode b1 b2
compareExprF (EPairAccessF e1 ix1) (EPairAccessF e2 ix2) = compareAnnotatedNode e1 e2 <> compare ix1 ix2
compareExprF (EBindF l1 e1) (EBindF l2 e2) = compare l1 l2 <> compareAnnotatedNode e1 e2
compareExprF (EOnceF l1 e1) (EOnceF l2 e2) = compare l1 l2 <> compareAnnotatedNode e1 e2
compareExprF (ECancelF l1) (ECancelF l2) = compare l1 l2
compareExprF (ERemoveF l1) (ERemoveF l2) = compare l1 l2
compareExprF a b = compare (tagExprF a) (tagExprF b)
  where
    tagExprF (EVarF{}) = 0 :: Int
    tagExprF (ELitIntF{}) = 1
    tagExprF (ELitStringF{}) = 2
    tagExprF (ELitBoolF{}) = 3
    tagExprF (EJSXNodeF{}) = 4
    tagExprF (EArrowF{}) = 5
    tagExprF (EAppF{}) = 6
    tagExprF (EIfF{}) = 7
    tagExprF (EEffectF{}) = 8
    tagExprF (EPairF{}) = 9
    tagExprF (EPairAccessF{}) = 10
    tagExprF (EBindF{}) = 11
    tagExprF (EOnceF{}) = 12
    tagExprF (ECancelF{}) = 13
    tagExprF (ERemoveF{}) = 14

-- JSXNodeF functions
showJSXNodeF :: JSXNodeF AnnotatedNode -> String
showJSXNodeF (JSXElementNodeF tag attrs children) =
  "JSXElementNodeF " ++ show tag ++ " " ++ show attrs ++ " [" ++ intercalate "," (map showAnnotatedNode children) ++ "]"
showJSXNodeF (JSXSelfClosingNodeF tag attrs) =
  "JSXSelfClosingNodeF " ++ show tag ++ " " ++ show attrs

eqJSXNodeF :: JSXNodeF AnnotatedNode -> JSXNodeF AnnotatedNode -> Bool
eqJSXNodeF (JSXElementNodeF t1 a1 c1) (JSXElementNodeF t2 a2 c2) =
  t1 == t2 && a1 == a2 && length c1 == length c2 && and (zipWith eqAnnotatedNode c1 c2)
eqJSXNodeF (JSXSelfClosingNodeF t1 a1) (JSXSelfClosingNodeF t2 a2) = t1 == t2 && a1 == a2
eqJSXNodeF _ _ = False

compareJSXNodeF :: JSXNodeF AnnotatedNode -> JSXNodeF AnnotatedNode -> Ordering
compareJSXNodeF (JSXElementNodeF t1 a1 c1) (JSXElementNodeF t2 a2 c2) =
  compare (t1, a1) (t2, a2) <> compare (length c1) (length c2) <> mconcat (zipWith compareAnnotatedNode c1 c2)
compareJSXNodeF (JSXSelfClosingNodeF t1 a1) (JSXSelfClosingNodeF t2 a2) = compare (t1, a1) (t2, a2)
compareJSXNodeF a b = compare (tagJSXNodeF a) (tagJSXNodeF b)
  where
    tagJSXNodeF (JSXElementNodeF{}) = 0 :: Int
    tagJSXNodeF (JSXSelfClosingNodeF{}) = 1

-- JSXChildF functions
showJSXChildF :: JSXChildF AnnotatedNode -> String
showJSXChildF (ChildTextF t) = "ChildTextF " ++ show t
showJSXChildF (ChildExprF e) = "ChildExprF (" ++ showAnnotatedNode e ++ ")"
showJSXChildF (ChildNodeF n) = "ChildNodeF (" ++ showAnnotatedNode n ++ ")"

eqJSXChildF :: JSXChildF AnnotatedNode -> JSXChildF AnnotatedNode -> Bool
eqJSXChildF (ChildTextF t1) (ChildTextF t2) = t1 == t2
eqJSXChildF (ChildExprF e1) (ChildExprF e2) = eqAnnotatedNode e1 e2
eqJSXChildF (ChildNodeF n1) (ChildNodeF n2) = eqAnnotatedNode n1 n2
eqJSXChildF _ _ = False

compareJSXChildF :: JSXChildF AnnotatedNode -> JSXChildF AnnotatedNode -> Ordering
compareJSXChildF (ChildTextF t1) (ChildTextF t2) = compare t1 t2
compareJSXChildF (ChildExprF e1) (ChildExprF e2) = compareAnnotatedNode e1 e2
compareJSXChildF (ChildNodeF n1) (ChildNodeF n2) = compareAnnotatedNode n1 n2
compareJSXChildF a b = compare (tagJSXChildF a) (tagJSXChildF b)
  where
    tagJSXChildF (ChildTextF{}) = 0 :: Int
    tagJSXChildF (ChildExprF{}) = 1
    tagJSXChildF (ChildNodeF{}) = 2

-- AnnotatedNode automatically gets Show, Eq, Ord instances from Cofree
-- No need to define explicit instances as they would overlap

-- Instance declarations using the standalone functions
instance Show JSXAttr where
  show = showJSXAttr

instance Eq JSXAttr where
  (==) = eqJSXAttr

instance Ord JSXAttr where
  compare = compareJSXAttr

instance Show JSXAttrValue where
  show = showJSXAttrValue

instance Eq JSXAttrValue where
  (==) = eqJSXAttrValue

instance Ord JSXAttrValue where
  compare = compareJSXAttrValue

instance Show Block where
  show = showBlock

instance Eq Block where
  (==) = eqBlock

instance Ord Block where
  compare = compareBlock

-- | Σ as a per-component Δ table. The component's own source is deliberately
-- NOT echoed here: @--verbose@ already prints the whole parsed program, and
-- repeating it buried the inferred effects, which are the point of this table.
instance Pretty Sigma where
  pretty (Sigma sigmaMap) = vsep $ map prettySigmaEntry (Map.toList sigmaMap)
    where
      prettySigmaEntry (n, SigmaEntry _comp delta) =
        "comp" <+> pretty n <> line <> indent 2 (pretty delta)

-- Helper functions for constructing annotated nodes
-- These will make it easier to migrate from the old constructors

-- Create a dummy annotation for nodes that don't have source info yet
dummyNodeAnnotation :: NodeAnnotation
dummyNodeAnnotation = NodeAnnotation
  { annNodeSpan = dummySpan
  , annType = TUnit      -- Will be overwritten by type checker
  , annEffect = EffNone  -- Will be overwritten by type checker
  }

-- Create a dummy span for nodes without source info
dummySpan :: Span
dummySpan = Span dummyPos dummyPos
  where
    dummyPos = SourcePos "<unknown>" (mkPos 1) (mkPos 1)

-- Create a dummy source annotation
dummySourceAnn :: SourceAnnotation
dummySourceAnn = SourceAnnotation dummySpan

-- Helper constructor functions that add dummy annotations
-- These can be used during migration to make minimal changes to existing code

mkVar :: Maybe NodeAnnotation -> Text -> AnnotatedNode
mkVar Nothing name = dummyNodeAnnotation :< LangFExpr (EVarF name)
mkVar (Just s) name = s :< LangFExpr (EVarF name)

mkLitInt :: Maybe NodeAnnotation -> Integer -> AnnotatedNode
mkLitInt Nothing n = dummyNodeAnnotation :< LangFExpr (ELitIntF n)
mkLitInt (Just s) n = s :< LangFExpr (ELitIntF n)

mkLitString :: Maybe NodeAnnotation -> Text -> AnnotatedNode
mkLitString Nothing s = dummyNodeAnnotation :< LangFExpr (ELitStringF s)
mkLitString (Just ann) s = ann :< LangFExpr (ELitStringF s)

mkLitBool :: Maybe NodeAnnotation -> Bool -> AnnotatedNode
mkLitBool Nothing b = dummyNodeAnnotation :< LangFExpr (ELitBoolF b)
mkLitBool (Just s) b = s :< LangFExpr (ELitBoolF b)

mkApp :: Maybe NodeAnnotation -> AnnotatedNode -> AnnotatedNode -> AnnotatedNode
mkApp Nothing f x = dummyNodeAnnotation :< LangFExpr (EAppF f x)
mkApp (Just s) f x = s :< LangFExpr (EAppF f x)

mkIf :: Maybe NodeAnnotation -> AnnotatedNode -> AnnotatedNode -> AnnotatedNode -> AnnotatedNode
mkIf Nothing cond t e = dummyNodeAnnotation :< LangFExpr (EIfF cond t e)
mkIf (Just s) cond t e = s :< LangFExpr (EIfF cond t e)

mkArrow :: Maybe NodeAnnotation -> Text -> Maybe Type -> AnnotatedNode -> AnnotatedNode
mkArrow Nothing param schema body = dummyNodeAnnotation :< LangFExpr (EArrowF [] param schema body)
mkArrow (Just s) param schema body = s :< LangFExpr (EArrowF [] param schema body)

mkEffect :: Maybe NodeAnnotation -> Effect -> AnnotatedNode
mkEffect Nothing eff = dummyNodeAnnotation :< LangFExpr (EEffectF eff)
mkEffect (Just s) eff = s :< LangFExpr (EEffectF eff)

mkPair :: Maybe NodeAnnotation -> AnnotatedNode -> AnnotatedNode -> AnnotatedNode
mkPair Nothing e1 e2 = dummyNodeAnnotation :< LangFExpr (EPairF e1 e2)
mkPair (Just s) e1 e2 = s :< LangFExpr (EPairF e1 e2)

mkPairAccess :: Maybe NodeAnnotation -> AnnotatedNode -> Int -> AnnotatedNode
mkPairAccess Nothing e ix = dummyNodeAnnotation :< LangFExpr (EPairAccessF e ix)
mkPairAccess (Just s) e ix = s :< LangFExpr (EPairAccessF e ix)

-- JSX helpers
mkJSXElement :: Maybe NodeAnnotation -> Text -> [JSXAttr] -> [AnnotatedNode] -> AnnotatedNode
mkJSXElement Nothing tag attrs children = dummyNodeAnnotation :< LangFJSXNode (JSXElementNodeF tag attrs children)
mkJSXElement (Just s) tag attrs children = s :< LangFJSXNode (JSXElementNodeF tag attrs children)

mkJSXSelfClosing :: Maybe NodeAnnotation -> Text -> [JSXAttr] -> AnnotatedNode
mkJSXSelfClosing Nothing tag attrs = dummyNodeAnnotation :< LangFJSXNode (JSXSelfClosingNodeF tag attrs)
mkJSXSelfClosing (Just s) tag attrs = s :< LangFJSXNode (JSXSelfClosingNodeF tag attrs)

mkChildText :: Maybe NodeAnnotation -> Text -> AnnotatedNode
mkChildText Nothing text = dummyNodeAnnotation :< LangFJSXChild (ChildTextF text)
mkChildText (Just s) text = s :< LangFJSXChild (ChildTextF text)

mkChildExpr :: Maybe NodeAnnotation -> AnnotatedNode -> AnnotatedNode
mkChildExpr Nothing expr = dummyNodeAnnotation :< LangFJSXChild (ChildExprF expr)
mkChildExpr (Just s) expr = s :< LangFJSXChild (ChildExprF expr)

mkChildNode :: Maybe NodeAnnotation -> AnnotatedNode -> AnnotatedNode
mkChildNode Nothing node = dummyNodeAnnotation :< LangFJSXChild (ChildNodeF node)
mkChildNode (Just s) node = s :< LangFJSXChild (ChildNodeF node)

mkJSXNode :: Maybe NodeAnnotation -> AnnotatedNode -> AnnotatedNode
mkJSXNode Nothing node = dummyNodeAnnotation :< LangFExpr (EJSXNodeF node)
mkJSXNode (Just s) node = s :< LangFExpr (EJSXNodeF node)

-- Declaration helpers
mkDeclState :: Text -> Text -> AnnotatedNode -> AnnotatedDeclaration
mkDeclState var setter expr = dummySourceAnn :< DeclStateF var setter expr

mkDeclEffect :: [Text] -> Block -> AnnotatedDeclaration
mkDeclEffect deps block = dummySourceAnn :< DeclEffectF deps block

mkDeclLet :: Maybe SourceAnnotation -> Text -> Maybe Type -> AnnotatedNode -> AnnotatedDeclaration
mkDeclLet mAnnot var mType expr = fromMaybe dummySourceAnn mAnnot :< DeclLetF var mType expr

mkDeclSubComp :: Text -> Text -> Maybe [Maybe Effect] -> [Text] -> AnnotatedDeclaration
mkDeclSubComp inst comp effs args = dummySourceAnn :< DeclSubCompF inst comp effs args

-- Component helper
mkComponent :: Text -> [EffVarName] -> [(Text, Type)] -> [AnnotatedDeclaration] -> Text -> Type -> AnnotatedComponent
mkComponent name effParams args decls ret retType =
  dummySourceAnn :< ComponentF name effParams args decls ret retType

-- Event declaration helper
mkEventDecl :: Maybe SourceAnnotation -> EventLabel -> Type -> AnnotatedEventDecl
mkEventDecl mAnnot lbl ty = fromMaybe dummySourceAnn mAnnot :< EventDeclF lbl ty

-- Program helper
mkProgram :: [AnnotatedEventDecl] -> [AnnotatedComponent] -> AnnotatedProgram
mkProgram eventDecls comps = dummySourceAnn :< ProgramF eventDecls comps

-- Helper functions for extracting data from Cofree-based AST
getComponents :: AnnotatedProgram -> [AnnotatedComponent]
getComponents (_ :< ProgramF _ comps) = comps

getEventDecls :: AnnotatedProgram -> [AnnotatedEventDecl]
getEventDecls (_ :< ProgramF eventDecls _) = eventDecls

getComponentName :: AnnotatedComponent -> Text
getComponentName (_ :< ComponentF name _ _ _ _ _) = name

getComponentArgs :: AnnotatedComponent -> [(Text, Type)]
getComponentArgs (_ :< ComponentF _ _ args _ _ _) = args

unDelta :: Delta -> Map Text DeltaEntry
unDelta (Delta d) = d

instance Pretty Span where
  pretty s = pretty (prettySpan s)

-- | Helper to extract span from AnnotatedNode
getNodeSpan :: AnnotatedNode -> Span
getNodeSpan (NodeAnnotation span _ _ :< _) = span

-- | Extract source span from a Component
getComponentSpan :: Component -> Span
getComponentSpan (annotation :< _) = annSourceSpan annotation

-- | Extract source span from a Declaration
getDeclarationSpan :: Declaration -> Span
getDeclarationSpan (annotation :< _) = annSourceSpan annotation

-- | Create a typed expression node
mkTypedExpr :: Span -> Type -> Effect -> ExprF AnnotatedNode -> AnnotatedNode
mkTypedExpr span schema eff exprF = NodeAnnotation span schema eff :< LangFExpr exprF

-- | Create a simple typed expression with no effect
mkSimpleTypedExpr :: Span -> Type -> ExprF AnnotatedNode -> AnnotatedNode
mkSimpleTypedExpr span ty = mkTypedExpr span ty EffNone

-- | Create a simple typed node (general)
mkSimpleTypedNode :: Span -> Type -> LangF AnnotatedNode -> AnnotatedNode
mkSimpleTypedNode span ty langF = NodeAnnotation span ty EffNone :< langF


