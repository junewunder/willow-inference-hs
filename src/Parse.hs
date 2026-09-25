
-- | Parser for annotated AST with source position information
module Parse
  ( AnnotatedParser,
    pProgram,
    pExpr,
    pJSXElement,
    pComponent,
    pDecl,
    pBlock,
    withSourceInfo,
    pType,
    pEffect,
  )
where

import Control.Comonad.Cofree
import Control.Monad.Combinators
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)
import Data.Either (partitionEithers)
import RIO hiding (many, try, some)
import RIO.Char (isSpace)
import RIO.Text (pack, strip)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Types
import Util


type AnnotatedParser = Parsec Void Text

-- | Space consumer (now supports nested block comments)
sc :: AnnotatedParser ()
sc = L.space space1 (L.skipLineComment "//") (L.skipBlockCommentNested "/*" "*/")

-- | A helper to consume whitespace after a parser
lexeme :: AnnotatedParser a -> AnnotatedParser a
lexeme = L.lexeme sc

-- | A helper to parse a text symbol and consume whitespace
symbol :: Text -> AnnotatedParser Text
symbol = L.symbol sc

-- | Parse parentheses
parens :: AnnotatedParser a -> AnnotatedParser a
parens = between (symbol "(") (symbol ")")

-- | Parse braces
braces :: AnnotatedParser a -> AnnotatedParser a
braces = between (symbol "{") (symbol "}")

-- | Integer parser (handles optional sign)
integer :: AnnotatedParser Integer
integer = lexeme (L.signed sc L.decimal)

-- | Helper to capture source position information for expressions
withSourceInfo :: AnnotatedParser (ExprF AnnotatedNode) -> AnnotatedParser AnnotatedNode
withSourceInfo parser = do
  startPos <- getSourcePos
  content <- parser
  endPos <- getSourcePos
  let sourceSpan = Span startPos endPos
      nodeAnnotation = NodeAnnotation sourceSpan
        TUnit
        EffNone  -- Dummy schema/effect, will be filled by type checker
  return $ nodeAnnotation :< LangFExpr content

-- | Helper to capture source position information for JSX nodes
withJSXSourceInfo :: AnnotatedParser (JSXNodeF AnnotatedNode) -> AnnotatedParser AnnotatedNode
withJSXSourceInfo parser = do
  startPos <- getSourcePos
  content <- parser
  endPos <- getSourcePos
  let sourceSpan = Span startPos endPos
      nodeAnnotation = NodeAnnotation sourceSpan TUnit EffNone
  return $ nodeAnnotation :< LangFJSXNode content

-- | Helper to capture source position information for JSX children
withJSXChildSourceInfo :: AnnotatedParser (JSXChildF AnnotatedNode) -> AnnotatedParser AnnotatedNode
withJSXChildSourceInfo parser = do
  startPos <- getSourcePos
  content <- parser
  endPos <- getSourcePos
  let sourceSpan = Span startPos endPos
      nodeAnnotation = NodeAnnotation sourceSpan TUnit EffNone
  return $ nodeAnnotation :< LangFJSXChild content

-- | Helper to get annotation from an AnnotatedNode
getNodeAnnotation :: AnnotatedNode -> NodeAnnotation
getNodeAnnotation (ann :< _) = ann

-- | Helper to get source position information from an AnnotatedNode
getSourceInfo :: AnnotatedNode -> NodeAnnotation
getSourceInfo = getNodeAnnotation

-- | List of reserved keywords
reservedKeywords :: [Text]
reservedKeywords =
  [ "comp", "state", "on", "do", "let", "return", "default",
    "true", "false", "string", "int", "bool", "none", "loop",
    "after", "effect", "r", "n"
  ]

-- | Parse an identifier
pIdentifier :: AnnotatedParser Text
pIdentifier = lexeme $ do
  firstChar <- letterChar
  rest <- many $ try $ do
    -- Look ahead for .0 or .1 and stop if found
    notFollowedBy (lookAhead (char '.' *> (char '0' <|> char '1')))
    alphaNumChar <|> char '.'
  let ident = pack (firstChar : rest)
  if ident `elem` reservedKeywords
    then fail $ "keyword " ++ show ident ++ " cannot be an identifier"
    else return ident

pIdentifierNoDot :: AnnotatedParser Text
pIdentifierNoDot = lexeme $ do
  firstChar <- letterChar
  rest <- many $ try $ do
    alphaNumChar
  let ident = pack (firstChar : rest)
  if ident `elem` reservedKeywords
    then fail $ "keyword " ++ show ident ++ " cannot be an identifier"
    else return ident

-- | Parse annotated program: an interleavable sequence of event declarations
-- (@event ℓ⟨v⟩ : τ;@) and components, partitioned into the two lists.
pProgram :: AnnotatedParser Program
pProgram = do
  sc
  declsOrComps <- many (try (Left <$> pEventDecl) <|> (Right <$> pComponent))
  sc
  eof
  let (eventDecls, components) = partitionEithers declsOrComps
  return $ mkProgram eventDecls components

-- | Parse an event declaration: @event ℓ⟨v⟩ : τ;@. 'event' is a
-- contextual keyword (NOT in 'reservedKeywords'): 'pModalityKeyword' requires
-- an identifier boundary, and 'pProgram' wraps the whole decl in 'try', so a
-- component named e.g. @eventHandler@ still parses as a component.
pEventDecl :: AnnotatedParser AnnotatedEventDecl
pEventDecl = do
  startPos <- getSourcePos
  _ <- pModalityKeyword "event"
  lbl <- pEventLabel
  _ <- symbol ":"
  ty <- pType
  _ <- symbol ";"
  endPos <- getSourcePos
  return $ SourceAnnotation (Span startPos endPos) :< EventDeclF lbl ty

-- | Parse annotated component
pComponent :: AnnotatedParser Component
pComponent = do
  startPos <- getSourcePos
  _ <- symbol "comp" <?> "component declaration (comp)"
  compNameParsed <- pIdentifier <?> "component name"
  effectParamsParsed <- option [] $ do
    _ <- symbol "<"
    params <- pIdentifier `sepBy1` symbol ","
    _ <- symbol ">"
    return params
  let effectParams = map EffVarName effectParamsParsed
  args <- parens (pArg `sepBy` symbol ",") <?> "component argument list"
  _ <- symbol ":" <?> "colon before return type"
  mType <- pType <?> "component return mType"
  -- The component's span is its header, up to the return type.
  headerEnd <- getSourcePos
  _ <- bracesOpen <?> "opening brace for component body"
  decls <- parseAnnotatedDeclsOrFail
  _ <- symbol "return" <?> "return statement in component body"
  retExpr <- pExpr <?> "return expression"
  _ <- symbol ";" <?> "semicolon after return statement"
  _ <- bracesClose <?> "closing brace for component body"
  let (finalDecls, retVar) =
        case retExpr of
          _ :< LangFExpr (EVarF v) -> (decls, v)
          nAnnot :< _ ->
            let sAnnot = SourceAnnotation (annNodeSpan nAnnot) in
            (decls ++ [mkDeclLet (Just sAnnot) "returnVar" Nothing retExpr], "returnVar")
  let _ :< compF = mkComponent compNameParsed effectParams args finalDecls retVar mType
  return $ SourceAnnotation (Span startPos headerEnd) :< compF

-- | Helper to parse component arguments
pArg :: AnnotatedParser (Text, Type)
pArg = (,) <$> pIdentifier <* symbol ":" <*> pType

-- | Helper parsers for braces
bracesOpen :: AnnotatedParser Text
bracesOpen = symbol "{"

bracesClose :: AnnotatedParser Text
bracesClose = symbol "}"

-- | Parse sequence of annotated declarations
parseAnnotatedDeclsOrFail :: AnnotatedParser [Declaration]
parseAnnotatedDeclsOrFail = go []
  where
    go acc = do
      next <- lookAhead (optional (choice [symbol "on", symbol "state", symbol "let", symbol "comp", symbol "return"]))
      case next of
        Just "return" -> return (reverse acc)
        Just _ -> do
          declList <- pDecl <?> "component declaration (state, let, on, comp)"
          go (reverse declList ++ acc)
        Nothing -> fail "Expected a declaration (state, let, on, comp) or return statement in component body."

-- | Parse annotated declaration (now returns a list to handle expression arguments)
pDecl :: AnnotatedParser [Declaration]
pDecl = choice
  [ do
      startPos <- getSourcePos
      _ <- symbol "state"
      var <- pIdentifier
      _ <- symbol ","
      setter <- pIdentifier
      _ <- symbol "default"
      val <- pExprTop
      endPos <- getSourcePos
      _ <- symbol ";"
      return [setDeclSpan (Span startPos endPos) (mkDeclState var setter val)]
  , do
      _ <- symbol "let"
      -- Try destructuring pattern first, then regular let
      choice
        [ do
            vars <- parens (pIdentifier `sepBy1` symbol ",")
            _ <- symbol "="
            val <- pExprTop
            _ <- symbol ";"
            return $ generateDestructuringDecls vars val
        , do
            var <- pIdentifier
            mSchema <- optional (symbol ":" *> pType)
            _ <- symbol "="
            val <- pExprTop
            _ <- symbol ";"
            let valAnnotation = SourceAnnotation $ annNodeSpan $ getNodeAnnotation val
            return [mkDeclLet (Just valAnnotation) var mSchema val]
        ]
  , do
      -- An @on@ declaration's span is its head, @on x, y@: the block's
      -- statements carry their own.
      startPos <- getSourcePos
      _ <- symbol "on"
      deps <- pIdentifier `sepBy1` symbol ","
      endPos <- getSourcePos
      _ <- symbol "do"
      effect <- mkDeclEffect deps <$> pBlock
      _ <- optional $ symbol ";"
      return [setDeclSpan (Span startPos endPos) effect]
  , do
      startPos <- getSourcePos
      _ <- symbol "comp"
      inst <- pIdentifier
      _ <- symbol "="
      cname <- pIdentifier
      effs <- optional $ do
        _ <- symbol "<"
        es <- (Nothing <$ symbol "?" <|> Just <$> pEffect) `sepBy` symbol ","
        _ <- symbol ">"
        return es
      args <- parens (pCompArg `sepBy` symbol ",")
      endPos <- getSourcePos
      _ <- symbol ";"
      let (letDecls, argNames) = processCompArgs inst args
          instDecl = setDeclSpan (Span startPos endPos) (mkDeclSubComp inst cname effs argNames)
      return $ letDecls ++ [instDecl]
  ]

-- | Give a declaration its source span. The span ends before the closing
-- @;@ (or, for @on@, before @do@), whose lexeme would carry it past the
-- trailing whitespace onto the next line.
setDeclSpan :: Span -> Declaration -> Declaration
setDeclSpan sp (_ :< declF) = SourceAnnotation sp :< declF

-- | Parse annotated block
pBlock :: AnnotatedParser Block
pBlock = braces $ do
  exprs <- sepEndBy pExprTop (symbol ";")
  return $ Block exprs

-- | Top-level annotated expression parser
pExprTop :: AnnotatedParser AnnotatedNode
pExprTop = pExpr

-- | Parse annotated expression
pExpr :: AnnotatedParser AnnotatedNode
pExpr = makeExprParser pExprAtom operatorTable

-- | Parse atomic annotated expressions
pExprAtom :: AnnotatedParser AnnotatedNode
pExprAtom = do
  base <- pBaseAnnotatedExprAtom
  pAccessChain base
  where
    pBaseAnnotatedExprAtom = choice
      [ try pArrowFunction
      , try $ withSourceInfo $ do
          _ <- symbol "("
          _ <- symbol ")"
          return $ EVarF "()"
      , -- Integer literals
        withSourceInfo $ ELitIntF <$> lexeme integer
      , -- Boolean literals
        withSourceInfo $ ELitBoolF True <$ symbol "true"
      , withSourceInfo $ ELitBoolF False <$ symbol "false"
      , -- String literals
        withSourceInfo $ ELitStringF <$> pStringLiteral
      , -- Event-layer listener expressions. 'bind'/'once'/'cancel'/
        -- 'remove' are CONTEXTUAL keywords (not reserved): each alternative
        -- backtracks via 'try' when the word is not followed by an event
        -- label (plus a handler for bind/once), so the four words stay usable
        -- as ordinary identifiers. Placed BEFORE the EVarF alternative, which
        -- would otherwise swallow the leading identifier. The handler argument
        -- is parsed with 'pExprAtom' (variables, arrow functions, parenthesized
        -- applications).
        try $ withSourceInfo $ do
          _ <- pModalityKeyword "bind"
          lbl <- pEventLabel
          EBindF lbl <$> pExprAtom
      , try $ withSourceInfo $ do
          _ <- pModalityKeyword "once"
          lbl <- pEventLabel
          EOnceF lbl <$> pExprAtom
      , try $ withSourceInfo $
          ECancelF <$> (pModalityKeyword "cancel" *> pEventLabel)
      , try $ withSourceInfo $
          ERemoveF <$> (pModalityKeyword "remove" *> pEventLabel)
      , -- Variables
        withSourceInfo $ EVarF <$> pIdentifier
      , -- JSX nodes
        withSourceInfo $ EJSXNodeF <$> pJSXElement
      , -- Effect expressions
        withSourceInfo $ EEffectF <$> (symbol "effect" *> pEffect)
      , -- Parenthesized expressions (including pairs and tuples)
        try $ parens $ do
          exprs <- pExpr `sepBy1` symbol ","
          case exprs of
            [singleExpr] -> return singleExpr
            (firstExpr:_) -> do
              let sourceInfo = getSourceInfo firstExpr
              return $ buildRightAssociativePair sourceInfo exprs
            [] -> fail "Empty tuple not allowed"
      ]

    -- Parse arrow parameter with optional schema
    pArrowParam :: AnnotatedParser (Text, Maybe Type)
    pArrowParam = do
      paramName <- pIdentifier
      mType <- optional (symbol ":" *> pType)
      pure (paramName, mType)

    -- Smart arrow function parser
    pArrowFunction :: AnnotatedParser AnnotatedNode
    pArrowFunction = do
      params <- try (parens (pArrowParam `sepBy` symbol ",") <* lookAhead (symbol "=>"))
                <|> try (do
                      x <- pIdentifier <* lookAhead (symbol "=>")
                      return [(x, Nothing)])
      _ <- symbol "=>"
      body <- braces pExpr <|> pExpr
      case params of
        [] -> withSourceInfo $ return $ EArrowF [] "_" (Just TAny) body
        _ -> do
          let curryArrow [] b = b
              curryArrow ((param, mSch):ps) b = do
                rest <- curryArrow ps b
                withSourceInfo $ return $ EArrowF [] param mSch rest
          curryArrow params (pure body)

    -- Parse access chain (.0, .1)
    pAccessChain e = do
      access <- optional $ do
        _ <- symbol "."
        0 <$ symbol "0" <|> 1 <$ symbol "1"
      case access of
        Just ix -> do
          let NodeAnnotation sourceSpan sch eff = getNodeAnnotation e
          pAccessChain (NodeAnnotation sourceSpan sch eff :< LangFExpr (EPairAccessF e ix))
        Nothing -> return e

-- | Parse string literal
pStringLiteral :: AnnotatedParser Text
pStringLiteral = symbol "\"" *> takeWhileP (Just "string content") (/= '"') <* symbol "\""

-- | Parse annotated JSX element (either normal or self-closing)
pJSXElement :: AnnotatedParser AnnotatedNode
pJSXElement = try pJSXSelfClosing <|> pJSXNormal
  where
    -- Parse normal JSX element: <tag attrs>children</tag>
    pJSXNormal = withJSXSourceInfo $ do
      _ <- symbol "<"
      tag <- pIdentifier
      attrs <- many pJSXAttr
      _ <- symbol ">"
      let closingTag = try (symbol "</" *> string tag *> sc *> symbol ">")
      children <- manyTill pJSXChild closingTag
      return $ JSXElementNodeF tag attrs children

    -- Parse self-closing JSX element: <tag attrs />
    pJSXSelfClosing = withJSXSourceInfo $ do
      _ <- symbol "<"
      tag <- pIdentifier
      attrs <- many pJSXAttr
      _ <- symbol "/>"
      return $ JSXSelfClosingNodeF tag attrs

    -- Parse JSX attribute
    pJSXAttr = do
      attrName <- pIdentifier
      _ <- symbol "="
      val <- pJSXAttrValue
      return $ JSXAttr (attrName, val)

    -- Parse JSX attribute value (string or expression)
    pJSXAttrValue =
      JSXAttrString <$> (symbol "\"" *> takeWhileP (Just "attr string") (/= '"') <* symbol "\"")
      <|> JSXAttrExpr <$> braces pExpr

    -- Parse JSX child (text, expression, or nested node)
    pJSXChild =
      withJSXChildSourceInfo (ChildTextF . strip <$> takeWhile1P (Just "jsx text") (`notElem` ['<', '{']))
      <|> withJSXChildSourceInfo (ChildExprF <$> braces pExpr)
      <|> withJSXChildSourceInfo (ChildNodeF <$> pJSXElement)

-- | Operator table for annotated expressions
operatorTable ::
  [ [Operator AnnotatedParser AnnotatedNode] ]
operatorTable =
  [ [ Prefix notOp ] -- Add the ! operator as prefix
  , [ InfixL (binaryOp "*")
    , InfixL (binaryOp "/") ]
  , [ InfixL (binaryOp "++")
    , InfixL (binaryOp "-")
    , InfixL (binaryOp "+") ]
  , [ InfixN (binaryOp "===")
    , InfixN (binaryOp "==")
    , InfixN (binaryOp "!==")
    , InfixN (binaryOp "!=")
    , InfixN (binaryOp "<=")
    , InfixN (binaryOp ">=")
    , InfixN (binaryOp "<")
    , InfixN (binaryOp ">") ]
  , [ InfixL (binaryOp "&&") ]
  , [ InfixL (binaryOp "||") ]
  , [ ternaryIfOp ]  -- Ternary if operator
  , [ InfixL (pure appOp) ] -- function application, lowest precedence
  , [ InfixL unitSeqOp ]  -- Add ';;' operator for unit sequencing
  ]
  where
    -- Prefix not operator
    notOp = do
      _ <- symbol "!"
      return $ \x ->
        let sourceInfo = getSourceInfo x
            opVar = sourceInfo :< LangFExpr (EVarF "not")
        in sourceInfo :< LangFExpr (EAppF opVar x)

    -- Binary operators
    binaryOp op = do
      _ <- symbol op
      return $ \x y ->
        let sourceInfo = getSourceInfo x
            opVar = sourceInfo :< LangFExpr (EVarF op)
            app1 = sourceInfo :< LangFExpr (EAppF opVar x)
        in sourceInfo :< LangFExpr (EAppF app1 y)

    -- Special binary operator for ';;' (unit sequencing)
    unitSeqOp = do
      _ <- symbol ";;"
      return $ \x y ->
        let sourceInfo = getSourceInfo x
            opVar = sourceInfo :< LangFExpr (EVarF ";;")
            app1 = sourceInfo :< LangFExpr (EAppF opVar x)
        in sourceInfo :< LangFExpr (EAppF app1 y)

    -- Ternary if operator
    ternaryIfOp = Postfix $ do
      _ <- symbol "?"
      thenE <- pExpr
      _ <- symbol ":"
      elseE <- pExpr
      return $ \cond ->
        let sourceInfo = getSourceInfo cond
        in sourceInfo :< LangFExpr (EIfF cond thenE elseE)

    -- Function application
    appOp x y =
      let sourceInfo = getSourceInfo x
      in sourceInfo :< LangFExpr (EAppF x y)

-- | Parse a type annotation, including arrow and pair types
pType :: AnnotatedParser Type
pType = pArrowType

-- | Parse arrow types, which may have pair types as their argument or return type
pArrowType :: AnnotatedParser Type
pArrowType = do
  argType <- pPairType
  option argType $ do
    _ <- symbol "->"
    retType <- pArrowType
    mEffect <- optional $ do
      _ <- symbol "|"
      pEffect
    case mEffect of
      Just eff -> return $ TArrow [] argType retType eff
      Nothing -> return $ TArrow [] argType retType EffNone

-- | Parse pair types (infix asterisk), e.g., int * bool
pPairType :: AnnotatedParser Type
pPairType = do
  t1 <- pBaseType
  option t1 $ do
    _ <- symbol "*"
    TPair t1 <$> pPairType

-- | Parse a base type (string, int, bool, or a parenthesized type)
pBaseType :: AnnotatedParser Type
pBaseType = choice
  [ TString <$ symbol "string"
  , TInt <$ symbol "int"
  , TInt <$ symbol "number"
  , TBool <$ symbol "bool"
  , TUnit <$ symbol "unit"
  , THtml <$ symbol "html"
  , TAny <$ symbol "any"
  , pSchema
  , parens pType
  ]

-- | Parse schema, either a polymorphic forall or a monomorphic type
pSchema :: AnnotatedParser Type
pSchema = do
  _ <- symbol "forall"
  vs <- sepBy pIdentifierNoDot (symbol ",")
  let vs' = map EffVarName vs
  _ <- symbol "."
  inner <- pArrowType
  case inner of
    (TArrow [] i o e) -> return (TArrow vs' i o e)
    _ -> fail "only function types can be generalized"

-- | Parse an 'Effect' value, handling sequence and branching
pEffect :: AnnotatedParser Effect
pEffect = do
  effs <- pEffectTerm `sepBy1` symbol "*"
  return $ mkEffSeq effs

-- | Parse an 'Effect' term, allowing for branching
pEffectTerm :: AnnotatedParser Effect
pEffectTerm = do
  eff1 <- pEffectFactor
  option eff1 $ do
    _ <- symbol "+"
    EffBranch eff1 <$> pEffectTerm

-- | Parse angle brackets (used by event labels)
angles :: AnnotatedParser a -> AnnotatedParser a
angles = between (symbol "<") (symbol ">")

-- | Parse an event label ℓ⟨v⟩: an identifier, then '<', then a
-- comma-separated tuple of statically-known base values, then '>'.
-- The empty tuple (@timeout<>@) is allowed. The label NAME is parsed by
-- 'pEventLabelName', which (unlike 'pIdentifier') permits reserved keywords:
-- the paper's asyncCompute events are literally named @comp<suc>@/@comp<err>@
-- ("comp" is the component keyword), and a label name is always immediately
-- followed by '<', so the relaxation is unambiguous at every use site.
pEventLabel :: AnnotatedParser EventLabel
pEventLabel = do
  name <- pEventLabelName
  values <- angles (pEventLabelValue `sepBy` symbol ",")
  return $ EventLabel name values

-- | Event-label names: same character rules as 'pIdentifier' but WITHOUT the
-- reserved-keyword check (see 'pEventLabel').
pEventLabelName :: AnnotatedParser Text
pEventLabelName = lexeme $ do
  firstChar <- letterChar
  rest <- many $ try $ do
    notFollowedBy (lookAhead (char '.' *> (char '0' <|> char '1')))
    alphaNumChar <|> char '.'
  return (pack (firstChar : rest))

-- | Parse one event-label value: an optional '#' followed by one or more
-- value characters (stored verbatim, '#' kept). Values are statically-known
-- base values (e.g. @#doc@, a request URL), so the charset
-- is permissive: anything except whitespace and the effect-grammar
-- metacharacters , > < { } ( ) * + |
pEventLabelValue :: AnnotatedParser Text
pEventLabelValue = lexeme $ do
  hash <- option "" (string "#")
  rest <- takeWhile1P (Just "label value") isValueChar
  return (hash <> rest)
  where
    isValueChar c = not (isSpace c) && c `notElem` (",><{}()*+|" :: String)

-- | Parse an event-layer keyword, requiring an identifier boundary so an
-- event kind whose NAME merely starts with the keyword (e.g. @cancelx<y>@)
-- still parses as a plain event effect. The boundary check must run BEFORE
-- the trailing-whitespace consumer, or the valid @cancel click<#doc>@ (whose
-- next non-space char is a letter) would be rejected too.
pModalityKeyword :: Text -> AnnotatedParser Text
pModalityKeyword kw = lexeme (string kw <* notFollowedBy (alphaNumChar <|> char '.'))

-- | Parse an atomic 'Effect' factor
pEffectFactor :: AnnotatedParser Effect
pEffectFactor = choice
  [ EffNone <$ symbol "none"
  , do
      _ <- symbol "loop["
      name' <- pIdentifier
      _ <- symbol "]"
      return $ EffLoop name'
  , do
      _ <- symbol "@"
      EffStateChange <$> pIdentifier
  , do
      _ <- symbol "after"
      delay <- pDelay
      _ <- symbol "{"
      eff <- pEffect
      _ <- symbol "}"
      return $ EffAfter delay eff
  -- Event layer. NOTE: 'always'/'eventually'/'cancel'/'remove' are deliberately
  -- NOT reserved keywords (they stay usable as ordinary identifiers in
  -- expression position), so each alternative backtracks via 'try': if the
  -- word is not followed by an event label (for the modalities, a label then a
  -- braced effect), the parse falls through to the EffVar alternative below.
  -- 'pModalityKeyword' additionally requires an identifier boundary, so event
  -- kinds named e.g. 'cancelled' or 'removeAll' parse as plain event effects.
  , try $ do
      _ <- pModalityKeyword "always"
      lbl <- pEventLabel
      eff <- braces pEffect
      return $ EffAlways lbl eff
  , try $ do
      _ <- pModalityKeyword "eventually"
      lbl <- pEventLabel
      eff <- braces pEffect
      return $ EffEventually lbl eff
  , try $ do
      _ <- pModalityKeyword "cancel"
      EffCancel <$> pEventLabel
  , try $ do
      _ <- pModalityKeyword "remove"
      EffRemove <$> pEventLabel
  , try (EffEvent <$> pEventLabel)
  , EffVar <$> pEffVar
  , parens pEffect
  ]

-- | Parse 'Unit' values (renders 'r', network requests 'n', milliseconds 'ms',
-- debounce 'db', intervals 'i', compute units 'u'). NOTE: unlike 'r'/'n', the
-- compute unit 'u' is NOT in 'reservedKeywords' (same as 'i'/'ms'/'db'), so it
-- remains usable as an ordinary identifier outside effect position.
pUnit :: AnnotatedParser Unit
pUnit = choice
  [ Renders <$ symbol "r"
  , NetworkReq <$ symbol "n"
  , Millis <$ symbol "ms"
  , Debounce <$ symbol "db"
  , Interval <$ symbol "i"
  , Compute <$ symbol "u"
  ]

-- | Parse 'Delay' values, allowing for addition
pDelay :: AnnotatedParser Delay
pDelay = do
  d1 <- pDelayTerm
  option d1 $ do
    _ <- symbol "+"
    Plus d1 <$> pDelay

-- | Parse a 'Delay' term, which is currently just a 'Time' unit
pDelayTerm :: AnnotatedParser Delay
pDelayTerm = Time . fromInteger <$> lexeme integer <*> pUnit

-- | Parse an effect variable name. The leading @?@ is optional on input but is
-- always produced on output (see 'prettyEffect'), so printed effects reparse.
-- This parses written variables only: a unification variable prints as
-- @?_e3@, which is deliberately not an identifier (see 'Types.prettyUnif').
pEffVar :: AnnotatedParser EffVarName
pEffVar = EffVarName <$> (option "" (symbol "?") *> pIdentifier)

-- | Data type to represent component arguments (either identifier or expression)
data CompArg = CompArgIdent Text | CompArgExpr AnnotatedNode

-- | Parse component argument (either identifier or expression)
-- | Parse identifier for component arguments (excludes boolean literals and arrow functions)
pCompArgIdentifier :: AnnotatedParser Text
pCompArgIdentifier = try $ do
  -- First, check if this looks like an arrow function pattern
  notFollowedBy $ try $ do
    _ <- pIdentifier
    _ <- symbol "=>" <|> symbol "?" <|> symbol "*" <|> symbol "/" <|> symbol "++" <|> symbol "-"
        <|> symbol "+" <|> symbol "===" <|> symbol "==" <|> symbol "!==" <|> symbol "!=" <|> symbol "<=" <|> symbol ">="
        <|> symbol "<" <|> symbol ">" <|> symbol "&&" <|> symbol "||" <|> symbol "("
    return ()
  -- Don't match boolean literals at all
  notFollowedBy (symbol "true" <|> symbol "false")
  -- Don't match expressions with dots (like todos.0)
  notFollowedBy $ try $ do
    _ <- pIdentifier
    _ <- symbol "."
    return ()
  -- Now parse the identifier normally
  pIdentifierNoDot  -- Use the no-dot version for component args

pCompArg :: AnnotatedParser CompArg
pCompArg =
  CompArgIdent <$> pCompArgIdentifier <|> CompArgExpr <$> pExpr

-- | Process component arguments, creating let declarations for expressions
processCompArgs :: Text -> [CompArg] -> ([Declaration], [Text])
processCompArgs inst args =
  let results = zipWith processArg [0..] args
      letDecls = mapMaybe fst results
      argNames = map snd results
  in (letDecls, argNames)
  where
    processArg :: Int -> CompArg -> (Maybe Declaration, Text)
    processArg _pos (CompArgIdent name) = (Nothing, name)
    processArg pos (CompArgExpr expr) =
      let argName = "__" <> inst <> "Arg" <> pack (show pos)
          exprAnnotation = SourceAnnotation $ annNodeSpan $ getNodeAnnotation expr
      in (Just (mkDeclLet (Just exprAnnotation) argName Nothing expr), argName)

-- | Generate destructuring declarations for let (a,b,c) = x syntax
-- Creates: let a = x.0; let b = x.1.0; let c = x.1.1; etc.
generateDestructuringDecls :: [Text] -> AnnotatedNode -> [Declaration]
generateDestructuringDecls vars val = case vars of
  [] -> []
  [var] -> [mkDeclLet (Just $ SourceAnnotation $ annNodeSpan $ getNodeAnnotation val) var Nothing val]
  (var:rest) ->
    let valAnnotation = SourceAnnotation $ annNodeSpan $ getNodeAnnotation val
        firstDecl = mkDeclLet (Just valAnnotation) var Nothing (createPairAccess val 0)
        restDecls = generateDestructuringDeclsRest rest val 1
    in firstDecl : restDecls

-- | Generate destructuring declarations for the rest of the variables
generateDestructuringDeclsRest :: [Text] -> AnnotatedNode -> Int -> [Declaration]
generateDestructuringDeclsRest vars baseVal accessIndex = case vars of
  [] -> []
  [var] -> [mkDeclLet (Just $ SourceAnnotation $ annNodeSpan $ getNodeAnnotation baseVal) var Nothing (createNestedPairAccess baseVal accessIndex)]
  (var:rest) ->
    let baseAnnotation = SourceAnnotation $ annNodeSpan $ getNodeAnnotation baseVal
        currentDecl = mkDeclLet (Just baseAnnotation) var Nothing (createPairAccess (createNestedPairAccess baseVal accessIndex) 0)
        restDecls = generateDestructuringDeclsRest rest baseVal (accessIndex + 1)
    in currentDecl : restDecls

-- | Create a pair access expression (e.g., x.0 or x.1)
createPairAccess :: AnnotatedNode -> Int -> AnnotatedNode
createPairAccess expr index =
  let sourceInfo = getSourceInfo expr
  in sourceInfo :< LangFExpr (EPairAccessF expr index)

-- | Create nested pair access for right-nested pairs (e.g., x.1.1.1)
createNestedPairAccess :: AnnotatedNode -> Int -> AnnotatedNode
createNestedPairAccess baseExpr 1 = createPairAccess baseExpr 1
createNestedPairAccess baseExpr n | n > 1 =
  createNestedPairAccess (createPairAccess baseExpr 1) (n - 1)
createNestedPairAccess baseExpr _ = baseExpr

-- | Build right-associative pair from a list of expressions
-- e.g., [a, b, c, d] becomes a, (b, (c, d))
buildRightAssociativePair :: NodeAnnotation -> [AnnotatedNode] -> AnnotatedNode
buildRightAssociativePair _sourceInfo [expr] = expr
buildRightAssociativePair sourceInfo [expr1, expr2] =
  sourceInfo :< LangFExpr (EPairF expr1 expr2)
buildRightAssociativePair sourceInfo (expr1:rest) =
  sourceInfo :< LangFExpr (EPairF expr1 (buildRightAssociativePair sourceInfo rest))
buildRightAssociativePair _ [] = error "buildRightAssociativePair: empty list"
