{-# LANGUAGE LambdaCase #-}

module Alge.Parser (parseProgram, parseExpression, parseType) where

import Alge.Syntax
import Control.Monad (guard, void)
import Control.Monad.Reader
import Data.Char (isUpper)
import Data.Functor (($>))
import Data.Void (Void)
import Text.Megaparsec hiding (parse)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- A boundary admits the original line and more-indented continuation lines.
-- Parentheses suspend the boundary. Layout products create a boundary per item.
data Boundary = Boundary Int Int
type Parser = ReaderT (Maybe Boundary) (Parsec Void String)

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "//")
  (L.skipBlockCommentNested "(*" "*)" <|> L.skipBlockComment "/*" "*/")

allowed :: Parser ()
allowed = do
  boundary <- ask
  pos <- getSourcePos
  case boundary of
    Nothing -> pure ()
    Just (Boundary line column) -> guard (unPos (sourceLine pos) == line || unPos (sourceColumn pos) > column)

lexeme :: Parser a -> Parser a
lexeme p = allowed *> p <* spaceConsumer

symbol :: String -> Parser String
symbol = lexeme . string

reserved :: [String]
reserved = ["type", "fun", "match", "with", "if", "then", "else", "int", "void"]

capitalized :: String -> Bool
capitalized (c:_) = isUpper c
capitalized [] = False

wordRaw :: Parser String
wordRaw = (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_' <|> char '\'')

identifier :: Parser Name
identifier = lexeme $ try $ do
  name <- wordRaw
  guard (name /= "_" && name `notElem` reserved)
  pure name

keyword :: String -> Parser ()
keyword s = void $ lexeme (try (string s <* notFollowedBy (alphaNumChar <|> char '_')))

typeVariable :: Parser Name
typeVariable = lexeme (char '\'' *> wordRaw)

parens :: Parser a -> Parser a
parens p = symbol "(" *> local (const Nothing) (p <* symbol ")")

lineAt :: SourcePos -> Int
lineAt = unPos . sourceLine

columnAt :: SourcePos -> Int
columnAt = unPos . sourceColumn

baseColumn :: Parser Int
baseColumn = asks (maybe 0 (\(Boundary _ c) -> c))

-- Inline RHSs use the enclosing indentation. A newline RHS is a product
-- whose items align at its first column; each item may continue further right.
body :: SourcePos -> Parser Expr -> Parser Expr
body anchor inlineParser = layoutBody anchor inlineParser expression productExpr

layoutBody :: SourcePos -> Parser a -> Parser a -> ([a] -> a) -> Parser a
layoutBody anchor inlineParser itemParser combine = do
  start <- getSourcePos
  base <- baseColumn
  if lineAt start == lineAt anchor
    then local (const (Just (Boundary (lineAt start) base))) inlineParser
    else do
      guard (columnAt start > base)
      let item = do
            pos <- getSourcePos
            local (const (Just (Boundary (lineAt pos) (columnAt start)))) itemParser
      first <- item
      rest <- many $ try $ do
        pos <- getSourcePos
        guard (columnAt pos == columnAt start && lineAt pos > lineAt start)
        item
      pure (combine (first:rest))

productExpr :: [Expr] -> Expr
productExpr [e] = e
productExpr es = EProduct es

expression :: Parser Expr
expression = productExpr <$> sepBy1 expressionNoProduct (symbol ",")

expressionNoProduct :: Parser Expr
expressionNoProduct = choice [lambda, conditional, matching, binaryExpression]

lambda :: Parser Expr
lambda = do
  anchor <- getSourcePos
  keyword "fun"
  args <- some argumentPattern
  void (symbol "->")
  lambdaArgs args <$> body anchor expressionNoProduct

conditional :: Parser Expr
conditional = do
  anchor <- getSourcePos
  keyword "if"
  cond <- expression
  keyword "then"
  yes <- body anchor expressionNoProduct
  keyword "else"
  EIf cond yes <$> body anchor expressionNoProduct

matching :: Parser Expr
matching = do
  keyword "match"
  subject <- expression
  keyword "with"
  cases <- some $ do
    pos <- getSourcePos
    void (symbol "|")
    pat <- patternParser
    void (symbol "->")
    rhs <- local (const (Just (Boundary (lineAt pos) (columnAt pos)))) (body pos expressionNoProduct)
    pure (pat,rhs)
  pure (EMatch subject cases)

binaryExpression :: Parser Expr
binaryExpression = level comparison (level addition (level multiplication application))
  where
    level op next = do
      first <- next
      let rest left = (do
            name <- op
            right <- next
            rest (EBinary name left right)) <|> pure left
      rest first
    comparison = choice (map (try . symbol) ["==", "!=", "<=", ">=", "<", ">"])
    addition = symbol "+" <|> try (symbol "-" <* notFollowedBy (char '>'))
    multiplication = symbol "*" <|> symbol "/"

application :: Parser Expr
application = do
  first <- projected
  args <- many (try (notFollowedBy (symbol "-") *> projected))
  pure (foldl EApply first args)

projected :: Parser Expr
projected = do
  first <- atom
  fields <- many (symbol "." *> identifier)
  pure (foldl EProject first fields)

atom :: Parser Expr
atom = choice
  [ parens $ do
      end <- optional (lookAhead (symbol ")"))
      case end of
        Just _ -> pure EUnit
        Nothing -> do
          e <- expression
          annotation <- optional (symbol ":" *> typeParser)
          pure (maybe e (EAnn e) annotation)
  , EInt <$> lexeme L.decimal
  , symbol "-" *> (EBinary "-" (EInt 0) <$> projected)
  , do
      anchor <- getSourcePos
      name <- identifier
      if capitalized name
        then pure (EField (tagName name) EUnit)
        else (do
          void (try (symbol "=" <* notFollowedBy (char '=')))
          EField name <$> body anchor expressionNoProduct) <|> pure (EVar name)
  ]

patternParser :: Parser Pattern
patternParser = normalizePatterns <$> sepBy1 patternAtom (symbol ",")

normalizePatterns :: [Pattern] -> Pattern
normalizePatterns [p] = p
normalizePatterns ps
  | all isPun ps = PProduct (map pun ps)
  | otherwise = PProduct ps
  where
    isPun = \case
      PVar _ -> True
      PAnn (PVar _) _ -> True
      _ -> False
    pun = \case
      p@(PVar n) -> PField n p
      p@(PAnn (PVar n) _) -> PField n p
      p -> p

patternAtom :: Parser Pattern
patternAtom = do
  p <- choice
    [ parens $ (lookAhead (symbol ")") $> PUnit) <|> patternParser
    , symbol "_" $> PWildcard
    , PInt <$> lexeme (L.signed (pure ()) L.decimal)
    , do
        n <- identifier
        if capitalized n
          then pure (PField (tagName n) PUnit)
          else (symbol "=" *> (PField n <$> patternAtom)) <|> pure (PVar n)
    ]
  annotation <- optional (symbol ":" *> typeNoProduct)
  pure (maybe p (PAnn p) annotation)

-- Bare declaration arguments are binders. Otherwise `foo x = body` would
-- consume `x = body` as a field pattern before reaching the declaration '='.
argumentPattern :: Parser Pattern
argumentPattern = choice
  [ parens ((lookAhead (symbol ")") $> PUnit) <|> patternParser)
  , symbol "_" $> PWildcard
  , do
      n <- identifier
      pure (if capitalized n then PField (tagName n) PUnit else PVar n)
  ]

typeParser :: Parser SType
typeParser = arrowType typeSum

arrowType :: Parser SType -> Parser SType
arrowType operand = do
  a <- operand
  (symbol "->" *> (SArrow a <$> arrowType operand)) <|> pure a

typeSum :: Parser SType
typeSum = do
  ts <- sepBy1 typeProduct (symbol "|")
  pure $ case ts of [t] -> t; _ -> SSum ts

typeProduct :: Parser SType
typeProduct = do
  ts <- sepBy1 typeApplication (symbol ",")
  pure $ case ts of [t] -> t; _ -> SProduct ts

typeNoProduct :: Parser SType
typeNoProduct = arrowType typeApplication

typeApplication :: Parser SType
typeApplication = do
  t <- typeAtom
  case t of
    SName n [] -> SName n <$> many (try typeArgument)
    _ -> pure t
  where
    typeArgument = choice
      [ SVar <$> typeVariable
      , keyword "int" $> SInt
      , parens ((lookAhead (symbol ")") $> SUnit) <|> typeParser)
      , do
          n <- identifier
          notFollowedBy (symbol ":")
          pure (SName n [])
      ]

typeAtom :: Parser SType
typeAtom = choice
  [ keyword "int" $> SInt
  , keyword "void" $> SVoid
  , SVar <$> typeVariable
  , symbol "_" $> SVar "_"
  , symbol ">" *> (SOpen <$> typeApplication)
  , parens ((lookAhead (symbol ")") $> SUnit) <|> typeParser)
  , do
      n <- identifier
      if capitalized n
        then pure (SField (tagName n) SUnit)
        else (symbol ":" *> (SField n <$> typeNoProduct)) <|> pure (SName n [])
  ]

declaration :: Parser Decl
declaration = typeDecl <|> valueDecl
  where
    typeDecl = do
      pos <- getSourcePos
      keyword "type"
      name <- identifier
      local (const (Just (Boundary (lineAt pos) (columnAt pos)))) $ do
        params <- many typeVariable
        void (symbol "=")
        DType name params <$> layoutBody pos typeParser typeParser
          (\ts -> case ts of [t] -> t; _ -> SProduct ts)
    valueDecl = do
      pos <- getSourcePos
      name <- identifier
      local (const (Just (Boundary (lineAt pos) (columnAt pos)))) $ do
        args <- many (try argumentPattern)
        ann <- optional (symbol ":" *> typeParser)
        hasBody <- optional (symbol "=")
        case hasBody of
          Nothing -> case (args,ann) of
            ([],Just t) -> pure (DSignature name t)
            _ -> fail "expected '=' or a type signature"
          Just _ -> DValue name args ann <$> body pos expression

run :: Parser a -> FilePath -> String -> Either String a
run p file input = case runParser (runReaderT (spaceConsumer *> p <* eof) Nothing) file input of
  Left err -> Left (errorBundlePretty err)
  Right x -> Right x

parseProgram :: FilePath -> String -> Either String Program
parseProgram = run (Program <$> many (declaration <* optional (symbol ";")))

parseExpression :: String -> Either String Expr
parseExpression = run expression "<expression>"

parseType :: String -> Either String SType
parseType = run typeParser "<type>"
