{-# LANGUAGE TemplateHaskell #-}
module ParserSemantics (parseSpecification, parseProgram) where

import Syntax
import Semantics
import ParserSyntax
import MetaParser

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Text (Text, pack, unpack)
import qualified Data.Text.IO as TIO
import Data.Void (Void)

import Control.Monad.State (runState, get)
import Control.Monad (unless)
import qualified Control.Monad.Combinators.Expr as E

-- Generate and embed parsers from the syntax specification
$(embedParsers ssosPath)

-- =========== Top parsers (used in Main) ============
parseSpecification :: FilePath -> IO (Either String Language)
parseSpecification path = do
  input <- TIO.readFile path

  -- First pass: Collect name of nonterminals
  let initialState = ParseState ["BExpr", "Expr"] []
  case runState (runParserT collectNTNames path input) initialState of
    (Left err,    _) -> return $ Left (errorBundlePretty err)
    (Right names, _) -> do
      -- Second pass: Parse the full language (using the NT-names)
      let st = ParseState (names ++ ["BExpr", "Expr"]) []
      case runState (runParserT (sc *> language <* eof) path input) st of
        (Left  err,  _) -> return $ Left (errorBundlePretty err)
        (Right lang, _) -> return $ Right lang

parseProgram :: FilePath -> IO (Either String ($(typeFor prog) Void))
parseProgram path = do
  input <- TIO.readFile path
  putStrLn "=== Parsing program ==="
  case runState (runParserT (sc *> $(parserFor prog) empty <* eof) path input) (ParseState [] []) of
    (Left err,  _) -> return $ Left (errorBundlePretty err)
    (Right ast, _) -> do
      putStrLn "Done."
      return $ Right ast

-- =========== Full Language Parser ===========
language :: Parser Language
language =
  Language
    <$> metaidentifier
      <* keyword "specification"
      <* symbol "{"
    <*> syntax
    <*> semantics
      <* symbol "}"

-- =========== Semantics Parsers ===========
semantics :: Parser Semantics
semantics = keyword "semantics" *> braces (many rule)

rule :: Parser (Rule XVar)
rule = do
  _    <- keyword "rule"
  name <- metaidentifier
  op   <- opName

  -- Fail if operator name is not defined in syntax
  st   <- get
  unless (op `elem` opNames st) $
    fail $ "rule '" ++ unpack name ++ "' refers to undefined operator '[" ++ unpack op ++ "]'"

  _  <- symbol "{"
  b  <- option Top trigger
  ps <- option [] premises
  c  <- conclusion
  _  <- symbol "}"
  return $ Rule name op b ps c

-- e.g., [Skip], [IF]
opName :: Parser Identifier
opName =
  between (symbol "[") (symbol "]") metaidentifier <?> "operator name"

trigger :: Parser BExpr
trigger = keyword "trigger" *> braces parseBExpr

parseBExpr :: Parser BExpr
parseBExpr = E.makeExprParser bTerm bOpTable <?> "boolean expression"
  where
    bTerm = choice
      [ parens parseBExpr
      , Top <$   keyword "T"
      , try (Comparison Less  <$> parseExpr <*> (symbol "<" *> parseExpr))
      , try (Comparison More  <$> parseExpr <*> (symbol ">" *> parseExpr))
      , try (Comparison Equal <$> parseExpr <*> (symbol "=" *> parseExpr))
      , BVar <$> userIdentifier
      ]

    bOpTable =
      [ [ E.Prefix (Not       <$ symbol "!") ]
      , [ E.InfixL (Logic And <$ symbol "&&") ]
      , [ E.InfixL (Logic Or  <$ symbol "||") ]
      ]

parseExpr :: Parser Expr
parseExpr = E.makeExprParser eTerm eOps <?> "expression"
  where
    eTerm = choice
      [ parens parseExpr
      , Num <$> lexeme L.decimal
      , Var <$> userIdentifier
      ]

    eOps =
      [ [ E.Prefix (Neg    <$ symbol "-")]
      , [ E.InfixL (Op Mul <$ symbol "*")
        , E.InfixL (Op Div <$ symbol "/") ]
      , [ E.InfixL (Op Add <$ symbol "+")
        , E.InfixL (Op Sub <$ symbol "-") ]
      ]

userIdentifier :: Parser Text
userIdentifier = do
  id <- $(parserFor var)
  let MX x = id
  return x

  -- Identifier cannot be the same as a defined terminal
  -- st <- get
  -- if id `elem` keywords st
  --   then fail $ "reserved keyword '" ++ unpack id ++ "' cannot be used as an identifier"
  --   else return id


premises :: Parser [Transition XVar]
premises = keyword "premises" *> braces (many transition)

conclusion :: Parser (Conclusion XVar)
conclusion = Conclusion
  <$> (keyword "conclusion" *> braces transition)

transition :: Parser (Transition XVar)
transition = try terminating <|> progressive

-- (x, a) => (y, b)
progressive :: Parser (Transition XVar)
progressive = Progressive
  <$> config
    <* symbol "=>"
  <*> config

-- (x, a) => (end, b)
terminating :: Parser (Transition XVar)
terminating = Terminating
  <$> config
    <* symbol "=>"
  <*> parens (keyword "end" *> symbol "," *> state)

-- (x, a)
config :: Parser ($(typeFor prog) XVar, State')
config = parens $ (,)
  <$> $(parserFor prog) parseMVar
    <* symbol ","
  <*> state

state :: Parser State'
state = try update <|> S <$> sVar

-- e.g., a[x |-> a'(e), y |-> a''(e)]
update :: Parser State'
update = Update
  <$> sVar
  <*> between (symbol "[") (symbol "]")
              (update' `sepBy1` symbol ",")
  where
    -- Update program-identifier with an expression
    update' =
      (,,)
      <$> $(parserFor var)
        <* symbol "|->"
      <*> sVar
      <*> parens parseExpr

-- Parses meta variables as one of the bases, followed by many (or none) numbers or primes (')
metaVar :: [Text] -> Parser Identifier
metaVar validBases = lexeme $ do
  b <- base
  d <- pack <$> many digitChar
  p <- pack <$> many (char '\'')
  _ <- notFollowedBy idChar -- avoid successfully parsing substrings
  return $ b <> d <> p
  where
    base = choice (symbol <$> validBases)
        <?> ("meta variable must be one of " <> show validBases)

parseMVar :: Parser XVar
parseMVar = metaVar xVars

sVar :: Parser SVar
sVar = metaVar sVars
