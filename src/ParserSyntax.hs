module ParserSyntax where

import Syntax

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Void (Void)
import Data.Text (Text, pack, unpack, isInfixOf, any)
import Data.Char (isSpace)
import Data.List.Unique (repeated)
import qualified Data.Text.IO as TIO

import Text.Regex.TDFA ((=~))

import Control.Monad (void, when)
import Control.Monad.State (State, runState, get, modify)

import Debug.Trace (trace)

-- ============ Parser State ============ --
data ParseState = ParseState { ntNames  :: [Identifier] -- names of nonterminals defined
                             , opNames  :: [Identifier] -- names of productions defined
                            --  , keywords :: [Text]       -- keywords defined by literals
                             } deriving (Show)

type Parser = ParsecT Void Text (State ParseState)

-- ========= Lexing Helpers =========

{- Whitespace handling: 
  We assume there are no whitespace before each token, and each parser consumes
  all whitespace after itself. -}

-- Space consumer: L.space tries all three until no one can no longer be applied
sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

-- Remove trailing whitespace
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- Matches text and removes trailing whitespace
symbol :: Text -> Parser Text
symbol = L.symbol sc

-- Keyword parser uses notFollowedBy to avoid longer strings
-- with the keyword as a substring to be wrongly parsed 
keyword :: Text -> Parser Text
keyword t = lexeme $ string t <* notFollowedBy idChar

-- Legal characters for identifiers in the specification
idChar :: Parser Char
idChar = alphaNumChar <|> char '_' <|> char '\''

-- Standard identifier. Must start with a letter followed by many or none id chars
metaidentifier :: Parser Identifier
metaidentifier = lexeme $ do
  first <- letterChar
  rest  <- many idChar
  let id = first : rest
  if id `elem` reserved
    then fail $ "reserved keyword '" ++ id ++ "' cannot be used as a meta-identifier"
    else return $ pack id

-- Reserved keywords in our meta-language (that can't be used as identifiers)
reserved :: [String]
reserved =
  ["specification", "syntax", "semantics"
  , "program-syntax", "variable-syntax"
  , "rule", "premises", "trigger", "conclusion"
  , "end"
  ]

regexParser :: Text -> Parser Text
regexParser pat = lexeme $ do
  input <- pack <$> some (satisfy valid)
  -- Check if the parsed input matches the specified pattern
  if input =~ pat
    then return input
    else fail $ "'" ++ unpack input ++ "' does not match pattern: " ++ unpack pat
  where
    valid c = c `notElem` metaRegexChar && not (isSpace c)

-- NOTE: tool only supports a subset of regexes due to limitations of parsing
-- Characters disallowed in regex-patterns, to allow for smoother parsing
illegalRegexChar :: [Char]
illegalRegexChar =  [' ', '\t', '\n', '\r']

-- Meta symbols used inside regex patterns, but should not be parsed in regexParser
metaRegexChar :: [Char]
metaRegexChar = [ ',', '(', ')', '{', '}']

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- ============== Main Parser ============== --
parseSyntax :: FilePath -> IO (Either String Syntax)
parseSyntax path = do
  input <- TIO.readFile path

  -- First pass: Collect name of nonterminals
  let initialState = ParseState [] []
  case runState (runParserT collectNTNames path input) initialState of
    (Left err,    _) -> return $ Left (errorBundlePretty err)
    (Right names, _) -> do
      -- Validate the names found
      case validateNames names of
        []  ->
          -- Second pass: Parse syntax (using the NT-names)
          let st = ParseState (names ++ ["BExpr", "Expr"]) []
          in case runState (runParserT parseOnlySyntax path input) st of
            (Left  err,  _) -> return $ Left (errorBundlePretty err)
            (Right syn,  _) -> return $ Right syn
        
        err -> return $ Left $ concat err
  where 
    parseOnlySyntax = 
      sc >> metaidentifier >> keyword "specification" >> symbol "{" 
        *> syntax

validateNames :: [Text] -> [String]
validateNames names = 
  concat [duplicateError, progError, varError]
  where
    repeatNTs = repeated names

    -- The specification cannot contain any duplicate nonterminal definitions
    duplicateError = 
      [ "Found duplicate defintions of nonterminal(s) " ++ show repeatNTs ++ " "
      | not (null repeatNTs)
      ]
    
    -- The variables set in the configuration must match one of the defined nonterminals
    progError =
      [ "The configured top program name '" ++ unpack prog ++ 
        "' does not match any of the defined nonterminals " ++ show names ++ " "
        | prog `notElem` names
      ]

    varError =
      [ "The configured top variable name '" ++ unpack var ++ 
        "' does not match any of the defined nonterminals " ++ show names ++ " "
      | var `notElem` names
      ]

-- ======== Nonterminal Name Collection ========
collectNTNames :: Parser [Identifier]
collectNTNames = do
  _ <- sc >> metaidentifier >> keyword "specification" >> symbol "{" >> keyword "syntax" >> keyword "{"
  nts <- many sectionNTs
  return $ concat nts

-- Collect non terminal names in each syntax section
sectionNTs :: Parser [Identifier]
sectionNTs = do
  kw <- keyword "program-syntax" <|> keyword "variable-syntax"
  braces (ntOnlyName `sepEndBy` symbol ";")

-- Collect only the name, skip the productions
ntOnlyName :: Parser Identifier
ntOnlyName = metaidentifier <* symbol ":" <* skipProductions

skipProductions :: Parser ()
skipProductions = void $
  manyTill skipChar (lookAhead (symbol ";"))
  where
    skipChar = void regex 
      <|> void terminal 
      <|> L.skipLineComment "--" 
      <|> L.skipBlockComment "{-" "-}" 
      <|> void L.charLiteral

-- =========== Syntax Parsers ===========
syntax :: Parser Syntax
syntax = buildSyntax <$> 
  (keyword "syntax" *> braces (many syntaxSection))

-- Note: The sections can be in arbitrary order
data SyntaxSection
  = Program  [NonTerminal]
  | Variable [NonTerminal]
  deriving (Eq, Show)

syntaxSection :: Parser SyntaxSection
syntaxSection =
        Program  <$> section "program-syntax"
    <|> Variable <$> section "variable-syntax"
  where
    section kw = keyword kw *> braces (nonTerminal `sepEndBy1` symbol ";")

-- There must be exactly one of each section
buildSyntax :: [SyntaxSection] -> Syntax
buildSyntax secs = Syntax pSection vSection
  where
    pSection =
      case [xs | Program xs <- secs] of
        []   -> error "no program syntax defined"
        [xs] -> xs
        _    -> error "duplicate program-syntax section"
    vSection =
      case [xs | Variable xs <- secs] of
        []   -> error "no variable syntax defined"
        [xs] -> xs
        _    -> error "duplicate variable-syntax section"

nonTerminal :: Parser NonTerminal
nonTerminal = NonTerminal
  <$> (metaidentifier <?> "nonterminal name")
    <* symbol ":"
  <*> (production `sepBy1` (symbol "|" <?> "nonterminal separator"))

production :: Parser Production
production = regex <|> production'

production' :: Parser Production
production' = 
  Production <$> some sym <*> prodName

-- Use '/' delimiters like in java script
regex :: Parser Production
regex = Regex <$> pattern' <*> prodName
  where
    pattern' :: Parser Text
    pattern' = do
      pat <- concat <$> (char '/' *> manyTill regexChar (symbol "/"))
      return $ "^" <> pack pat <> "$" -- Ground it for complete match

    regexChar :: Parser String
    regexChar = escapedChar <|> normalChar

    escapedChar :: Parser String
    escapedChar = do
      _ <- char '\\'
      c <- anySingle
      -- Don't allow any escaped meta characters or escaped whitespace
      if c `elem` metaRegexChar || c `elem` ['n', 'r', 't', 's'] 
        then fail $ "Illegal escape sequence: '\\" ++ [c] ++ "'"
        else return ['\\', c]

    normalChar :: Parser String
    normalChar = do
      c <- anySingle
      -- Don't allow whitespace in pattern, as this will later be the delimiter when parsing 
      if c `elem` illegalRegexChar
        then fail $ "Illegal character in regex: '" ++ [c] ++ "'"
        else return [c]

prodName :: Parser Identifier
prodName = do
  name <- symbol "#" *> metaidentifier
  st   <- get
  -- Check for unique operator name
  when (name `elem` opNames st) $
    fail $ "duplicate production name: " ++ unpack name
  -- Add operator name to list of names
  modify $ \st -> st { opNames = name : opNames st }
  return name


sym :: Parser Sym
sym = (terminal <|> reference) <?> "symbol"

terminal :: Parser Sym
terminal = lexeme $ do
  t <- (char '\'' *> manyTill L.charLiteral (char '\'')) <?> "single-quoted terminal"

  -- add terminal to list of keywords used in the language 
  -- st <- get
  -- modify $ \st -> st { keywords = pack t : keywords st }

  return $ Term (pack t)

reference :: Parser Sym
reference = do
  id <- metaidentifier <?> "nonterminal reference"
  st <- get
  if id `elem` ntNames st -- id name must be known / in parseState
    then return $ NTRef id
    else fail   $ "unknown nonterminal referenced: " ++ unpack id
