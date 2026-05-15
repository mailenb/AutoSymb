{-# LANGUAGE TemplateHaskell #-}
module MetaParser where

import ParserSyntax
import Syntax
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (addDependentFile, lift, liftTyped, Lift)

import Data.Text (pack, unpack, Text, toLower)
import Data.List (partition)
import Data.Maybe (isJust, fromJust)
import Data.Data ( Data, Typeable )

import Text.Megaparsec ((<?>), try)
import Control.Applicative (asum)

import qualified Data.Char as C
import qualified Control.Monad.Combinators.Expr as E


{- For each non-terminal in the grammar, generate:
  1. a type declaration 'T a :: * -> *'  for the signature 
  2. a parser 'Parser (T Var)' to parse into the data type, 
     to retrieve the AST to the parsed program

  We use Template Haskell (TH) to both parts for meta programming.
  https://wiki.haskell.org/Template_Haskell -}

-- Reads a (.ssos-) file, parses the syntax, generates parsers from the spec, 
-- and embeds them into the module that splices this function
embedParsers :: FilePath -> Q [Dec]
embedParsers path = do
  -- Note: Recompiles this function every time the specification changes
  addDependentFile path 
  spec <- runIO $ parseSyntax path
  case spec of
    Left e       -> fail $ "*** Parse error: " ++ e
    Right syntax -> do
      runIO $ putStrLn "[-] Generating parsers..."
      let sigs = (makeParser           <$> pSyntax syntax)
              ++ (makeSimpleParser     <$> vSyntax syntax)
      concat <$> sequence sigs

embedTypes :: FilePath -> Q [Dec]
embedTypes path = do
  addDependentFile path 
  spec <- runIO $ parseSyntax path
  case spec of
    Left e       -> fail $ "*** Parse error: " ++ e
    Right syntax -> do
      runIO $ putStrLn "[-] Generating data types..."
      let sigs = (makeSignature <$> pSyntax syntax)
               : (makeSimple    <$> vSyntax syntax)
      return (concat sigs)

typeFor :: Identifier -> Q Type
typeFor = return . ConT . typeName

parserFor :: Identifier -> Q Exp
parserFor = return . VarE . parserName

{- ========= 1. Generating type signatures =========
    For each nonterminal p, we generate a corresponding algebraic data type.
    Each production becomes a constructor, where:
      * the constructor name matches the production name (conName == pName),
      * and its fields correspond to the (possibly empty) list of nonterminals it references

    For example, for the grammar:
      p : [Skip] 'Skip' 
        | [Asg]  x ':=' Expr 
        | [IF]   'if' BExpr p p 
        | [Seq]  p ';' p ;
    
    This algebraic data type is generated:
      data Meta_P a
        = MVar a
        | Meta_Skip
        | Meta_Asg Meta_x Expr
        | Meta_IF  BExpr (Meta_P a) (Meta_P a)
        | Meta_Seq (Meta_P a) (Meta_P a)
        deriving (Eq, Show, Functor, Lift, Foldable, Data, Typeable)
  
    Some things to note:
    * The type parameter 'a' represents what kind of variables we have, where
      - Closed programs: Meta_P Void
      - Open programs:   Meta_P XVar

    * The program data type gets an extra constructor 'MVar a', 
      and represents meta-variables used in the symbolic SOS semantics rules

    * All generated type and constructor names are prefixed with 'Meta_'
      to avoid unforeseeable name collisions with names in the source code
-}
-- Generate signature 'data P a = ...'
makeSignature :: NonTerminal -> Dec
makeSignature (NonTerminal name rules) = decl
  where
    tyName = typeName name -- type name 
    a      = mkName "a"    -- type parameter
  
    -- Generate a constructor for each production 
    constructors = map makeConstructor rules

    -- Add meta variable constructor for top program nt
    mvar = [NormalC (mkName "MVar") [lazyType (VarT a)] | name == prog]
    
    -- Add derivations
    derivations = DerivClause 
                    Nothing 
                    [ ConT ''Eq,   ConT ''Show, ConT ''Functor
                    , ConT ''Lift, ConT ''Foldable
                    , ConT ''Data
                    -- , ConT ''Typeable
                    ]
    
    -- Make data type declaration
    decl = DataD [] tyName [PlainTV a ()] Nothing (mvar ++ constructors) [derivations]

makeConstructor :: Production -> Con
-- Regexes are always of simple type, | OpName Text
makeConstructor (Regex pat name) =
  let conName = typeName name
  in NormalC conName [lazyType (ConT ''Text)]

makeConstructor (Production syms name) = 
  let conName = typeName name
  in NormalC conName [lazyType (argType x) | NTRef x <- syms]
  where
    argType :: Identifier -> Type
    argType x =
      let t = typeName x
          a = mkName "a"
      -- Pass the parameter, unless it is of simple type
      in if isSimple x
          then ConT t
          else AppT (ConT t) (VarT a)
 
-- Variable syntax has the simple type Text, with a single predefined constructor MX
-- e.g., newtype X = MX Text
makeSimple :: NonTerminal -> [Dec]
makeSimple (NonTerminal name _) =
  -- Only need to make a type for the top variable nt
  if name == var then decl : [liftInstance] else []
  where   
      tyName = typeName name
      cName  = mkName "MX"
      -- Constructor is always Text
      con = NormalC cName [lazyType (ConT ''Text)]

      derivations = 
          DerivClause Nothing 
          [ ConT ''Eq,   ConT ''Show, ConT ''Data -- , ConT ''Typeable
          ]
  
      decl = NewtypeD [] tyName [] Nothing con [derivations]
      liftInstance = deriveVarLift tyName

{- Make a lift instance for variables, that turns 
   the variable text into a TH name. For example:
    instance Lift Meta_X where
        lift (MX x) = return (VarE (mkName (unpack x)))
-}
deriveVarLift :: Name -> Dec
deriveVarLift tyName = liftInstance
  where
    x     = mkName "x"
    cName = mkName "MX"
    pat   = ConP cName [] [VarP x]

    --   = return $ VarE $ mkName $ unpack x
    body = 
      AppE 
        (VarE 'return)
        (AppE
          (ConE 'VarE)
          (AppE 
            (VarE 'mkName)
            (AppE
              (VarE 'unpack)
              (VarE x)))
        )
    liftFun = FunD 'lift [Clause [pat] (NormalB body) []]

    -- To suppress the warning, but is unused and undefined
    liftTypedFun = FunD 'liftTyped [Clause [pat] (NormalB (VarE 'undefined)) []]

    liftInstance = 
      InstanceD
        Nothing
        []
        (AppT (ConT ''Lift) (ConT tyName))
        [liftFun, liftTypedFun]


{- ========= 2. Parsers  ========= 
  To parse something of type 'T x', we make a function for each nonterminal
   'parseT :: Parser x -> Parser (T x)'

  'makeExprParser' is used to handle grammars with left-recursion,
  by separating the productions into operators and terms.

  A production is an operator iff it recursively refers to the same nonterminal it defines.
  
  In particular, we classify a production over non-terminal 'X' as an operator 
  if it contains only reference(s) to 'X' that are located either:
    1. two times, both at the start and end, making it an INFIX operator
    2. exactly once, at the beginning, making it a POSTFIX operator
    3. exactly once, at the end, making it a PREFIX operator

  The productions that don't fulfill these criteria are terms.
-}
makeParser :: NonTerminal -> Q [Dec]
makeParser (NonTerminal name rules) = do
  let funcName = parserName name
      -- Use the pre-defined 'parseMVar' parser when parsing xvars
      argName  = mkName "parseMVar" 

  -- Seperate the productions into terms and operators
  let (opProds, termProds) = partition (isOperator name) rules
      ops = makeOpTable name opProds

  terms <- makeConsParser name argName termProds

  -- Apply makeExprParser to the terms and operator table
  let body = AppE (AppE (VarE 'E.makeExprParser) terms) ops

  return [FunD funcName [Clause [VarP argName] (NormalB body) []]]

isOperator :: Identifier -> Production -> Bool
isOperator name = isJust . opFixity name

opFixity :: Identifier -> Production -> Maybe Name
-- Regexes are never operators
opFixity _    (Regex _ _ ) = Nothing 
opFixity name (Production syms p) 
  | syms == [NTRef name] = 
      error $ "Illegal operator '" ++ show p ++ 
              "' containing only reference to itself: " ++ show syms

  -- Production with no references is a term
  | null references = Nothing 
  
  -- Operators only contain self references and terminals
  | not (all (== name) references) = Nothing
  
  | otherwise =
      case references of
        -- Production contains only one self-reference -> must be first or last
        [_] | isFirst -> Just 'E.Postfix -- e.g., p '+' '+'
            | isLast  -> Just 'E.Prefix  -- e.g., 'do' p
            -- Productions with self reference in the middle is a term, e.g, '(' p ')'
            | otherwise -> Nothing 

        -- Production contains two self-references -> must be both first and last
        [_,_] | isFirst && isLast -> Just 'E.InfixL

        -- Note: makeExprParser only supports prefix, postfix, and binary infix operators.
        -- Productions with more than two self-references must therefore be refactored
        _ -> Nothing
  where
    references = [nt | NTRef nt <- syms]

    isFirst = head syms == NTRef name 
    isLast  = last syms == NTRef name

-- Build the operator table from the productions, assigning each operator
-- their own precedence level and ordering them according to the specification
makeOpTable :: Identifier -> [Production] -> Exp
makeOpTable name prods = ListE $ map (makeOperator name) prods

-- e.g., (E.Prefix parser)
makeOperator :: Identifier -> Production -> Exp
makeOperator name p = 
  let fixity = fromJust (opFixity name p)
  in  ListE [AppE (ConE fixity) (makeOpParser p)]

-- Parse only the terminal symbols, self-references gets handled by makeExprParser
-- e.g., (Seq <$ symbol ";")
makeOpParser :: Production -> Exp
makeOpParser (Production syms name) =
  case map kwParser terminals of
    [] -> 
      -- Operator contains only self-references, use pure
      AppE (VarE 'pure) (ConE cName) 
    
    ps -> 
      -- Chain terminal parsers by combining them with *>, add a try to not eagerly consume if fails
      UInfixE (ConE cName) (VarE '(<$)) (AppE tryExp (foldr1 chain ps))
  where
    cName     = typeName name
    terminals = [t | Term t <- syms]

    -- e.g., keyword "+" *> keyword "+"
    chain p1 p2 = AppE (AppE (VarE '(*>)) p1) p2

-- Make a parser for each term production in the nonterminal
makeConsParser :: Identifier -> Name -> [Production] -> Q Exp
makeConsParser tyName px prods = do
  constr <- mapM (consParser tyName px) prods
  let parsers = constr ++ metaParsers
      base    = AppE asumExp (ListE (AppE tryExp <$> parsers))
  return $ addLabel base tyName
  where
    metaParsers
      -- Only make meta parsers for program
      | tyName == prog =
        let -- Parse meta variables using the parser in px
            mVar = UInfixE (ConE (mkName "MVar")) (VarE '(<$>)) (VarE px)
            
            p = AppE (VarE (parserName tyName)) (VarE px)
            parensP   = AppE (VarE 'parens) p
            bracketsP = AppE (VarE 'braces) p

        in [parensP, bracketsP, mVar]
      | otherwise = []

consParser :: Identifier -> Name -> Production -> Q Exp
-- Parse regexes using the predefined regexParser
-- e.g., parseX a = regexParser "[0-9]*" <?> "X"
consParser tyName px (Regex pat name) = 
  return $ addLabel base name
  where
    cName  = typeName name 
    parser = AppE (VarE 'regexParser) (textExp pat)
    base   = UInfixE (ConE cName) (VarE '(<$>)) parser 

consParser tyName px (Production syms name) = do
  parser <- parseSyms [] syms
  return $ addLabel (DoE Nothing parser) name
  where
    cName = typeName name

    parseSyms :: [Name] -> [Sym] -> Q [Stmt]
    -- Parse terminal as a keyword, "_ <- keyword t"
    parseSyms ns (Term t:rest) = do
      next <- parseSyms ns rest
      return $ BindS WildP (kwParser t) : next

    -- Parse references using the parser to the name it refers to "n <- parseN"
    parseSyms ns (NTRef n:rest) = do
      let -- tName = nameBase (typeName n)
          pName = parserName n -- mkName ("parse" <> tName)

          -- Propagate the px unless it is of simple type
          parser =
            if isSimple n
              then VarE pName
              else AppE (VarE pName) (VarE px)
    
      vName <- varName n
      next  <- parseSyms (ns <> [vName]) rest

      return $ BindS (VarP vName) parser : next

    --  List of symbols is empty: Connect variable names together to make full data type
    parseSyms ns [] =
      return
        [NoBindS $ AppE (VarE 'return)
                        (foldl AppE (ConE cName) (VarE <$> ns))]


{- =========== 2.2 Simple Text Parser (for variable syntax) =========== 
  
  Due to parsing limitations, variable syntax does not allow whitespace.
  Each production must consist of exactly one symbol.

  Example:
    parseX    = try (keyword "abc") <|> try parseVar <|> try parseFunc
    parseVar  = regexParser "[a-z]*"
    parseFunc = regexParser "[A-Z][a-zA-Z]*"

    parseX    = X <$> (try (keyword "abc") <|> try parseVar <|> try parseFunc)
    parseVar  = regexParser "[a-z]*"
    parseFunc = regexParser "[A-Z][a-zA-Z]*"
-}
makeSimpleParser :: NonTerminal -> Q [Dec]
makeSimpleParser (NonTerminal name rules) = 
  return [FunD funcName [Clause [] (NormalB wrapped) []]]
  where
    funcName = parserName name
    body     = makeSimpleConsParser rules
    -- Wrap top variable NT in MX constructor
    wrapped = 
      if name == var
        then UInfixE (ConE (mkName "MX")) (VarE '(<$>)) body
        else body

makeSimpleConsParser :: [Production] -> Exp
makeSimpleConsParser prods =
  case map simpleConsParser prods of
    [p] -> p -- Do not add asum if it is only one
    ps  -> AppE asumExp (ListE (map (AppE tryExp) ps))

simpleConsParser :: Production -> Exp
-- "regexParser "..."
simpleConsParser (Regex pat _) =
    AppE (VarE 'regexParser) (textExp pat)

-- "keyword t"
simpleConsParser (Production [Term t] _) =
  kwParser t

-- "parseN"
simpleConsParser (Production [NTRef n] _) =
  VarE (parserName n)

simpleConsParser (Production syms name) =
  error $ 
    "Variable productions must contain exactly one symbol, but '"
    ++ unpack name ++ "' contains " ++ show (length syms)


-- ======= Miscellaneous helper functions =======
parserName :: Identifier -> Name
parserName name = mkName $ "parse" <> nameBase (typeName name)

-- Add prefix to avoid name collisions with types or constructors in the source code
typeName :: Identifier -> Name
typeName name 
  | name `elem` ["BExpr", "Expr"] = mkName $ unpack name
  | otherwise = mkName $ "Meta_" <> capitalizeFirst (unpack name)

-- We prefix variables with "var_" to avoid illegal variable names in haskell
varName :: Identifier -> Q Name
varName name = newName ("var_" <> unpack (toLower name))

capitalizeFirst :: String -> String
capitalizeFirst (x:xs) = C.toUpper x : xs
capitalizeFirst _ = ""

lowerFirst :: String -> String
lowerFirst (x:xs) = C.toLower x : xs
lowerFirst _ = ""

kwParser :: Text -> Exp
kwParser t = AppE (VarE 'keyword) (textExp t) 

textExp :: Text -> Exp
textExp = LitE . StringL . unpack

asumExp :: Exp
asumExp = VarE 'asum

tryExp :: Exp
tryExp  = VarE 'try

addLabel :: Exp -> Text -> Exp
addLabel p l = UInfixE p (VarE '(<?>)) (textExp l)

lazyType :: Type -> BangType
lazyType t = (Bang NoSourceUnpackedness NoSourceStrictness, t)

-- Check if nonterminal name is one of the pre-defined expression-types or variable syntax
isSimple :: Identifier -> Bool
isSimple x = x == "BExpr" || x == "Expr" || x == var
