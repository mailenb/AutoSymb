module Syntax where

import Data.Text (Text)

-- Variables dependent on the specification, but that must be known at compile time
-- They can be configured by the user by running the bash script configuration.sh
prog :: Identifier
prog = "p" 

var :: Identifier
var = "x"

ssosPath :: FilePath
ssosPath = "examples/casestudy2/while_extended.ssos"


type Identifier = Text

-- Later extension: Extend sections with eSyntax and bSyntax to let the user
-- be able to define their own expressions and booleans (for now we only rely on built-ins)
data Syntax = Syntax
  { pSyntax :: [NonTerminal] -- Program syntax / start symbol  
  , vSyntax :: [NonTerminal] -- Variable syntax
  } deriving (Eq, Show)
-- Note: the lists of nonterminals are non-empty

data NonTerminal 
  = NonTerminal
  { ntName  :: Identifier
  , ntRules :: [Production] -- non empty list of available productions 
  } deriving (Eq, Show)

data Production 
  = Production
  { symbols :: [Sym]      -- Extension for later: Add support for repetition and optional symbols
  , pName   :: Identifier -- must be unique, e.g., [SKIP]
  } 
  | Regex 
  { pattern :: Text
  , pName   :: Identifier 
  }
  deriving (Eq, Show)

-- Can be either a terminal (in single quotes) or reference to a nonterminal (just a name)
data Sym
  = Term  Text       -- e.g., 'Skip', ':='
  | NTRef Identifier -- e.g., EXPR, BEXPR, NOTE: must be defined
  deriving (Eq, Show) 


{- Extension for later:

  * extend with constructs for repetition and optional symbols
  
  * Split term in keywords and terminals to 
  allow terminals to be written without a space after them
  => Will need to check it does not contain any symbols that can be used as a variable name -}
