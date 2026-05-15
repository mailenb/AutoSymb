{-# LANGUAGE TemplateHaskell, 
    DeriveFunctor, DeriveLift, DeriveFoldable,
    DeriveDataTypeable #-}

module Semantics where

import Syntax
import MetaParser (embedTypes, typeFor, typeName)

import Data.Data ( Data, Typeable )
import Data.Text ( Text, unpack )
import Language.Haskell.TH ( mkName, Exp(VarE) )
import Language.Haskell.TH.Syntax (Lift, lift, liftTyped)

-- ======= Default Expressions and booleans ======
-- Note: Trigger (B) and expression (E) must be defined outside the language specification
data Expr
  = Var Text
  | Num Integer
  | Neg Expr
  | Op BinOp Expr Expr
  deriving (Eq, Show, Data, Typeable)

data BinOp = Add | Sub | Mul | Div deriving (Eq, Show, Lift, Data, Typeable)

-- Custom lift function
instance Lift Expr where
  -- Note: Since the rules are normalized, we can use the meta variable directly as a TH name
  lift (Var x)       = return $ VarE (mkName (unpack x))
  lift (Num n)       = [| Num n |]
  lift (Neg e)       = [| Neg $(lift e) |]
  lift (Op op e1 e2) = [| Op op $(lift e1) $(lift e2) |]
  
  -- unused
  liftTyped = error "not implemented"

data BExpr
  = Top       -- 'T', true in all states
  | Not BExpr -- '!'
  | Logic LogicOp BExpr BExpr
  | Comparison CompOp Expr Expr
  | BVar Text -- Meta-variable 'b'
  deriving (Eq, Show, Data, Typeable)

data LogicOp = And {-&&-} | Or {-||-} deriving (Eq, Show, Lift, Data, Typeable)
data CompOp = Less | More | Equal     deriving (Eq, Show, Lift, Data, Typeable)

-- Custom lift function
instance Lift BExpr where
  lift (BVar x) = 
    return $ VarE (mkName (unpack x))
  lift Top = 
    [| Top |]
  lift (Not b) = 
    [| Not $(lift b) |]
  lift (Logic op b1 b2) = 
    [| Logic op $(lift b1) $(lift b2) |]
  lift (Comparison op e1 e2) = 
    [| Comparison op $(lift e1) $(lift e2) |]

  -- unused
  liftTyped = error "not implemented"


-- Generate and embed data types from the syntax-specification
$(embedTypes ssosPath)

data Language = Language
  { langName   :: Identifier --- e.g., "While"
  , syntax'    :: Syntax     --- EBNF grammar
  , semantics' :: Semantics  --- list of symbolic SOS rules
  } deriving (Eq, Show)

type Semantics = [Rule XVar]

data Rule x = Rule
  { ruleName    :: Identifier
  , opName'     :: Identifier      -- matches a single rule in syntax
  , trigger'    :: BExpr           -- 'Top' if omitted
  , premises'   :: [Transition x]  -- may be empty
  , conclusion' :: Conclusion x
  }
  deriving (Eq, Show)

newtype Conclusion x = Conclusion (Transition x) deriving (Eq, Show)

data Transition x
  = Progressive ($(typeFor prog) x, State') ($(typeFor prog) x, State')
  -- (x, a) => (y, b) with x, y ∈ XVar and a, b ∈ SVar.
  -- x (source) transitions to y (target) with input a and output b

  | Terminating ($(typeFor prog) x, State') State'
  -- (x, a) ↓ b  ==  (x, a) => (end, b) <-- produces only an output
  deriving (Eq, Show)

data State' 
  = S      SVar -- Metavariable, e.g., a, a'
  | Update SVar [($(typeFor var), SVar, Expr)] 
    -- Variable updates happening at the same time, 
    -- where later updates override earlier ones
    -- e.g., a[ x |-> a(e), y |-> a(e)]
  deriving (Eq, Show)


-- ======= Meta Variables ======
{- In the symbolic SOS rule format, meta variables are used for placeholders for 
    programs, and concrete and symbolic states. -}

type XVar = Identifier -- Program meta-variables
type SVar = Identifier -- State meta-variables

-- Default meta-variable base names that the user can freely use with numbers and primes after them
-- Meta variables must be disjunct
xVars :: [XVar]
xVars = ["x", "y", "z", "program", "prog", "p", "q"]

sVars :: [SVar]
sVars = ["a", "state", "st", "s"]


-- ==== Pretty printers ====
showBExpr :: BExpr -> String
showBExpr Top = "True"
showBExpr (Not b) = 
  "!" ++ showBExpr b
showBExpr (Logic op b1 b2) = 
  "(" ++ showBExpr b1 ++ showLogicOp op ++ showBExpr b2 ++ ")"
showBExpr (Comparison op e1 e2) = 
  "(" ++ showExpr e1 ++ showCompOp op ++ showExpr e2 ++ ")"
showBExpr (BVar b) = unpack b

showLogicOp :: LogicOp -> String
showLogicOp And = " /\\ "
showLogicOp Or = " \\/ "

showCompOp :: CompOp -> String
showCompOp Less = "<"
showCompOp More = ">"
showCompOp Equal = "="

showExpr :: Expr -> String
showExpr (Var x) = unpack x
showExpr (Num n) = show n
showExpr (Neg e) = "-" ++ showExpr e
showExpr (Op op e1 e2) = 
  "(" ++ showExpr e1 ++ showBinOp op ++ showExpr e2 ++ ")"

showBinOp :: BinOp -> String
showBinOp Add = " + "
showBinOp Sub = " - "
showBinOp Mul = " * "
showBinOp Div = " / "



-- ==== Getter functions ====
concTrans :: Rule XVar -> Transition XVar
concTrans r = case conclusion' r of Conclusion tr -> tr

sourceProg :: Transition XVar -> $(typeFor prog) XVar
sourceProg (Progressive (p, _) _) = p
sourceProg (Terminating (p, _) _) = p

targetProg :: Transition XVar -> Maybe ($(typeFor prog) XVar)
targetProg (Progressive _ (p, _)) = Just p
targetProg (Terminating _ _)      = Nothing

outputState :: Transition XVar -> State'
outputState (Progressive _ (_, s)) = s
outputState (Terminating _ s)      = s

-- ==== Unsafe getter functions (safe after validation) ====
-- Premise sources must be a meta-variable
sourceXVar' :: Transition XVar -> XVar
sourceXVar' (Progressive (MVar p, _) _) = p
sourceXVar' (Terminating (MVar p, _) _) = p

-- Premise targets must be meta variables
targetXVar' :: Transition XVar -> Maybe XVar
targetXVar' (Progressive _ (MVar p, _)) = Just p
targetXVar' (Terminating _ _)           = Nothing

-- Input states must be meta variables
inputSVar' :: Transition XVar -> SVar
inputSVar' (Progressive (_, S sVar) _) = sVar
inputSVar' (Terminating (_, S sVar) _) = sVar

-- Premise outputs must be meta variable
outputSVar' :: Transition XVar -> SVar
outputSVar' (Progressive _ (_, S sVar)) = sVar
outputSVar' (Terminating _ (   S sVar)) = sVar
