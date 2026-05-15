{-# LANGUAGE TemplateHaskell #-}

module Interpreter where

import Syntax (Identifier, var)
import Semantics
import MetaParser (typeFor)

import Data.Maybe (fromMaybe)
import Data.Text (pack, unpack, Text)
import Data.List (nub, intercalate)

import qualified Data.Map as M

-- ===== For concrete interpreters =====
-- We have only one pre-defined data types for variables
newtype Val = VInt Integer deriving (Eq, Show)

-- maps variables to values, e.g., {'x' |-> 1, 'y' |-> 2}
type ConcreteState = M.Map Identifier Val

emptyState :: ConcreteState
emptyState = M.empty

-- Pretty printers
showVal :: Val -> String
showVal (VInt n) = show n

showConcState :: ConcreteState -> String
showConcState = intercalate ", " . map showConcBinding . M.toList

showConcBinding ::  (Identifier, Val) -> String
showConcBinding (var, val) = show var ++ "|->" ++ showVal val

-- maps an identifier to a concrete state, e.g., maps 'a' |-> {'x' |-> 1, 'y' |-> 2}
type MetaSubst = M.Map SVar ConcreteState

lookupState :: MetaSubst -> SVar -> ConcreteState
lookupState metaSubst sVar =
  M.findWithDefault emptyState sVar metaSubst

updateState :: MetaSubst -> State' -> ConcreteState
-- simple case: u = a, return existing state
updateState metaSubst (S sVar) = lookupState metaSubst sVar

-- each update modifies the current state -> foldl
updateState metaSubst (Update sVar updates) =
  foldl (applyUpdate metaSubst) 
        (lookupState metaSubst sVar) 
        updates

-- evaluate expression in evalState and insert it into resultState with key var
applyUpdate :: MetaSubst -> ConcreteState -> ($(typeFor var), SVar, Expr) -> ConcreteState
applyUpdate metaSubst resultState (MX var, evalState, expr) =
  let val = evalExpr (lookupState metaSubst evalState) expr
  in M.insert var val resultState

-- Expression evaluation (epsilon)
evalExpr :: ConcreteState -> Expr -> Val
evalExpr _   (Num n)       = VInt n
evalExpr env (Neg e)       = 
  case evalExpr env e of 
    VInt v -> VInt (-v)

-- Note: uses 0 as default value for unbounded variables
evalExpr env (Var x)       = M.findWithDefault (VInt 0) x env 
evalExpr env (Op op e1 e2) =
  applyOp op
  (evalExpr env e1)
  (evalExpr env e2)

applyOp :: BinOp -> Val -> Val -> Val
applyOp Add (VInt v1) (VInt v2) = VInt (v1 + v2)
applyOp Sub (VInt v1) (VInt v2) = VInt (v1 - v2)
applyOp Mul (VInt v1) (VInt v2) = VInt (v1 * v2)

applyOp Div (VInt v1) (VInt 0)  = error $ "division by zero: " ++ show v1 ++ " / 0"
applyOp Div (VInt v1) (VInt v2) = VInt (v1 `div` v2)


-- Guard evaluation
evalBExpr :: ConcreteState -> BExpr -> Bool
evalBExpr env (BVar x) = error "expected bool meta-variable" -- just a meta variable

evalBExpr _ Top = True

evalBExpr env (Not b) = not (evalBExpr env b)

evalBExpr env (Logic op b1 b2) =
  applyLogicOp op
  (evalBExpr env b1)
  (evalBExpr env b2)

evalBExpr env (Comparison op e1 e2) =
  applyCompOp op
  (evalExpr env e1)
  (evalExpr env e2)

applyLogicOp :: LogicOp -> Bool -> Bool -> Bool
applyLogicOp And = (&&)
applyLogicOp Or  = (||)

applyCompOp :: CompOp -> Val -> Val -> Bool
applyCompOp Less  (VInt v1) (VInt v2) = v1 < v2
applyCompOp More  (VInt v1) (VInt v2) = v1 > v2
applyCompOp Equal (VInt v1) (VInt v2) = v1 == v2


-- ===== For symbolic execution =====
-- The path condition is represented as a list of booleans, with conjunction between each element
type PathCond = [BExpr]

initCond :: PathCond
initCond = [] -- Or [Top]

-- Move And-operators to their own element of the BExpr list, and remove duplicates and top
simplifyCond :: PathCond -> PathCond
simplifyCond = nub . concatMap removeT . concatMap flatten
  where
    -- make each and expression boolean its own list-element
    flatten :: BExpr -> PathCond
    flatten (Logic And b1 b2) = flatten b1 ++ flatten b2 
    flatten b = [b]

    removeT :: BExpr -> PathCond
    removeT Top = []  -- replace Top with empty list
    removeT b   = [b]

-- Later extension: tie it to a SMT solver
isSatisfiable :: PathCond -> Bool
isSatisfiable cond = Not Top `notElem` cond

-- Pretty printer
showCond :: PathCond -> String
showCond = intercalate " /\\ " . map showBExpr

-- Symbolic states operate on expressions, not values
type SymbolicState = M.Map Identifier Expr
type MetaSubstSym  = M.Map SVar SymbolicState

emptySymState :: SymbolicState
emptySymState = M.empty

-- Pretty printers
showSymbState :: SymbolicState -> String
showSymbState = intercalate ", " . map showSymbBinding . M.toList

showSymbBinding :: (Identifier, Expr) -> String
showSymbBinding (var, exp) = show var ++ "|->" ++ showExpr exp

-- Symbolic update functions
lookupSymState :: MetaSubstSym -> SVar -> SymbolicState
lookupSymState metaSubst sVar = M.findWithDefault emptySymState sVar metaSubst

updateStateSym :: MetaSubstSym -> State' -> SymbolicState
updateStateSym metaSubst (S sVar) = lookupSymState metaSubst sVar 

updateStateSym metaSubst (Update sVar updates) = 
  foldl (applyUpdateSym metaSubst) 
        (lookupSymState metaSubst sVar) 
        updates

applyUpdateSym :: MetaSubstSym
              -> SymbolicState
              -> ($(typeFor var), SVar, Expr)
              -> SymbolicState
applyUpdateSym metaSubst resultState (MX var, evalState, expr) = 
  let evalState' = lookupSymState metaSubst evalState
      expr' = simplifyExpr evalState' expr
  in M.insert var expr' resultState


-- Expression evaluation (epsilon):
simplifyExpr :: SymbolicState -> Expr -> Expr
simplifyExpr _ (Num n) = Num n

simplifyExpr env (Neg (Neg e)) = simplifyExpr env e -- remove double negation
simplifyExpr _   (Neg (Num 0)) = Num 0
simplifyExpr _   (Neg (Num n)) = Num (-n)
simplifyExpr env (Neg e) = 
  case simplifyExpr env e of 
    Num n  -> Num (-n)
    Neg e' -> simplifyExpr env e'
    e'     -> Neg e'

-- Either look up x in the environment, or use a symbolic variable x
simplifyExpr env (Var x) = 
  -- trace ("Trying to find var: " ++ show x ++ " in env " ++ show env) $
  M.findWithDefault (Var x) x env 

simplifyExpr env (Op op e1 e2) = 
  simplifyOp env op 
    (simplifyExpr env e1) 
    (simplifyExpr env e2)

simplifyOp :: SymbolicState -> BinOp -> Expr -> Expr -> Expr
simplifyOp env op e1 e2 = 
  case (op, e1, e2) of
    -- Completly reduce fully numeric expressions
    (Add, Num n1, Num n2) -> Num (n1 + n2)
    (Sub, Num n1, Num n2) -> Num (n1 - n2)
    (Mul, Num n1, Num n2) -> Num (n1 * n2)

    (Div, _, Num 0)       -> error "division by zero"
    (Div, Num n1, Num n2) -> Num (n1 `div` n2)
    
    -- Further simplifications of some trivial operator applications 
    (Add, Num 0, e) -> e -- 0 + e = e
    (Add, e, Num 0) -> e -- e + 0 = e
    (Add, e1, Neg e2) -> simplifyOp env Sub e1 e2 -- e1 + -e2 = e1 - e2
    (Add, Neg e1, e2) -> simplifyOp env Sub e2 e1 -- -e1 + e2 = e2 - e1

    (Sub, Num 0, e) -> simplifyExpr env (Neg e) -- 0 - e = -e
    (Sub, e, Num 0) -> e              -- e - 0 = e
    (Sub, e1, e2) | e1 == e2 -> Num 0 -- e - e = 0
    (Sub, e1, Neg e2) -> simplifyOp env Add e1 e2 -- e1 - (-e2) = e1 + e2 

    (Mul, Num 0, _) -> Num 0 -- 0 * e = 0
    (Mul, _, Num 0) -> Num 0 -- e * 0 = 0
    (Mul, Num 1, e) -> e     -- 1 * e = e
    (Mul, e, Num 1) -> e     -- e * 1 = e
    (Mul, Neg e1, Neg e2) -> simplifyOp env Mul e1 e2 -- -e * -e = e * e
    (Mul, Neg(Num 1), e)  -> simplifyExpr env (Neg e) -- -1 * e = -e
    (Mul, e, Neg(Num 1))  -> simplifyExpr env (Neg e) -- e * -1 = -e
    
    (Div, Num 0, _) -> Num 0          -- 0 / e = 0
    (Div, e, Num 1) -> e              -- e / 1 = e
    (Div, e1, e2) | e1 == e2 -> Num 1 -- e / e = 1

    _ -> Op op e1 e2

simplifyBExpr :: SymbolicState -> BExpr -> BExpr
simplifyBExpr _ Top = Top
simplifyBExpr env (BVar x) = BVar x

-- inversion law / remove direct double negation
simplifyBExpr env (Not (Not b)) = simplifyBExpr env b 
simplifyBExpr env (Not b) = 
  case simplifyBExpr env b of
    Not b' -> simplifyBExpr env b'
    Logic And b1 b2 -> Logic Or  (Not b1) (Not b2) -- De Morgan's First Law
    Logic Or  b1 b2 -> Logic And (Not b1) (Not b2) -- De Morgan's Second Law
    b'     -> Not b'

simplifyBExpr env (Logic op b1 b2) =
  simplifyLogicOp env op
  (simplifyBExpr env b1)
  (simplifyBExpr env b2)

simplifyBExpr env (Comparison op e1 e2) =
  simplifyCompOp env op
  (simplifyExpr env e1)
  (simplifyExpr env e2)


simplifyLogicOp :: SymbolicState -> LogicOp -> BExpr -> BExpr -> BExpr
simplifyLogicOp env op b1 b2 = 
  case (op, b1, b2) of
    -- Identity law
    (Or, b, Not Top) -> simplifyBExpr env b
    (Or, Not Top, b) -> simplifyBExpr env b
    (And, b, Top)    -> simplifyBExpr env b
    (And, Top, b)    -> simplifyBExpr env b

    -- Domination law
    (Or, Top, _)      -> Top
    (Or, _, Top)      -> Top
    (And, Not Top, _) -> Not Top
    (And, _, Not Top) -> Not Top

    -- Complement law
    (Or, b1, Not b2)  | b1 == b2 -> Top
    (Or, Not b1, b2)  | b1 == b2 -> Top
    (And, b1, Not b2) | b1 == b2 -> Not Top
    (And, Not b1, b2) | b1 == b2 -> Not Top

    -- Equality laws
    (Or,  b1, b2) | b1 == b2 -> b1
    (And, b1, b2) | b1 == b2 -> b1

    -- Absorption laws
    (Or,  b1, Logic And b2 b3) | b1 == b2 || b1 == b3 -> b1
    (Or,  Logic And b2 b3, b1) | b1 == b2 || b1 == b3 -> b1
    (And, b1, Logic Or b2 b3)  | b1 == b2 || b1 == b3 -> b1
    (And, Logic Or b2 b3, b1)  | b1 == b2 || b1 == b3 -> b1

    _ -> Logic op b1 b2

simplifyCompOp :: SymbolicState -> CompOp -> Expr -> Expr -> BExpr
simplifyCompOp env op e1 e2 = 
  case (op, e1, e2) of
    (_, Num n1, Num n2) -> 
      if applyCompOp op (VInt n1) (VInt n2)
        then Top
        else Not Top 
    (Equal, e1, e2) | e1 == e2  -> Top

    _ -> Comparison op e1 e2
