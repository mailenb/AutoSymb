{-# LANGUAGE TemplateHaskell #-}

module Runtime where

import Syntax ( prog, ssosPath )
import Semantics
import MetaParser ( typeFor )

import Interpreter
import MetaInterpreter ( embedInterpreters, interpreterFor, symbolicExecutorFor )

import Data.Void (Void)
import Data.Text (pack, unpack, Text)

import Debug.Trace (trace)

$(embedInterpreters ssosPath)

-- Input: AST of program
-- Output: The concrete state after executing program
interpProgram :: $(typeFor prog) Void -> IO ConcreteState
interpProgram program = do
  putStrLn "\n=== Interpreting program ==="
  case runConcrete program emptyState of 
    (Nothing, state) -> return state

  -- case runConcrete program emptyState of 
  --   Left  err              -> fail $ "*** Runtime error: " ++ err
  --   Right (Nothing, state) -> return $ Right state

symbExecProgram :: $(typeFor prog) Void -> IO [(SymbolicState, PathCond)]
symbExecProgram p = do
  putStrLn "\n=== Running symbolic executor on program ==="
  case runSymbolic p emptySymState initCond 250 of
    Left err      -> fail $ "*** Runtime error: " ++ err
    Right results -> return $ map getResult results
  where
    getResult (Nothing, state, cond) = (state, cond)


-- Repeatedly call small-step function until (Nothing, endState)
runConcrete :: $(typeFor prog) Void 
                -> ConcreteState 
                -> (Maybe ($(typeFor prog) Void), ConcreteState)
runConcrete p s = 
  case $(interpreterFor prog) p s of
    (Nothing, s') -> (Nothing, s')
    (Just p', s') -> runConcrete p' s'

runSymbolic :: $(typeFor prog) Void 
                -> SymbolicState 
                -> PathCond
                -> Int
                -> Either String [(Maybe ($(typeFor prog) Void), SymbolicState, PathCond)]
runSymbolic p s cond 0 = Left "Symbolic execution timed out" 
runSymbolic p s cond bound = 
  concat <$> mapM step ($(symbolicExecutorFor prog) p s cond)
  where
    step (prog, s', cond') =
      -- Simplify the condition to allow for simpler satisfiability check
      let simpleCond = simplifyCond cond' 
      in -- Only explores the paths that are still feasible
        if isSatisfiable simpleCond
        then case prog of 
          -- Branch has terminated, return the result
          Nothing -> Right [(Nothing, s', cond')]
          
          -- Continue stepping on the simplified condition and reduce the bound
          Just p' -> runSymbolic p' s' simpleCond (bound - 1)

        -- end the branch if the conditions is no longer satisfiable
        else Right []
