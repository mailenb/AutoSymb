module Main where

import ParserSemantics (parseProgram)
import Runtime         (interpProgram, symbExecProgram)
import Interpreter     (showConcState, showCond, showSymbState)

import System.Exit        (die)
import System.Environment (getArgs)
import Control.Monad      (when, void)

-- Example run:
-- cabal run tool -- -ast examples/WHILE.ssos

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["-p", file]         -> void (parseFile file False)
    ["-p", "-ast", file] -> void (parseFile file True)

    ["-c", file]         -> parseFile file False >>= runConcrete 
    ["-c", "-ast", file] -> parseFile file True  >>= runConcrete

    ["-s", file]         -> parseFile file False >>= runSymbolic
    ["-s", "-ast", file] -> parseFile file True  >>= runSymbolic

    [file]         -> parseFile file False >>= runBoth
    ["-ast", file] -> parseFile file True >>= runBoth

    _ ->
      die "Usage:\n\
            \  cabal build (build parsers and executors from specification, remember to run configure.sh first) \n\
            \  cabal run tool -- -p program.LANG   (parse only) \n\
            \  cabal run tool -- -c program.LANG   (concrete execution only) \n\
            \  cabal run tool -- -s program.LANG   (symbolic execution only) \n\
            \  cabal run tool -- program.LANG      (both concrete and symbolic execution) \n\ 
            \  Optional flag: -ast (print out the parsed ast of the program) "
  where
    parseFile file printAst = do
      ast <- parseProgram file
      case ast of
        Left e  -> die $ "*** Parse error: " ++ e
        Right p -> do
          when printAst $ do
            putStrLn "Parsed program AST:"
            print p
          return p

    runConcrete p = do
      finalState <- interpProgram p
      putStrLn "Done."
      putStrLn $ "> Final state: " ++ showConcState finalState

    runSymbolic p = do
      result <- symbExecProgram p
      putStrLn "Done."
      putStrLn $ "> Result:\n" ++ showPaths 1 result

    runBoth p = runConcrete p >> runSymbolic p

    -- ===== Pretty printer =====
    {- Symbolic execution output: 
      Path 1:
        Path Condition: { x = 1 }
        End state: { y := 2 }
        ... 
    -}
    showPaths _ [] = "."
    showPaths num ((state, cond):rest) =
      "Path "               ++ show num ++ 
      ":\nPath condition: " ++ showCond cond ++
      "\nFinal state: "     ++ showSymbState state
      ++ "\n\n" ++ showPaths (num + 1) rest
