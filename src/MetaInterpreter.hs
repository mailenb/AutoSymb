{-# LANGUAGE TemplateHaskell #-}
module MetaInterpreter where

import Syntax ( Identifier, prog, var )
import Semantics
import ParserSemantics ( parseSpecification )
import MetaParser ( typeFor, typeName, capitalizeFirst, textExp )

import MetaUtil
import Interpreter ( evalBExpr, simplifyBExpr, updateState, updateStateSym )
import Validate ( validateLanguage, groupByShape )
import Normalize (normalizeSemantics)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (addDependentFile, lift)

import Data.Char (isDigit)
import Data.Text (pack, unpack, toLower, stripPrefix, Text)
import Data.List (groupBy, sortOn)
import Data.Function (on)
import Control.Monad (filterM)

import Data.Validation (Validation(..))

import qualified Data.Map as M

embedInterpreters :: FilePath -> Q [Dec]
embedInterpreters path = do
  addDependentFile path

  -- Parse specification to generate interpreters from semantic rules
  spec <- runIO $ parseSpecification path
  case spec of
    Left e     -> fail $ "*** Parse error: " ++ e
    Right lang -> do
      -- runIO $ putStrLn ("Parsed rules: " ++ show (semantics' lang))
      -- runIO $ putStrLn ("Normalized rules: " ++ show (semantics' normalized))

      -- NOTE: we validate that the rules are well formed before generating the interpreters
      case validateLanguage lang of
        Failure es -> fail $ "*** Validation error: " ++ show es
        Success validated  -> do
          normalized <- normalizeSemantics validated

          runIO $ putStrLn "[-] Successfully validated the rules."
          runIO $ putStrLn "[-] Generating interpreters..."
          ntGroups <- groupByNt (semantics' normalized)

          concreteInterpreters <- mapM makeStepFunc ntGroups
          symbolicExecutors    <- mapM makeSymbolicStepFunc ntGroups

          runIO $ putStrLn $ "[-] Successfully generated interpreters for " ++ show (langName lang) ++ "."
          return (concreteInterpreters ++ symbolicExecutors)


interpreterFor :: Identifier -> Q Exp
interpreterFor = return . VarE . interpreterName

symbolicExecutorFor :: Identifier -> Q Exp
symbolicExecutorFor = return . VarE . symbolicExecutorName


{- For each generated data type we want to create both concrete and symbolic small step-functions:
    stepT     :: T Void 
              -> ConcreteState
              -> (Maybe (T Void), ConcreteState)
    
    symbolicT :: T Void 
              -> SymbolicState 
              -> PathCond 
              -> [(Maybe (T Void), SymbolicState, PathCond)]

    Where:
    * T is the type we generated earlier, and Void is used for closed programs
    * Nothing represents terminating programs
    * Function name is "step" ++ nt type name
    * Rules over the same data type are multiple clauses of the same function
    * Pattern for each clause is the constructor applied to normalized names, e.g.,
        stepMeta_P (Meta_Seq p1 p2) a
    
    Note how symbolic executors may have multiple outgoing transitions, represented with a list
-}
makeStepFunc :: [Rule XVar] -> Q Dec
makeStepFunc rules = do
  parent <- ruleParent (head rules)
  let funcName = simpleInterpreterName $ pack $ nameBase parent

  -- Make one clause for each operator with rules
  clauses <- mapM stepClause (groupByOp rules)

  -- Find constructors for parent with missing rules
  missing <- missingOps parent rules

  -- Make wrapper clauses for the missing wrapper constructor(s)
  wrapperClauses <- mapM makeWrapperClause missing

  return $ FunD funcName (clauses ++ wrapperClauses)

makeSymbolicStepFunc :: [Rule XVar] -> Q Dec
makeSymbolicStepFunc rules = do
  parent <- ruleParent (head rules)
  let funcName = simpleSymbExecName $ pack $ nameBase parent

  clauses <- mapM symbStepClause (groupByOp rules)

  missing <- missingOps parent rules
  wrapperClauses <- mapM makeSymbWrapperClause missing

  return $ FunD funcName (clauses ++ wrapperClauses)


{- Constructs with no rule attached, is just a nonterminal wrapper
    meaning the interpreters can simply send it forward to the appropriate one, e.g.,
      stepMeta_P         (Meta_B branching1) a      = stepMeta_Branching         branching1 a
      symbolicStepMeta_P (Meta_B branching1) a cond = symbolicStepMeta_Branching branching1 a cond
-}
makeWrapperClause :: Identifier -> Q Clause
makeWrapperClause opName = do
  (_,argTypes',_) <- consInfo (mkName (unpack opName))
  let var = head (argNames argTypes')                   -- name of the nt it points to, e.g., "branching1"
      pat = ConP (mkName (unpack opName)) [] [VarP var] -- clause pattern, e.g., (Meta_B branching1)
      state = mkName "a"

      -- Find the appropiate interpreter name
      nestedInterp = interpreterName (typePrefix (head argTypes'))

      -- Make the body expression, e.g., stepMeta_Branching branching1 a
      bodyExp = AppE (AppE (VarE nestedInterp) (VarE var)) (VarE state)

  return $ Clause [pat, VarP state] (NormalB bodyExp) []

makeSymbWrapperClause :: Identifier -> Q Clause
makeSymbWrapperClause opName = do
  (_,argTypes',_) <- consInfo (mkName (unpack opName))
  let var = head (argNames argTypes')                   
      pat = ConP (mkName (unpack opName)) [] [VarP var]
      state = mkName "a"
      cond = mkName "cond"

      -- Find the appropiate symbolic executor
      nestedInterp = symbolicExecutorName (typePrefix (head argTypes'))

      -- Make the body, e.g., symbolicStepMeta_Branching branching1 a cond
      bodyExp = AppE (AppE (AppE (VarE nestedInterp) (VarE var)) (VarE state)) (VarE (mkName "cond"))

  return $ Clause [pat, VarP state, VarP cond] (NormalB bodyExp) []

-- Make a clause for each production in the nonterminal
stepClause :: [Rule XVar] -> Q Clause
stepClause rules = do
  -- Since we know the rules are well-formed, 
  -- we use the first one to get information about the operator
  (cName, argTypes', _) <- 
    consInfo (typeName (opName' (head rules)))
  let -- List of normalized argument names, e.g., [b1, p1, p2]
      args = argNames argTypes'            
      -- Make the program part of the clause pattern, e.g., (If b1 p1 p2)
      progPat = ConP cName [] (map VarP args) 
      -- Input state is always "a"
      state   = mkName "a"
  body <- makeBody rules state
  return $ Clause [progPat, VarP state] body []

symbStepClause :: [Rule XVar] -> Q Clause
symbStepClause rules = do
  (cName, argTypes', _) <- consInfo (typeName (opName' rule))
  let args    = argNames argTypes'
      progPat = ConP cName [] (map VarP args)
  body <- makeSymbolicBody rules state pathCond -- make symbolic body
  return $ Clause [progPat, VarP state, VarP pathCond] body [] -- add path condition
  where
    rule     = head rules
    state    = mkName "a"
    pathCond = mkName "cond"


-- ===== Three different kinds of body functions ==== ---
-- 1. no premises no trigger, 2. no premises trigger, 3. with premises
makeBody :: [Rule XVar] -> Name -> Q Body
makeBody rs s
  -- If it has no premises
  | null (premises' (head rs)) =
      if trigger' (head rs) == Top
        then bodyTop     rs s
        else bodyTrigger rs s
  -- If it has premsies
  | otherwise = bodyPremises rs s

makeSymbolicBody :: [Rule XVar] -> Name -> Name -> Q Body
makeSymbolicBody rs s cond
  -- If it has no premises
  | null (premises' (head rs)) =
      if trigger' (head rs) == Top
        then symbolicBodyTop     rs s cond
        else symbolicBodyTrigger rs s cond
  -- If it has premsies
  | otherwise = symbolicBodyPremises rs s cond


{- 1. No premises, trigger == T, simply transition to target prog + update state
      stepMeta_P (Skip)    s = (Nothing, s)
      stepMeta_P (Asg x e) s = (Nothing, updateState a x e)

    Note: Since W is empty, the meta substitution is built from the input state alone

    Symbolic execution makes a list with one element, 
    as the transition with path condition -T is never satisfied
      symbolicStepMeta_P Meta_Skip a cond = [(Nothing, a, cond)]  
    
    Note: We do not need to extend path condition as cond /\ T == cond
-}
bodyTop :: [Rule XVar] -> Name -> Q Body
bodyTop [rule] inputState = do
  metaSubst <- buildMetaSubst [inputState] -- Build meta substitution from inputstate alone
  NormalB <$> transExp rule metaSubst

symbolicBodyTop :: [Rule XVar] -> Name -> Name -> Q Body
symbolicBodyTop [rule] inputState cond = do
  let varExp = VarE cond -- Path condition remains the same
  metaSubst <- buildMetaSubst [inputState]
  bodyExp   <- symbTransExp rule metaSubst varExp
  return $ NormalB (ListE [bodyExp])


{- 2. No premises, trigger /= Top:
    stepMeta_P (Meta_IF b1 p1 p2) a
      | evalBExpr b1 a = (Just p1, a)
      | otherwise      = (Just p2, a)

    stepMeta_P (Meta_WHILE b p) a =
      | evalBExpr b a = (Just (M_Seq p (M_While b p)), a)
      | otherwise     = (Nothing, a)
    
    Note: rule format enforces that there must exist exactly two rules for triggers=/=Top, so we 
    can simplify the second guard with 'otherwise'
  
    Symbolic execution makes a list of outgoing transitions, 
    consisting of two elements: one for b(f) and one for -b(f),
    as both the trigger branches always fire/produce a result.

      symbolicStepMeta_P (Meta_IF b1 p1 p2) a cond
        = [ (Just p1, a, cond ++ b1)
          , (Just p2, a, cond ++ (Not b1))]
    
    Note: trigger gets added to the path condition  
-}
bodyTrigger :: [Rule XVar] -> Name -> Q Body
bodyTrigger [r1, r2] inputState = do
  -- Make meta substitution from input state alone
  metaSubst <- buildMetaSubst [inputState]

  guard1 <- guardExp r1 inputState
  res1 <- transExp r1 metaSubst

  let guard2 = NormalG (VarE 'otherwise)
  res2 <- transExp r2 metaSubst

  return $ GuardedB [(guard1, res1), (guard2, res2)]

symbolicBodyTrigger :: [Rule XVar] -> Name -> Name -> Q Body
symbolicBodyTrigger [r1, r2] inputState inputCond = do
  metaSubst <- buildMetaSubst [inputState]

  -- Make the new path conditions
  cond1 <- pathCondExp r1 inputState inputCond
  cond2 <- pathCondExp r2 inputState inputCond

  res1 <- symbTransExp r1 metaSubst cond1
  res2 <- symbTransExp r2 metaSubst cond2

  -- Function returns a list with both rule-results
  return $ NormalB (ListE [res1, res2])


{- 3. With premises
  Concrete interpreters:
  Use 'case of' to check if each premise returns their target
    step_XXX prog a =
      case [step_XXX p1 a, ...] of
          [(Just p1', a1'), ...] -> (..., updateState a1')
          [(Nothing,  a1'), ...] -> (..., updateState a1')

  If the rule has a trigger /= Top, also add a guard to the case body
          [(Just p1', a1'), ...] | evalBExpr a b -> (..., updateState a1')

  Symbolic executors:
  Since the step of each premise creates a list of outgoing transitions,
  we need to take the cartesian product (X) of all the premise results.
  This is modeled using Haskell's list comprehension.

  An operator with arity n, has the form:
  symbolicStep_XXX (XXX p1 p2 ... pn) a cond =
    [ result
      | -- cartesian product of ALL premise transitions
        p1Res <- step p1 a cond
      , p2Res <- step p2 a cond
      , ... 
      , pnRes <- step pn a cond
      
      , result <- case (p1Res, p2Res, ...) of 
            ((Nothing,  a1', cond1), (Nothing, a2', cond2), ...) -> [...]
            ((Just p1', a1', cond1), (Nothing, a2', cond2), ...) -> [...]
            ...
    ]
-}
bodyPremises :: [Rule XVar] -> Name -> Q Body
bodyPremises rules inputState = do
  -- Find all meta-variables from the premise sources
  -- Assumes all premises have the same set of source meta-variables, so just uses the first one
  let sources = map (mkName . unpack . sourceXVar') (premises' (head rules))

  -- Make what we want to match on, i.e., (step p1 s, ...)
  scrutinee <- ListE <$> mapM (progInterpreter inputState) sources
  matches   <- mapM (makeMatch inputState) rules

  return $ NormalB (CaseE scrutinee matches)
  where
    -- Make function to step each XVar premise source, stepP p a
    progInterpreter :: Name -> Name -> Q Exp
    progInterpreter stateName p = do
      interp <- interpreterFor prog
      return $ AppE (AppE interp (VarE p)) (VarE stateName)

    -- Make one match for each rule
    makeMatch :: Name -> Rule XVar -> Q Match
    makeMatch input rule = do
      let pat = ListP (map makePattern (premises' rule))
          -- Get all output SVars from premises to determine scope
          outputs = map (mkName . unpack . outputSVar') (premises' rule)
          scope   = input : outputs

      metaSubst <- buildMetaSubst scope
      bodyExp   <- transExp rule metaSubst
      body <-
        -- Make guarded body if trigger /= Top
        case trigger' rule of
          Top -> return $ NormalB bodyExp
          _   -> do
            guard <- guardExp rule input
            return $ GuardedB [(guard, bodyExp)]

      return $ Match pat body []

    -- Make case pattern for premsie transition
    makePattern :: Transition XVar -> Pat
    makePattern t =
      -- The premise target is a meta-variable pi' or Nothing
      let targetPat = xVartoPattern $ targetXVar' t
      -- The premise output is a meta-variable ai' 
          outputPat = VarP $ mkName $ unpack $ outputSVar' t
      in TupP [targetPat, outputPat]


symbolicBodyPremises :: [Rule XVar] -> Name -> Name -> Q Body
symbolicBodyPremises rules input cond = do
  -- Find all meta-variables from premise sources
  let pSources = map (mkName . unpack . sourceXVar') (premises' (head rules))

  -- Step on each premise, and make bindings
  bindings <- mapM (makeBinding input cond) pSources

  -- Make a case match for each rule with matching shape
  matches <- mapM (makeSymbolicMatch input cond) (groupByShape rules)

  -- Make what we want to match on, e.g., (p1Res, p2Res, ..., pnRes)
  let scrutinee = ListE (map (VarE . resultName) pSources)
      -- Make case expression and bind it to a variable "result"
      caseExp = CaseE scrutinee matches
      caseBind = BindS (VarP (mkName "result")) caseExp

  -- Make the final result bind, giving the result of the list comprehension
  let resultBind = NoBindS (VarE (mkName "result"))

  -- Return the list comprehension
  return $ NormalB (CompE (bindings ++ [caseBind] ++ [resultBind]))
  where
    -- Bind result of premise step to a result name, e.g., p1Res <- step p1 a cond
    makeBinding :: Name -> Name -> Name -> Q Stmt
    makeBinding input cond sourceName = do
      interp <- symbExecProg input cond sourceName
      return $ BindS (VarP (resultName sourceName)) interp

    -- Result name for each premise step is source name ++ 'Res', e.g, p1Res
    resultName :: Name -> Name
    resultName n = mkName (nameBase n ++ "Res")

    -- Apply the symbolic executor for programs on a program term
    -- i.e., stepSymbolicP metaVar a cond
    symbExecProg :: Name -> Name -> Name -> Q Exp
    symbExecProg stateName cond p = do
      interp <- symbolicExecutorFor prog
      return $
        AppE (AppE (AppE interp (VarE p)) (VarE stateName)) (VarE cond)

    -- Make a match for each trigger pair of rules
    makeSymbolicMatch :: Name -> Name -> [Rule XVar]  -> Q Match
    makeSymbolicMatch input inputCond rules = do
      -- Since we've already validated that the rules are correct for each group, 
      -- we can just base it on the first one
      let rule = head rules
          -- Make a pattern-match for each premise result
          pattern' = ListP (map makeSymbPattern (premises' rule))
          -- Get all output SVars from premises to determine scope
          outputs = map (mkName . unpack . outputSVar') (premises' rule)
          scope   = input : outputs

      metaSubst <- buildMetaSubst scope

      -- Make a case match body for each rule
      bodies <- mapM (makeBodyExp metaSubst) rules
      return $ Match pattern' (NormalB (ListE bodies)) []
      where
        makeBodyExp metaSubst r = do
          cond <- pathCondExp r input inputCond
          symbTransExp r metaSubst cond

    makeSymbPattern :: Transition XVar -> Pat
    makeSymbPattern t =
      -- The premise target is a meta-variable pi' or Nothing
      let targetPat = xVartoPattern $ targetXVar' t
      -- The premise output is a meta-variable ai' 
          outputPat = VarP $ mkName $ unpack $ outputSVar' t
      -- The premise path condition is a variable piCond
          condPat = VarP $ mkName (unpack (sourceXVar' t) ++ "Cond" )
      in TupP [targetPat, outputPat, condPat]

-- Helper function to transform the target xvar to a template-haskell pattern
xVartoPattern :: Maybe XVar -> Pat
xVartoPattern (Just x) = ConP 'Just    [] [VarP $ mkName $ unpack x]
xVartoPattern Nothing  = ConP 'Nothing [] []


-- Generates guard: (evalBExpr state trigger)
guardExp :: Rule XVar -> Name -> Q Guard
guardExp rule sName = do
  trigExp <- lift (trigger' rule)
  return $ NormalG $ AppE (AppE (VarE 'evalBExpr) (VarE sName)) trigExp

-- Extends path condition with substiuted trigger and premise conditions
-- inputCond /\ (triggerCond) /\ premiseConds
pathCondExp :: Rule XVar -> Name -> Name -> Q Exp
pathCondExp rule inputState inputCond = do
  -- Add trigger to path condition iff trigger /= Top 
  let trigger = trigger' rule
  base <-
    if trigger /= Top
    then do
      trigExp <- lift trigger
      -- Simplify the trigger before adding it to the path condition
      let trigCond =
            ListE
              [AppE (AppE (VarE 'simplifyBExpr) (VarE inputState)) trigExp ]
      return $
        UInfixE (VarE inputCond) (VarE '(++)) trigCond

    else return $ VarE inputCond

  -- Get the path conditions from all premises
  let premiseConds = map makePremiseCond (premises' rule)

  -- Propogate all the path conditions produced by the premises to the conclusion's path condition
  return $ foldl addPremiseCond base premiseConds
  where
    -- Name of the premise condition is just its sourcename ++ Cond, e.g., p1Cond
    makePremiseCond t =
      VarE $ mkName (unpack (sourceXVar' t) ++ "Cond")

    -- Chain add the premise conditions
    addPremiseCond acc = UInfixE acc (VarE '(++))


-- Generate the configuration the conclusion transitions to
transExp :: Rule XVar -> Exp -> Q Exp
transExp rule metaSubst = do
  let conc = concTrans rule
  pExp <- targetExp conc
  sExp <- outputExp conc metaSubst 'updateState
  return $ TupE [Just pExp, Just sExp]

symbTransExp :: Rule XVar -> Exp -> Exp -> Q Exp
symbTransExp rule metaSubst cond = do
  let conc = concTrans rule
  pExp <- targetExp conc
  sExp <- outputExp conc metaSubst 'updateStateSym
  return $ TupE [Just pExp, Just sExp, Just cond]

targetExp :: Transition XVar -> Q Exp
targetExp tr =
  case targetProg tr of
    Nothing -> return $ ConE 'Nothing
    Just p  -> do
      p' <- liftProg p
      return $ AppE (ConE 'Just) (removeMVar p')

outputExp :: Transition XVar -> Exp -> Name -> Q Exp
outputExp tr metaSubst updateFunc =
  case outputState tr of
    S sVar ->
      return $ VarE (mkName (unpack sVar))

    Update sVar ups -> do
      upsExp <- mapM liftUpdate ups
      let updateExp = AppE (AppE (ConE 'Update) (textExp sVar)) (ListE upsExp)
      return $ AppE (AppE (VarE updateFunc) metaSubst) updateExp -- updateFunc metaSubst (Update s ups)

  where
    liftUpdate :: ($(typeFor var), SVar, Expr) -> Q Exp
    liftUpdate (var, s, e) = do
      let s' = textExp s
      var' <- lift var -- lift to TH name    
      e'   <- lift e
      eExp <- toExp e'
      return $ TupE [Just var', Just s', Just eExp]
    
    -- Wrap Exp in Var if it is an identifier to make it an Expr
    toExp :: Exp -> Q Exp
    toExp (VarE n) 
      | prefix (nameBase n) == unpack var = do
          toVar <- [| \(MX x) -> Var x |]
          return $ AppE toVar (VarE n)
    toExp (AppE x y) = do 
      x' <- toExp x
      y' <- toExp y
      return $ AppE x' y'
    toExp e = return e

    -- Strip digit suffix
    prefix :: String -> String
    prefix = reverse . dropWhile isDigit . reverse


-- ==== Meta Substitution builder ====
{- Need to build the meta substitution (psi) from the context, and apply it to the conclusion result.
  
  The psi is built from all bindings available at the point of applying it, that is:
    1. input
    2. each premise output
  
  Note: The meta substitution is constructed per rule application,
  and it's the body functions that have the responsibility to provide the correct name scope

  Want to construct a map from names (which are bound to concrete/symbolic states), 
  and its sVar name, i.e., the expression:
    M.fromList [("a", a), ("a1'", a1'), ...]
-}
buildMetaSubst :: [Name] -> Q Exp
buildMetaSubst states = do
  entries <- mapM makeBinding states
  return $ AppE (VarE 'M.fromList) (ListE entries)
  where
    makeBinding sName = do
      key <- lift (pack (nameBase sName))
      return $ TupE [Just key, Just (VarE sName)]


-- ======= Miscellaneous helper functions =======
-- Interpreter name without type prefix "Meta"
simpleInterpreterName :: Identifier -> Name
simpleInterpreterName name = mkName $ "step" ++ unpack name

simpleSymbExecName :: Identifier -> Name
simpleSymbExecName name = mkName $ "symbolicStep" ++ unpack name

-- Interpreter name with type prefix
interpreterName :: Identifier -> Name
interpreterName name = mkName $ "step" ++ nameBase (typeName name)

symbolicExecutorName :: Identifier -> Name
symbolicExecutorName name = mkName $ "symbolicStep" ++ nameBase (typeName name)

-- ==== Grouping helpers ====
-- Group rules by their parent/nonterminal
groupByNt :: [Rule XVar] -> Q [[Rule XVar]]
groupByNt [] = return []
groupByNt (r:rs) = do
  p <- ruleParent r
  same <- filterM (sameParent p) rs
  rest <- filterM (differentParent p) rs
  restGroups <- groupByNt rest

  return ((r:same) : restGroups)
  where
    sameParent p r = do
      p' <- ruleParent r
      return (p == p')

    differentParent p r = do
      p' <- ruleParent r
      return (p /= p')

-- Group rules by operator name
groupByOp :: [Rule XVar] -> [[Rule XVar]]
groupByOp = groupBy ((==) `on` opName') . sortOn opName'

-- Find the operators that doesn't have an attached rule
missingOps :: Name -> [Rule XVar] -> Q [Identifier]
missingOps parent rules = do
  allCons <- allConstructors parent
  let usedOps = map opName' rules
      metaOps = map addPrefix usedOps
  
  -- Find all names in allCons that is not used in the semantic-rules
  return $ filter (isMissing metaOps) allCons
  where
    addPrefix op = "Meta_" <> pack (capitalizeFirst (unpack op))
    isMissing metaOps op =
        op /= "MVar" && op `notElem` metaOps
