{-# LANGUAGE TemplateHaskell #-}
module Validate where

import Syntax
import Semantics

import MetaParser (typeFor)
import MetaUtil

import Data.Text (Text, pack, unpack)
import Data.List (groupBy, sortOn, nub, sort)
import Data.Function (on)
import Data.List.Unique (repeated)

import Data.Maybe (catMaybes, mapMaybe)
import Data.Foldable (Foldable(toList), traverse_)

{- 
  data Validation e a
  = Failure e
  | Success a

  is applicative, which means we can run all possible checks,
   and it returns Sucess only if **all** of them passes
-}
import Data.Validation (Validation(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Bifunctor (first)

-- import qualified Data.Map as M
-- import Data.Data

data ValidationError
  = LangErr LanguageError
  | OpErr OperatorError
  | RuleErr RuleError
  deriving (Show) -- Eq

data LanguageError
  -- Operator defined in syntax without a corresponding semantic rule
  = MissingRule Identifier
  -- "No rules for operator " ++ name

  deriving (Eq, Show)

data OperatorError
  -- Two rules for same operator whose triggers arent complementary (b and -b)
  = NonComplementaryTriggers Identifier Identifier
    -- "Triggers for operator " ++ name ++ " are not complementary (" ++ (trigger' r1) ++ " and " ++ (trigger' r2) ++ ")" 
 
  -- Group consists of a single rule with a non-trivial trigger 
  | MissingComplementaryRule Identifier Identifier
   --  "Operator " ++ name ++ " has only one rule, but trigger is non-trivial. " 

  -- Group contains more than 2 rules 
  | TooManyRules [Identifier]
  -- "Operator " ++ name ++ " has " ++ length rs ++ " rules, but can at most consist of two." 

  --                     opName    ruleName  arity n
  | InvalidPremiseCount Identifier Identifier Int Int

  --                     opName    required actual
  | InsufficientCoverage Identifier Int Int

  --                   opName   required actual
  | DuplicateCoverage Identifier Int Int
  deriving (Eq, Show)

data RuleError
  = IllegalInputUpdate State' 
  | InvalidInput Identifier [SVar]

  | IllegalPremiseUpdate State'
  | InvalidOutput Identifier [SVar]

  | InvalidPermiseSource ($(typeFor prog) XVar)
  | InvalidPermiseSourceName Identifier [XVar]
  | RepeatedPermiseSourceName Identifier [XVar]

  | InvalidPremiseTarget ($(typeFor prog) XVar)
  | InvalidPremiseTargetName Identifier [XVar]

  | InvalidConclusionTarget Identifier [XVar]
  | InvalidConclusionSource Identifier String 

  | InvalidTrigger Identifier BExpr

  deriving (Show) -- Eq


{- 1. validateLanguage/RuleSet: validates the set of ALL rules
      * check if they cover all operators in pSyntax (minus simple wrappers) 
  
  TODO: update notes with correct information!
  In order to reduce the complexity of the interpreter generator, 
  as well as avoiding creating step functions that are never used,
  I have redefined what it means for the rules to be well-defined:
  * Iff trigger == Top, a complimentary rule may be omitted, as a rule with trigger Bottom will never be satisfied

  * Iff neither the target nor output of a premise is used in 
    the conclusion's target or output, the premise **must be??** omitted

    unused premises **must be** omitted
    * can for each rule check if rule has any unused premises
        * then make the W only from the subterms that appear as premise sources

    * if w length /= 2^arity:
        * check if the meta variables used in the conclusion target has a combinations 
          of terminating/progressive premisses

    unused premises **may be** omitted
-}

-- allow reporting of multiple errors at the same time
validateLanguage :: Language -> Validation (NonEmpty ValidationError) Language
validateLanguage lang =
  lang
    <$ first (fmap LangErr) (validateCoverage lang)

    -- validate the form of each rule
    <* first (fmap RuleErr) (traverse validateRule (semantics' lang))

    -- group by operators and validate each group  
    <* first (fmap OpErr) (traverse validateOperator groupedByOp)
  
  where
    sameOp r1 r2 = opName' r1 == opName' r2
    groupedByOp = groupBy sameOp . sortOn opName' $ semantics' lang


validateCoverage :: Language -> Validation (NonEmpty LanguageError) ()
validateCoverage lang = traverse_ checkOp allSyntax
  where
    allSyntax = concatMap getNames (pSyntax (syntax' lang)) -- all operator names in program syntax
    allSemantics = nub(map opName' (semantics' lang))       -- all operator names with rules

    progNts = map ntName (pSyntax (syntax' lang))

    -- Validate that all names in syntax have a rule attached to them 
    checkOp :: Identifier -> Validation (NonEmpty LanguageError) ()
    checkOp name =
      if name `elem` allSemantics
        then Success ()
        else Failure $ MissingRule name :| []

    getNames :: NonTerminal -> [Identifier]
    getNames nt = concatMap getProdName (ntRules nt)

    getProdName :: Production -> [Identifier]
    getProdName (Production [NTRef nt] name)
      | nt `elem` progNts           = []     -- ignore program wrapper productions
    getProdName (Production _ name) = [name]
    getProdName (Regex _ name)      = [name]


{-   2. validateOperator: validates the set of all rules for the **same operator**  
      * check if it has the right amount of rules -> each operator needs rule(s) covering **all cases**
        * group the rules for each operator into all their combinations of progressive and terminating premises

      Validate each group:
      * If rule-group has premises: 
          * does it have all the combinations for progressive/terminating premises?
      * If rule-group has trigger /= Top:
        * Group must consist of two rules with complementary triggers (b, !b)

      W: which subterms that take a progressive step

      "for every progressive operator f, and for every 
      subset of W < {1, ..., arity}, there are exactly
      two rules R1, R2 such that:
        - the premises of both R1 and R2 are progressive
        - the other premises of both R1 and R2 are terminating
        => and the triggers of the rules are complimentary "

      => There are exactly 2^n possible W sets for an operator of arity n
      * one for each subset of {1,...,n}
      With trigger: 2^(n+1)
-}
validateOperator :: [Rule XVar] -> Validation (NonEmpty OperatorError) [Rule XVar]
validateOperator rules = 
  rules <$ 
    ( validatePremiseCount 
    *> validateCoverage
    *> validateTriggerPairs
    )
  where
    arity  = getArity (head rules)
    opName = opName'  (head rules)
    w = groupByShape rules

    -- Every rule must have the same exact number of premises
    validatePremiseCount :: Validation (NonEmpty OperatorError) ()
    validatePremiseCount = traverse_ checkPremise rules
      where
        checkPremise rule = 
          let n = length (premises' rule)
          in if n == arity 
            then Success ()
            else Failure $ InvalidPremiseCount opName (ruleName rule) arity n :| []
    
    validateCoverage :: Validation (NonEmpty OperatorError) ()
    validateCoverage = 
      let wLength = length w
          required = 2 ^ arity
      in if wLength == required
        then Success ()
        else if wLength < required
            then Failure $ InsufficientCoverage opName required wLength :| [] 
            else Failure $ DuplicateCoverage    opName required wLength :| [] 

    validateTriggerPairs :: Validation (NonEmpty OperatorError) ()
    validateTriggerPairs = traverse_ validatePair w

    {- Note: Because we allow the user to omit rules for shapes of XVar-premises that is
      unused in conclusion target/output, we redefine the arity to mean the number
      of premises in the rule. -}
    getArity :: Rule XVar -> Int
    getArity rule = length (premises' rule)


groupByShape :: [Rule XVar] -> [[Rule XVar]]
groupByShape = 
  groupBy ((==) `on`premiseShape) . sortOn premiseShape 
  where
    premiseShape :: Rule XVar -> [Bool]
    premiseShape r = map isProgressive (premises' r)

    isProgressive :: Transition XVar -> Bool 
    isProgressive (Progressive _ _) = True
    isProgressive (Terminating _ _) = False


validatePair :: [Rule XVar] -> Validation (NonEmpty OperatorError) ()
validatePair rules =
  case rules of
    [r]
      | trigger' r == Top -> Success ()  -- or do some simple rewriting to check if it reduces to top?
      | otherwise         -> Failure $ pure $ MissingComplementaryRule (opName' r) (ruleName r)

    [r1, r2]
      | areComplementary (trigger' r1) (trigger' r2) -> Success ()
      | otherwise -> Failure $ pure $ NonComplementaryTriggers (ruleName r1) (ruleName r2)

    -- Must only be at most two rules for each rule pair
    rs -> Failure $ pure $ TooManyRules (map ruleName rs)


-- simple checks for now, extend with simple SAT checking later?
areComplementary :: BExpr -> BExpr -> Bool
areComplementary Top      Top      = False
areComplementary (Not b1) b2       = b1 == b2
areComplementary b1       (Not b2) = b1 == b2

-- areComplementary (Comparison (Less e1 e2)) 
--                  (Comparison (More e1' e2'))  = e1 == e1' && e2 == e2'

areComplementary _        _        = False


{- 3. validateRule: cover definition 1 by checking if each rule is well-defined
      * the input of each premise AND the conclusion input must be the **same** SVar

      * if premise is progressive, its target must be another meta-variable y
      * the output of each premise must be a simple SVar (no update)
      * each premise output and premise targets need to be **fresh** meta names
      
      * each premise-source i must be a meta-variable in the conclusion's source

      * if the conclusion is progressive, its target may be composed of the original
         subterm-meta-variables and/or the (progressive) premise targets yi, 
         into a new program term freely

      * the conclusion output may be a compound state, composed of the input state
        and/or the premise-outputs    
-}
validateRule :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validateRule rule =  
  rule <$ 
    (  validateIdenticalInput rule
    *> validatePremiseOutputs rule
    *> validatePremiseSources rule
    *> validatePremiseTargets rule
    *> validateConcOutput rule
    *> validateConcTarget rule
    )

validateIdenticalInput :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validateIdenticalInput rule =
  case liftA2 (,) (inputSVar (concTrans rule)) 
                  (traverse inputSVar (premises' rule)) of
    Failure e -> Failure e
    Success (inputConc, inputPremises) ->
      -- Find all (invalid) inputs that are not equal to the conclusion's input
      let invalidInput = filter (/= inputConc) inputPremises
      in if null invalidInput
        then Success rule -- Succeed if they are all equal
        else Failure $ 
          InvalidInput (ruleName rule) invalidInput :| []

-- the output of each premise must be a simple, and fresh, SVar (no update, no repeats)
validatePremiseOutputs :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validatePremiseOutputs rule =
  case liftA2 (,) (inputSVar (concTrans rule))
                  (traverse outputSVar (premises' rule)) of
    Failure e -> Failure e
    Success (input, outputs) ->
      let repeatedOuts = repeated (input : outputs)
      in if null repeatedOuts
        then Success rule
        else Failure $ 
          InvalidOutput (ruleName rule) repeatedOuts :| []

-- Each premise targets (if progressive) need to be **fresh** meta variable yi
validatePremiseTargets :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validatePremiseTargets rule =
  case traverse targetXVar (premises' rule) of
    Failure e -> Failure e
    Success premiseTargets ->
      -- Find the (illegaly) repeated XVar values in the terminating premises
      let repeatedXVars = repeated (catMaybes premiseTargets)
      in if null repeatedXVars
          then Success rule
          else Failure $ 
            InvalidPremiseTargetName (ruleName rule) repeatedXVars :| []

-- The source of each premise must be an unique meta-variable in the conclusion's source
validatePremiseSources :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validatePremiseSources rule =
  case traverse sourceXVar (premises' rule) of
    Failure e              -> Failure e
    Success premiseSources ->
      -- Check if there exists any premise sources that is not a meta variable the conclusion's source
      let unknown = filter (`notElem` concXVars) premiseSources
      in if null unknown 
          then 
            let repeatedXVars = repeated premiseSources
            in if null repeatedXVars
              then Success rule
              else Failure $ 
                RepeatedPermiseSourceName (ruleName rule) repeatedXVars :| []
          else Failure $ 
            InvalidPermiseSourceName (ruleName rule) unknown :| []
  where
    concXVars = toList (sourceProg (concTrans rule))

-- the conclusion output may be a compound state, composed of the input state and/or the premise-outputs
validateConcOutput :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validateConcOutput rule =
  case liftA2 (,) (inputSVar (concTrans rule))
                  (traverse outputSVar (premises' rule)) of 
    Failure e -> Failure e
    Success (concInput, premiseOuts) ->
      let scope = (concInput : premiseOuts)
      in case concOutput of
        S s          -> validateSVar scope s
        Update s ups -> validateSVar scope s
                          <* traverse_ (validateUpdate scope) ups 
  where
    concOutput = outputState (concTrans rule)

    -- Validate that the sVar is in scope
    validateSVar scope s =
      if s `elem` scope
        then Success rule
        else Failure $ InvalidOutput (ruleName rule) [s] :| []

    -- Validate that the evaluation state is in scope
    validateUpdate scope (_, evalState, _) = validateSVar scope evalState

{- For progressive rules, its target may be composed of the original
    subterm meta-variables and/or the (progressive) premise targets yi, 
    into a new program term freely -}
validateConcTarget :: Rule XVar -> Validation (NonEmpty RuleError) (Rule XVar)
validateConcTarget rule =
  rule <$ validateTarget
  where
    source = sourceProg (concTrans rule)
    target = targetProg (concTrans rule)

    -- meta variables in conclusion source
    sourceXVars = toList source
    -- meta variables in premise targets
    pXVars = mapMaybe targetXVar' (premises' rule) 
    
    -- all meta variables the conclusion target may use freely 
    scope = sourceXVars ++ pXVars

    validateTarget = do
      case target of
        Nothing -> Success ()
        Just p ->
          -- check if there exists any meta variables in target that doesn't exist in the scope 
          let unknownVars = filter (`notElem` scope) (toList p)
          in if null unknownVars
            then Success ()
            else Failure $ InvalidConclusionTarget (ruleName rule) unknownVars :| []


-- ==== Getter functions that also validate ====
-- Premise sources must be a meta-variable
sourceXVar :: Transition XVar -> Validation (NonEmpty RuleError) XVar
sourceXVar (Progressive (MVar p, _) _) = Success p
sourceXVar (Terminating (MVar p, _) _) = Success p
sourceXVar (Progressive (prog,  _)  _) = Failure $ InvalidPermiseSource prog :| []
sourceXVar (Terminating (prog,  _)  _) = Failure $ InvalidPermiseSource prog :| []

-- Premise targets must be meta variables
targetXVar :: Transition XVar -> Validation (NonEmpty RuleError) (Maybe XVar)
targetXVar (Progressive _ (MVar p, _)) = Success $ Just p
targetXVar (Progressive _ (prog, _))   = Failure $ InvalidPremiseTarget prog :| []
targetXVar (Terminating _ _)           = Success Nothing

-- Input states must be meta variables
inputSVar :: Transition XVar -> Validation (NonEmpty RuleError) SVar
inputSVar (Progressive (_, S sVar) _) = Success sVar
inputSVar (Terminating (_, S sVar) _) = Success sVar
inputSVar (Progressive (_, update) _) = Failure $ IllegalInputUpdate update :| []
inputSVar (Terminating (_, update) _) = Failure $ IllegalInputUpdate update :| []

-- Premise outputs must be meta variable
outputSVar :: Transition XVar -> Validation (NonEmpty RuleError) SVar
outputSVar (Progressive _ (_, S sVar)) = Success sVar
outputSVar (Terminating _ (S sVar))    = Success sVar
outputSVar (Progressive _ (_, update)) = Failure $ IllegalPremiseUpdate update :| []
outputSVar (Terminating _ update)      = Failure $ IllegalPremiseUpdate update :| []
