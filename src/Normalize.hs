{-# LANGUAGE TemplateHaskell #-}
module Normalize (normalizeSemantics) where

import Syntax
import Semantics
import MetaUtil
import MetaParser (typeFor, typeName, lowerFirst)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (lift)

import Control.Monad (when)

import Data.Text (pack, unpack, stripPrefix, Text)
import Data.Maybe (mapMaybe, fromJust, fromMaybe)
import Data.List ( sortOn )
import Data.Generics (extT, everywhere, mkT)
import qualified Data.Map as M


{- ===== Normalizing the rules =====

  To simplify the interpreter generator, we need to normalize the rules

  For that we need to maps of the original value and their normalized equivalent for:
  * NameMap: Map Text Text

  Need a substitution on meta-variable names
  mapping: old name -> canonical name
  then apply it everywhere in the rule
  i.e., to the 
    premise sources + targets + outputs
    conclusion source + target + output

  input state -> "a"
  target of (progressive) premise i -> show i <> "'",  e.g., "p1'", "p2'"
  output of premise i -> show i <> "Res",  e.g., "p1Res", "p2Res"
-}

-- nameMap = {actualName |-> canonName}
-- e.g., {x -> p1, y -> p2, x' -> p1', state -> a, state1 -> a1'}
type NameMap = M.Map Text Text

normalizeSemantics :: Language -> Q Language
normalizeSemantics (Language name syn sem) =
  Language name syn <$> mapM normalizeRule sem

normalizeRule :: Rule XVar -> Q (Rule XVar)
normalizeRule rule = do
  nameMap <- buildNameMap
  let normalized = applySubst rule nameMap
  -- runIO $ do
  --   putStrLn "---- BEFORE -----"
  --   print rule
  --   putStrLn "---- AFTER -----"
  --   print normalized
  return normalized
  where
    op = opName' rule
    input = inputSVar' (concTrans rule)

    -- Build the full substitution name map {old name |-> canon name}
    buildNameMap :: Q NameMap
    buildNameMap = do
      -- Get the canonical XVar names from the constructor's argument types
      (_, argTypes', _) <- consInfo (typeName op)
      let canon = map (pack . nameBase) (argNames argTypes')

      -- Extract the actual variable names used
      actual <- getVars (sourceProg (concTrans rule))

      -- Sanity check for getVars, verify that they are of the same length
      when (length actual /= length canon) $
        error $ "normalizeRule: mismatched variable counts in target program in " ++ show (ruleName rule) ++ 
              ". Expected: " ++ show canon ++ ", actually got: " ++ show actual

      -- Build the source map by zipping them together -> [("prog1", "p1"), ...]
      let sourceMap = M.fromList (zip actual canon)

          -- Build premise target map
          targetMap = map (normalizeMetaVar sourceMap "'") premisePairs

          inputMap = [(input, "a")] -- input is always 'a'
          -- outputs are p1Res, p2Res etc.
          outputMap = map (normalizeMetaVar sourceMap "Res") premiseOutputPairs

      return $
        sourceMap <> M.fromList (targetMap ++ inputMap ++ outputMap)

    -- Extract (source, target) pairs from premises
    premisePairs :: [(XVar, XVar)]
    premisePairs =
      mapMaybe makePair (premises' rule) -- Ignore terminating premises
      where
        makePair t =
          case targetXVar' t of
            Just target -> Just (sourceXVar' t, target)
            Nothing     -> Nothing

    -- Extract (source, output) pairs from premises
    premiseOutputPairs :: [(XVar, SVar)]
    premiseOutputPairs =
        [(sourceXVar' t,  outputSVar' t) | t <- premises' rule]

    -- Normalize target meta variables, (source svar, target svar)
    normalizeMetaVar :: NameMap -> Text -> (Text, Text) -> (Text, Text)
    normalizeMetaVar m postfix (source, target) =
      case M.lookup source m of
        Just base -> (target, base <> postfix)
        Nothing   -> error $ "normalizeMetaVar: missing source for " ++ unpack source

-- Variable extraction
getVars :: $(typeFor prog) XVar -> Q [Text]
getVars p =
  -- Lift the program and collect the variables
  collectVars <$> liftProg p
  where
    collectVars :: Exp -> [Text]
    collectVars (VarE x)
      | nameBase x /= "unpackCStringLen#" =
        [pack $ nameBase x]

    -- For user variable x
    collectVars (LitE (BytesPrimL bs)) =
      [pack $ show bs]

    collectVars (AppE x y) =
      collectVars x ++ collectVars y

    collectVars _ = []

-- Apply substitution on the rule -> renaming
applySubst :: Rule XVar -> NameMap -> Rule XVar
applySubst (Rule name op t ps (Conclusion c)) nameMap =
  Rule
    name
    op
    (renameBExpr nameMap t)
    (sortPremises (map (substTrans nameMap) ps))
    (Conclusion (substTrans nameMap c))

  where
    -- Sort premises by the numeric part of the source XVar
    sortPremises :: [Transition XVar] -> [Transition XVar]
    sortPremises = sortOn premiseKey

    premiseKey :: Transition XVar -> Int
    premiseKey p = read $ unpack $ stripP $ sourceXVar' p

    -- Strip the 'prog' prefix to safely sort rules with arity > 9
    stripP :: Text -> Text
    stripP p = fromMaybe 
      (error $ "Couldn't get number from name: " ++ unpack p) 
      (let prefix = pack $ lowerFirst $ unpack prog
       in stripPrefix prefix p)


substTrans :: NameMap -> Transition XVar -> Transition XVar
substTrans nameMap tr =
  case tr of
    (Progressive (p1, s1) (p2, s2)) ->
      Progressive
        (renameConfig nameMap p1 s1)
        (renameConfig nameMap p2 s2)

    (Terminating (p1, s1) s2) ->
      Terminating
        (renameConfig nameMap p1 s1)
        (renameState nameMap s2)
  where
    renameConfig nameMap p s =
      (renameProg nameMap p, renameState nameMap s)

-- Renaming helpers
rename :: NameMap -> Text -> Text
rename m x = M.findWithDefault x x m

renameVar :: NameMap -> $(typeFor var) -> $(typeFor var)
renameVar m (MX x) = MX (rename m x)

renameExpr :: NameMap -> Expr -> Expr
renameExpr m (Var x) = Var (rename m x)
renameExpr m (Num n) = Num n
renameExpr m (Op op e1 e2) =
  Op op
  (renameExpr m e1)
  (renameExpr m e2)

renameBExpr :: NameMap -> BExpr -> BExpr
renameBExpr m (BVar b) = BVar (rename m b)
renameBExpr _ Top = Top
renameBExpr m (Not b) = Not (renameBExpr m b)
renameBExpr m (Logic op b1 b2) =
  Logic op
  (renameBExpr m b1)
  (renameBExpr m b2)
renameBExpr m (Comparison op e1 e2) =
  Comparison op
  (renameExpr m e1)
  (renameExpr m e2)

renameState :: NameMap -> State' -> State'
renameState m (S s) = S (rename m s)
renameState m (Update s ups) =
  Update
    (rename m s)
    (map (renameUpdate m) ups)
  where
    renameUpdate :: NameMap -> ($(typeFor var), SVar, Expr) -> ($(typeFor var), SVar, Expr)
    renameUpdate m (var, s, e) = (renameVar m var, rename m s, renameExpr m e)

renameXVar :: NameMap -> $(typeFor prog) XVar -> $(typeFor prog) XVar
renameXVar m (MVar x) = MVar (rename m x)
renameXVar _ x = x

-- Do generic transformations over the program term thereby renaming each part of the term
renameProg :: NameMap -> $(typeFor prog) XVar -> $(typeFor prog) XVar
renameProg m = everywhere
  (    mkT (renameXVar m)
    `extT` renameExpr m
    `extT` renameBExpr m
    `extT` renameVar m
  )
