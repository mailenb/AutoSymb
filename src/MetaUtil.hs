{-# LANGUAGE TemplateHaskell #-}

-- Helper functions used in Validate.hs, Normalize.hs and MetaInterpreter.hs
module MetaUtil where

import Syntax (Identifier, prog)
import Semantics
import MetaParser (typeFor, typeName, lowerFirst)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (lift)
import TH.Utilities (ExpLifter(..))

import Data.Text (pack, unpack, stripPrefix, Text)

-- ==== Lift help functions ====
liftProg :: $(typeFor prog) XVar -> Q Exp
liftProg p = lift (substMetaVars p)

-- Wrap Exp inside ExpLifter to fix that lift can't be used on Exp
substMetaVars :: $(typeFor prog) XVar -> $(typeFor prog) ExpLifter
substMetaVars = fmap toExpLifter
  where
    toExpLifter :: XVar -> ExpLifter
    toExpLifter x = ExpLifter $ return $ VarE $ mkName $ unpack x

-- Remove MVar constructor from variable name by recursively unwrapping the applications
-- and removing the MVar constructor, leave the other constructors as normal
removeMVar :: Exp -> Exp
removeMVar (AppE (ConE c) x)
  | c == 'MVar        = x
removeMVar (AppE x y) = AppE (removeMVar x) (removeMVar y)
removeMVar p          = p


-- ==== Reification helpers ====
-- We use reify to get information about the constructor
consInfo :: Name -> Q (Name, [Type], Name)
consInfo tyName = do
  Just cName <- lookupValueName (nameBase tyName)
  info       <- reify cName
  case info of
    DataConI name t parentName -> return (name, argTypes t, parentName)
    _                          -> fail "unknown data constructor"

ruleParent :: Rule XVar -> Q Name
ruleParent r = do
  (_,_,p) <- consInfo (typeName (opName' r))
  return p

-- Get the names of all constructors to the data type
allConstructors :: Name -> Q [Identifier]
allConstructors dataType = do
  Just nt <- lookupTypeName (nameBase dataType)
  info    <- reify nt
  case info of
    TyConI dec ->
      case dec of
        DataD _ _ _ _ cons _ -> return (map conName cons)
  where
    conName :: Con -> Identifier
    conName (NormalC name _) = pack $ nameBase name

-- ==== Name normalizing helpers ====
-- Flattens the type of the constructor to get its argument types
-- e.g., the type of the constructor IF 'BExpr -> Meta_P x -> Meta_P x' gives the list [BExpr, Meta_P x, Meta_P x]
argTypes :: Type -> [Type]
argTypes (ForallT _ _ t)                        = argTypes t
argTypes (AppT (AppT (AppT MulArrowT _) t1) t2) = t1 : argTypes t2
argTypes (AppT (AppT ArrowT t1) t2)             = t1 : argTypes t2
argTypes _                                      = []

{- Normalize argument names: type prefix + number
    * BExpr -> b1
    * Expr  -> e1
    * Generated data types -> Meta_P -> p1 -}
argNames :: [Type] -> [Name]
argNames = names []
  where
    names :: [Text] -> [Type] -> [Name]
    names seen [] = []
    names seen (t:ts) =
      let prefix = typePrefix t
          n      = count prefix seen + 1
          name   = mkName (unpack prefix ++ show n)
      in name : names (prefix : seen) ts

    -- count how many of that prefix we have already seen
    count :: Text -> [Text] -> Int
    count prefix = length . filter (== prefix)

typePrefix :: Type -> Text
typePrefix (ConT n)   =
  case pack (nameBase n) of
    "BExpr" -> "b"
    "Expr"  -> "e"
    "Text"  -> "t"
    n'       -> do
      -- Remove the type prefix name and make it lowercase
      case stripPrefix "Meta_" n' of
        Just n'' -> pack  $ lowerFirst $ unpack n''
        Nothing  -> error $ "Couldn't make argument name from: " ++ unpack n'
typePrefix (AppT t _) = typePrefix t
typePrefix t          = error $ "unknown argument type: " ++ show t

