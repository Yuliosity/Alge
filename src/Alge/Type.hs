{-# LANGUAGE LambdaCase #-}

module Alge.Type where

import Alge.Syntax (Name, SType)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

type Variable = Int

data Type
  = TInt | TV Variable | TRecord Row | TVariant Row
  | TFun Type Type | TNamed Name [Type] | TRec Variable Type
  deriving (Eq, Ord, Show)

data Row = Row (Map Name Type) (Maybe Variable) deriving (Eq, Ord, Show)

data MergeMode = Compatible | Disjoint deriving (Eq, Ord, Show)
data Constraint = Merge MergeMode Row Row Row | Lacks Name Row
  deriving (Eq, Ord, Show)

data Scheme = Scheme [Variable] [Constraint] Type deriving (Eq, Show)
data Alias = Alias [Name] SType deriving (Eq, Show)
type Aliases = Map Name Alias
type TypeEnv = Map Name Scheme

newtype TypeError = TypeError String deriving (Eq, Show)

emptyRow :: Row
emptyRow = Row M.empty Nothing

unitType :: Type
unitType = TRecord emptyRow

boolType :: Type
boolType = TVariant (Row (M.fromList [("true", unitType), ("false", unitType)]) Nothing)

freeType :: Type -> Set Variable
freeType = \case
  TInt -> S.empty
  TV v -> S.singleton v
  TRecord r -> freeRow r
  TVariant r -> freeRow r
  TFun a b -> freeType a `S.union` freeType b
  TNamed _ ts -> S.unions (map freeType ts)
  TRec v body -> S.delete v (freeType body)

-- Unlike freeType, this includes bound recursive IDs; a new inference session
-- must not recycle them and capture fresh variables inside a recursive type.
allTypeVariables :: Type -> Set Variable
allTypeVariables = \case
  TInt -> S.empty
  TV v -> S.singleton v
  TFun a b -> allTypeVariables a `S.union` allTypeVariables b
  TNamed _ ts -> S.unions (map allTypeVariables ts)
  TRec v body -> S.insert v (allTypeVariables body)
  TRecord r -> allRowVariables r
  TVariant r -> allRowVariables r

allRowVariables :: Row -> Set Variable
allRowVariables (Row fs rest) = S.unions (maybe [] (\v -> [S.singleton v]) rest ++ map allTypeVariables (M.elems fs))

allConstraintVariables :: Constraint -> Set Variable
allConstraintVariables = \case
  Merge _ a b c -> S.unions (map allRowVariables [a,b,c])
  Lacks _ r -> allRowVariables r

freeRow :: Row -> Set Variable
freeRow (Row fields rest) = S.unions (maybe [] (\v -> [S.singleton v]) rest ++ map freeType (M.elems fields))

freeConstraint :: Constraint -> Set Variable
freeConstraint = \case
  Merge _ a b c -> S.unions (map freeRow [a,b,c])
  Lacks _ r -> freeRow r

freeScheme :: Scheme -> Set Variable
freeScheme (Scheme vs cs t) = (freeType t `S.union` S.unions (map freeConstraint cs)) S.\\ S.fromList vs

-- Rename both type variables and row variables with the same fresh-ID supply.
renameType :: Map Variable Variable -> Type -> Type
renameType m = \case
  TInt -> TInt
  TV v -> TV (M.findWithDefault v v m)
  TRecord r -> TRecord (renameRow m r)
  TVariant r -> TVariant (renameRow m r)
  TFun a b -> TFun (renameType m a) (renameType m b)
  TNamed n ts -> TNamed n (map (renameType m) ts)
  TRec v body -> TRec v (renameType (M.delete v m) body)

renameRow :: Map Variable Variable -> Row -> Row
renameRow m (Row fs tailVar) = Row (M.map (renameType m) fs) (fmap (\v -> M.findWithDefault v v m) tailVar)

renameConstraint :: Map Variable Variable -> Constraint -> Constraint
renameConstraint m = \case
  Merge k a b c -> Merge k (renameRow m a) (renameRow m b) (renameRow m c)
  Lacks l r -> Lacks l (renameRow m r)

prettyType :: Type -> String
prettyType t = prettyTypeWith (namesFor (S.toAscList (freeType t))) t

prettyScheme :: Scheme -> String
prettyScheme (Scheme vs cs t) =
  let names = namesFor (S.toAscList (freeType t `S.union` S.unions (map freeConstraint cs)))
      quant = if null vs then "" else "forall " ++ unwords (map (variableName names) vs) ++ ". "
      context = if null cs then "" else intercalate ", " (map (prettyConstraint names) cs) ++ " => "
  in quant ++ context ++ prettyTypeWith names t

namesFor :: [Variable] -> Map Variable String
namesFor vs = M.fromList (zip vs (map name [0 :: Int ..]))
  where name i = '\'' : [toEnum (fromEnum 'a' + i `mod` 26)] ++ if i < 26 then "" else show (i `div` 26)

variableName :: Map Variable String -> Variable -> String
variableName ns v = M.findWithDefault ("'t" ++ show v) v ns

prettyTypeWith :: Map Variable String -> Type -> String
prettyTypeWith ns = go
  where
    go = \case
      TInt -> "int"
      TV v -> variableName ns v
      TRecord r -> "(" ++ prettyRow ns ", " r ++ ")"
      TVariant (Row fs Nothing) | M.null fs -> "void"
      TVariant r -> "(" ++ prettyRow ns " | " r ++ ")"
      TFun a b -> argument a ++ " -> " ++ go b
      TNamed n [] -> n
      TNamed n ts -> n ++ " " ++ unwords (map argument ts)
      TRec v body ->
        let binder = "'rec" ++ show v
        in "mu " ++ binder ++ ". " ++ prettyTypeWith (M.insert v binder ns) body
    argument = \case
      x@(TFun _ _) -> "(" ++ go x ++ ")"
      x@(TNamed _ (_:_)) -> "(" ++ go x ++ ")"
      x -> go x

prettyRow :: Map Variable String -> String -> Row -> String
prettyRow ns sep (Row fs rest) = intercalate sep $
  [l ++ ": " ++ prettyTypeWith ns t | (l,t) <- M.toAscList fs] ++ maybe [] (\v -> [variableName ns v]) rest

prettyConstraint :: Map Variable String -> Constraint -> String
prettyConstraint ns = \case
  Merge k a b c ->
    (if k == Disjoint then "merge" else "combine") ++ "(" ++ intercalate "; " (map (prettyRow ns ", ") [a,b,c]) ++ ")"
  Lacks l r -> l ++ " absent from (" ++ prettyRow ns ", " r ++ ")"
