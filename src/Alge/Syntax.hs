module Alge.Syntax where

type Name = String

data SType
  = SInt | SVoid | SUnit | SVar Name | SName Name [SType]
  | SField Name SType | SProduct [SType] | SSum [SType]
  | SArrow SType SType | SOpen SType
  deriving (Eq, Show)

data Pattern
  = PVar Name | PWildcard | PInt Integer | PUnit
  | PField Name Pattern | PProduct [Pattern] | PAnn Pattern SType
  deriving (Eq, Show)

data Expr
  = EInt Integer | EUnit | EVar Name
  | EField Name Expr | EProduct [Expr] | EProject Expr Name
  | ELambda Pattern Expr | EApply Expr Expr
  | EIf Expr Expr Expr | EMatch Expr [(Pattern, Expr)]
  | EBinary Name Expr Expr | EAnn Expr SType
  deriving (Eq, Show)

data Decl
  = DType Name [Name] SType
  | DSignature Name SType
  | DValue Name [Pattern] (Maybe SType) Expr
  deriving (Eq, Show)

newtype Program = Program [Decl] deriving (Eq, Show)

tagName :: Name -> Name
tagName [] = []
tagName (c:cs) = toLowerAscii c : cs
  where toLowerAscii x | x >= 'A' && x <= 'Z' = toEnum (fromEnum x + 32)
                       | otherwise = x

lambdaArgs :: [Pattern] -> Expr -> Expr
lambdaArgs args body = foldr ELambda body args
