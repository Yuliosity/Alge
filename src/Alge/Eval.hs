{-# LANGUAGE LambdaCase #-}

module Alge.Eval
  ( Value(..), ValueEnv, RuntimeError(..), evalProgram, evalExpression
  , evalProgramWithFuel, evalExpressionWithFuel, prettyValue
  ) where

import Alge.Syntax
import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

data Value = VInt Integer | VRecord (Map Name Value) | VClosure Pattern Expr ValueEnv
type ValueEnv = Map Name Value
newtype RuntimeError = RuntimeError String deriving (Eq, Show)
type Eval = StateT Int (Either RuntimeError)

instance Show Value where show = prettyValue

prettyValue :: Value -> String
prettyValue = \case
  VInt n -> show n
  VRecord fields
    | M.null fields -> "()"
    | otherwise -> "(" ++ intercalate ", " [n ++ " = " ++ prettyValue v | (n,v) <- M.toAscList fields] ++ ")"
  VClosure {} -> "<function>"

failure :: String -> Eval a
failure = lift . Left . RuntimeError

tick :: Eval ()
tick = do
  remaining <- get
  when (remaining <= 0) $ failure "evaluation step limit exceeded"
  put (remaining - 1)

unit :: Value
unit = VRecord M.empty

boolean :: Bool -> Value
boolean b = VRecord (M.singleton (if b then "true" else "false") unit)

integer :: Value -> Eval Integer
integer = \case
  VInt n -> pure n
  _ -> failure "expected an integer"

record :: Value -> Eval (Map Name Value)
record = \case
  VRecord fs -> pure fs
  _ -> failure "expected a record"

evaluate :: ValueEnv -> Expr -> Eval Value
evaluate env expr = do
  tick
  case expr of
    EInt n -> pure (VInt n)
    EUnit -> pure unit
    EVar n -> maybe (failure ("unbound value '" ++ n ++ "'")) pure (M.lookup n env)
    EField n e -> VRecord . M.singleton n <$> evaluate env e
    EProduct es -> do
      fields <- foldM (\acc e -> do
        next <- evaluate env e >>= record
        unless (M.null (M.intersection acc next)) $ failure "duplicate label in value composition"
        pure (M.union acc next)) M.empty es
      pure (VRecord fields)
    EProject e n -> do
      fs <- evaluate env e >>= record
      maybe (failure ("missing field '" ++ n ++ "'")) pure (M.lookup n fs)
    ELambda p e -> pure (VClosure p e env)
    EApply f x -> do
      function <- evaluate env f
      argument <- evaluate env x
      case function of
        VClosure p body captured -> case matchPattern p argument of
          Nothing -> failure "function argument did not match its pattern"
          Just bindings -> evaluate (M.union bindings captured) body
        _ -> failure "attempted to call a non-function"
    EAnn e _ -> evaluate env e
    EBinary op a b -> do
      x <- evaluate env a >>= integer
      y <- evaluate env b >>= integer
      case op of
        "+" -> pure (VInt (x+y))
        "-" -> pure (VInt (x-y))
        "*" -> pure (VInt (x*y))
        "/" -> if y == 0 then failure "division by zero" else pure (VInt (x `quot` y))
        "==" -> pure (boolean (x == y))
        "!=" -> pure (boolean (x /= y))
        "<" -> pure (boolean (x < y))
        ">" -> pure (boolean (x > y))
        "<=" -> pure (boolean (x <= y))
        ">=" -> pure (boolean (x >= y))
        _ -> failure ("unknown operator '" ++ op ++ "'")
    EIf c yes no -> do
      value <- evaluate env c
      case value of
        VRecord fs | M.keys fs == ["true"] -> evaluate env yes
        VRecord fs | M.keys fs == ["false"] -> evaluate env no
        _ -> failure "expected True or False"
    EMatch subject cases -> do
      value <- evaluate env subject
      let choose [] = failure "non-exhaustive match at runtime"
          choose ((p,e):rest) = case matchPattern p value of
            Nothing -> choose rest
            Just bindings -> evaluate (M.union bindings env) e
      choose cases

matchPattern :: Pattern -> Value -> Maybe ValueEnv
matchPattern p value = case p of
  PVar n -> Just (M.singleton n value)
  PWildcard -> Just M.empty
  PInt n -> case value of VInt m | n == m -> Just M.empty; _ -> Nothing
  PUnit -> case value of VRecord fs | M.null fs -> Just M.empty; _ -> Nothing
  PAnn inner _ -> matchPattern inner value
  PField n inner -> case value of
    VRecord fs | M.size fs == 1 -> M.lookup n fs >>= matchPattern inner
    _ -> Nothing
  PProduct ps -> do
    fs <- case value of VRecord fields -> Just fields; _ -> Nothing
    let flattened = concatMap flatten ps
        fields = [(n,inner) | PField n inner <- flattened]
        remainders = [inner | inner <- flattened, not (isField inner), inner /= PUnit]
    bindings <- mapM (\(n,inner) -> M.lookup n fs >>= matchPattern inner) fields
    let leftover = foldr (M.delete . fst) fs fields
    residual <- case remainders of
      [] -> if M.null leftover then Just M.empty else Nothing
      [inner] -> matchPattern inner (VRecord leftover)
      _ -> Nothing
    foldM merge M.empty (bindings ++ [residual])
  where
    flatten = \case
      PProduct xs -> concatMap flatten xs
      inner -> [inner]
    isField = \case
      PField _ _ -> True
      _ -> False
    merge a b | M.null (M.intersection a b) = Just (M.union a b)
              | otherwise = Nothing

evalProgram :: Program -> Either RuntimeError ValueEnv
evalProgram = evalProgramWithFuel 1000000

evalProgramWithFuel :: Int -> Program -> Either RuntimeError ValueEnv
evalProgramWithFuel fuel (Program declarations) = evalStateT (foldM define M.empty declarations) fuel
  where
    define env (DValue n args _ body) = do
      let expression = lambdaArgs args body
      case expression of
        ELambda p rhs ->
          let recursiveEnv = M.insert n closure env
              closure = VClosure p rhs recursiveEnv
          in pure recursiveEnv
        EAnn (ELambda p rhs) _ ->
          let recursiveEnv = M.insert n closure env
              closure = VClosure p rhs recursiveEnv
          in pure recursiveEnv
        _ -> do
          value <- evaluate env expression
          pure (M.insert n value env)
    define env _ = pure env

evalExpression :: ValueEnv -> Expr -> Either RuntimeError Value
evalExpression = evalExpressionWithFuel 1000000

evalExpressionWithFuel :: Int -> ValueEnv -> Expr -> Either RuntimeError Value
evalExpressionWithFuel fuel env expression = evalStateT (evaluate env expression) fuel
