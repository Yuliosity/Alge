module Alge (Loaded(..), loadProgram, runExpression) where

import Alge.Syntax
import Alge.Parser
import Alge.Type
import Alge.Infer
import Alge.Eval

data Loaded = Loaded
  { loadedProgram :: Program
  , loadedInference :: Inference
  , loadedValues :: ValueEnv
  }

loadProgram :: FilePath -> String -> Either String Loaded
loadProgram file source = do
  program <- parseProgram file source
  context <- either (Left . typeMessage) Right (inferProgram program)
  values <- either (Left . runtimeMessage) Right (evalProgram program)
  pure (Loaded program context values)
  where
    typeMessage (TypeError message) = "Type error: " ++ message
    runtimeMessage (RuntimeError message) = "Runtime error: " ++ message

runExpression :: Loaded -> String -> Either String (Scheme,Value)
runExpression loaded source = do
  expression <- parseExpression source
  scheme <- either (Left . typeMessage) Right (inferExpression (loadedInference loaded) expression)
  value <- either (Left . runtimeMessage) Right (evalExpression (loadedValues loaded) expression)
  pure (scheme,value)
  where
    typeMessage (TypeError message) = "Type error: " ++ message
    runtimeMessage (RuntimeError message) = "Runtime error: " ++ message
