module Main (main) where

import Alge
import Alge.Eval
import Alge.Infer
import Alge.Type
import qualified Data.Map.Strict as M
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (hSetEncoding, stdout, stderr, utf8)
import qualified System.IO as IO
import Control.Exception (IOException, try)

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  args <- getArgs
  case args of
    [] -> usage
    ["--help"] -> usage
    file:options -> do
      sourceResult <- try (IO.withFile file IO.ReadMode (\handle -> hSetEncoding handle utf8 >> IO.hGetContents' handle)) :: IO (Either IOException String)
      source <- either (die . show) pure sourceResult
      loaded <- either die pure (loadProgram file source)
      runOptions loaded options
  where
    usage = putStrLn "Usage: alge FILE [--types] [--expr EXPRESSION]\nWithout options, print all declared values."
    runOptions loaded [] = mapM_ (\(n,v) -> putStrLn (n ++ " = " ++ prettyValue v)) (M.toAscList (loadedValues loaded))
    runOptions loaded ("--types":rest) = do
      mapM_ (\(n,t) -> putStrLn (n ++ ": " ++ prettyScheme t)) (M.toAscList (inferredTypes (loadedInference loaded)))
      unlessEmpty rest (runOptions loaded rest)
    runOptions loaded ("--expr":expression:rest) = do
      (scheme,value) <- either die pure (runExpression loaded expression)
      putStrLn (prettyValue value ++ " : " ++ prettyScheme scheme)
      unlessEmpty rest (runOptions loaded rest)
    runOptions _ _ = die "Unknown options. Use --help."
    unlessEmpty [] _ = pure ()
    unlessEmpty _ action = action
