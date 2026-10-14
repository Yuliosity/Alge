module Main (main) where

import Alge
import Alge.Eval
import Alge.Infer
import Alge.Parser
import Alge.Syntax
import Alge.Type
import Data.Either (isLeft)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as M
import GHC.Stack (HasCallStack)
import Test.Hspec
  ( Expectation, Spec, describe, expectationFailure, hspec, it
  , shouldBe, shouldContain, shouldSatisfy
  )

parseOK :: String -> Either String Program
parseOK = parseProgram "test.alge"

expectRight :: (HasCallStack, Show e) => Either e a -> IO a
expectRight (Right value) = pure value
expectRight (Left err) = expectationFailure (show err) >> fail "expected Right"

run :: String -> String -> Either String String
run source expression = do
  loaded <- loadProgram "test.alge" source
  (_,value) <- runExpression loaded expression
  pure (prettyValue value)

valueIs :: HasCallStack => String -> String -> String -> Expectation
valueIs source expression expected = run source expression `shouldBe` Right expected

rejects :: HasCallStack => String -> String -> Expectation
rejects source fragment = case loadProgram "test.alge" source of
  Left message -> message `shouldContain` fragment
  Right _ -> expectationFailure "expected rejection, but program succeeded"

lists :: String
lists = unlines
  [ "type list 'a = None | cons: (head: 'a, tail: list 'a)"
  , "map: (f: 'a -> 'b, list: list 'a) -> list 'b"
  , "map (f: 'a -> 'b, list: list 'a) = match list with"
  , "  | None -> None"
  , "  | cons = xs -> cons = (head = f xs.head, tail = map (f = f, list = xs.tail))"
  , "apply x f = fun y -> f (x, y)"
  , "incAll = apply (f = fun x -> x + 1) map"
  , "xs: list int = cons = (head = 1, tail = cons = (head = 2, tail = None))"
  ]
 
named :: String
named = unlines
  [ "apply x f = fun y -> f (x, y)"
  , "add (n: int, m: int) = n + m"
  , "addTwo = apply (n = 2) add"
  ]

spec :: Spec
spec = do
  describe "Parsing" $ do
    it "parse integer" $ parseExpression "42" `shouldBe` Right (EInt 42)
    it "parse unit" $ parseExpression "()" `shouldBe` Right EUnit
    it "parse product fields" $ parseExpression "(x = 1, y = 2)" `shouldBe` Right (EProduct [EField "x" (EInt 1), EField "y" (EInt 2)])
    it "parse precedence" $ parseExpression "1 + 2 * 3" `shouldBe` Right (EBinary "+" (EInt 1) (EBinary "*" (EInt 2) (EInt 3)))
    it "parse right associative arrows" $ parseType "int -> int -> int" `shouldBe` Right (SArrow SInt (SArrow SInt SInt))
    it "parse capitalized tag" $ parseExpression "None" `shouldBe` Right (EField "none" EUnit)
    it "parse all declaration forms" $ do
      Program ds <- expectRight (parseOK "type number = int\nsquare: number -> number\nsquare x = x * x\none: number = 1\n")
      length ds `shouldBe` 4
    it "parse line layout" $ do
      p <- expectRight (parseOK "point =\n  x = 1\n  y = 2\nanswer = point.x\n")
      q <- expectRight (parseOK "point = (x = 1, y = 2)\nanswer = point.x\n")
      p `shouldBe` q
    it "parse type layout" $ do
      p <- expectRight (parseOK "type point =\n  x: int\n  y: int\n")
      q <- expectRight (parseOK "type point = x: int, y: int\n")
      p `shouldBe` q
    it "parse comments" $ do
      Program ds <- expectRight (parseOK "(* outer (* nested *) *)\nx = 1 // line\ny = 2 /* block */\n")
      length ds `shouldBe` 2
    it "parse malformed input" $ parseOK "x = (y = 1" `shouldSatisfy` isLeft
  describe "Evaluation and functions" $ do
    it "arithmetic" $ valueIs "" "(8 - 2) * 3 / 2" "9"
    it "negative integer" $ valueIs "" "-3 * 2" "-6"
    it "function declaration" $ valueIs "square x = x * x\n" "square 7" "49"
    it "lambda and currying" $ valueIs "add x y = x + y\n" "add 3 4" "7"
    it "polymorphic identity" $ valueIs "id x = x\na = id 1\nb = id (x = 2)\n" "b.x + a" "3"
    it "polymorphic signature identity" $ valueIs "id: 'a -> 'a\nid x = x\n" "id (x = 2)" "(x = 2)"
    it "over-general polymorphic signature rejected" $ rejects "id: 'a -> 'a\nid x = x + 1\n" "more general"
    it "inline polymorphic signature checked" $ rejects "id: 'a -> 'a = fun x -> x + 1\n" "more general"
    it "independent signature variables remain independent" $ rejects "f: 'a -> 'b -> 'a\nf x y = if 1 == 1 then x else y\n" "independent signature"
    it "open-row signature cannot require unlisted fields" $ rejects "type item = x: int\nf: (>item) -> int\nf v = v.y\n" "more general"
    it "lexical closure" $ valueIs "make x = fun y -> x + y\na = make 10\n" "a 5" "15"
    it "projection" $ valueIs "" "(y = 2, x = 1).x" "1"
    it "recursive integer function" $ valueIs "factorial n = if n == 0 then 1 else n * factorial (n - 1)\n" "factorial 6" "720"
    it "integer patterns" $ valueIs "f n = match n with | 0 -> 9 | _ -> n + 1\n" "f 0 + f 2" "12"
    it "negative integer pattern" $ valueIs "f n = match n with | -1 -> 9 | _ -> 0\n" "f (-1)" "9"
  describe "Type synonyms and product composition" $ do
    it "type synonym" $ valueIs "type number = int\nx: number = 4\n" "x + 1" "5"
    it "parameterized synonym" $ valueIs "type pair 'a 'b = fst: 'a, snd: 'b\nx: pair int int = (fst = 2, snd = 3)\n" "x.fst + x.snd" "5"
    it "type composition flattens shared fields" $ valueIs (unlines
      ["type colored = label: int, color: int", "type shaped = label: int, shape: int", "type both = colored, shaped",
       "x: both = (label = 1, color = 2, shape = 3)"]) "x.shape" "3"
    it "duplicate type labels with incompatible payloads" $ rejects "type bad = x: int, x: ()\n" "type mismatch"
    it "duplicate value labels" $ rejects "x = (a = 1, a = 1)\n" "duplicate label"
    it "duplicate labels through variables" $ rejects "a = x = 1\nb = x = 2\nc = a, b\n" "duplicate label"
    it "duplicate labels in patterns" $ rejects "f (x = a, x = b) = a\n" "duplicate label"
    it "duplicate pattern bindings" $ rejects "f (x = a, y = a) = a\n" "duplicate variable"
    it "unit product identity" $ valueIs "" "((), x = 4, (), y = 5, ()).x" "4"
    it "unit payload is a real field" $ valueIs "x = (a = (), b = 1)\n" "x.a" "()"
    it "duplicate unit-valued fields rejected" $ rejects "x = (a = (), a = ())\n" "duplicate label"
    it "unit-only composition" $ valueIs "" "(), (), ()" "()"
    it "primitive composition rejected" $ rejects "x = 1, 2\n" "only products"
    it "primitive type composition rejected" $ rejects "type bad = int, int\n" "only products"
  describe "Records and row polymorphism" $ do
    it "closed function rejects extras" $ rejects "f (x = x) = x + 1\ny = f (x = 1, extra = 2)\n" "fields do not match"
    it "closed annotation rejects extras" $ rejects "x: (a: int) = (a = 1, b = 2)\n" "fields do not match"
    it "missing named argument" $ rejects "f (x: int, y: int) = x + y\na = f (x = 1)\n" "fields do not match"
    it "open pattern ignores extras" $ valueIs "f (x = x, _) = x + 1\n" "f (x = 4, extra = 9)" "5"
    it "open pattern binds remainder" $ valueIs "f (x = x, rest) = rest.y + x\n" "f (x = 4, y = 5)" "9"
    it "open type sugar" $ valueIs "type item = x: int\nf: (>item) -> int\nf v = v.x\n" "f (x = 4, y = 5)" "4"
    it "explicit row variable preserves extras" $ valueIs "keep: (x: int, 'r) -> (x: int, 'r)\nkeep v = v\n"
      "(keep (x = 1, y = 2)).y" "2"
    it "explicit anonymous row" $ valueIs "f (v: (x: int, _)) = v.x\n" "f (x = 3, y = 4)" "3"
    it "record order irrelevant" $ valueIs "f (x: int, y: int) = x - y\n" "f (y = 2, x = 7)" "5"
  describe "Named partial application" $ do
    it "apply partial named arguments" $ valueIs named "addTwo (m = 5)" "7"
    it "annotated apply" $ valueIs (unlines
      ["apply (x: 'a) (f: ('a, 'b) -> 'c): ('b -> 'c) = fun y -> f (x, y)",
       "add (n: int, m: int) = n + m"]) "apply (n = 2) add (m = 3)" "5"
    it "apply inferred residual is exact" $ rejects (named ++ "bad = addTwo (m = 1, extra = 2)\n") "fields do not match"
    it "apply rejects replacing supplied argument" $ rejects (named ++ "bad = addTwo (n = 3, m = 1)\n") "fields do not match"
    it "apply rejects unknown supplied argument" $ rejects (named ++ "bad = apply (unknown = 3) add\n") "provided fields"
    it "apply empty fragment" $ valueIs named "apply () add (n = 3, m = 4)" "7"
    it "apply complete fragment" $ valueIs named "apply (n = 3, m = 4) add ()" "7"
    it "apply must compose records" $ rejects (named ++ "bad = apply 1 add\n") "type mismatch"
  describe "Recursive lists" $ do
    it "map empty list" $ valueIs lists "map (f = fun x -> x + 1, list = None)" "(none = ())"
    it "map two elements" $ valueIs lists "map (f = fun x -> x * 2, list = xs)" "(cons = (head = 2, tail = (cons = (head = 4, tail = (none = ())))))"
    it "map infers recursive result without signature" $ valueIs
      (unlines (filter (not . isInfixOf "map:") (lines lists)))
      "incAll (list = xs)" "(cons = (head = 2, tail = (cons = (head = 3, tail = (none = ())))))"
    it "fully inferred recursive map" $ valueIs (unlines
      ["map f list = match list with", "  | None -> None",
       "  | cons = xs -> cons = (head = f xs.head, tail = map f xs.tail)"])
      "map (fun x -> x + 1) (cons = (head = 4, tail = None))"
      "(cons = (head = 5, tail = (none = ())))"
    it "nested layout in map" $ valueIs (unlines
      ["map f list = match list with", "  | None -> None", "  | cons = xs ->",
       "    cons =", "      head = f xs.head", "      tail = map f xs.tail"])
      "map (fun x -> x + 1) (cons = (head = 4, tail = None))"
      "(cons = (head = 5, tail = (none = ())))"
    it "incAll" $ valueIs lists "incAll (list = xs)" "(cons = (head = 2, tail = (cons = (head = 3, tail = (none = ())))))"
    it "map changes element type" $ valueIs lists "map (f = fun x -> value = x, list = xs)" "(cons = (head = (value = 1), tail = (cons = (head = (value = 2), tail = (none = ())))))"
    it "inferred incAll type" $ do
      loaded <- expectRight (loadProgram "test.alge" lists)
      scheme <- expectRight (maybe (Left "missing incAll") Right (M.lookup "incAll" (inferredTypes (loadedInference loaded))))
      prettyScheme scheme `shouldBe` "(list: list int) -> list int"
  describe "Recursive aliases and variants" $ do
    it "structurally equal recursive aliases" $ valueIs (unlines
      ["type first = End | next: first", "type second = End | next: second",
       "id: first -> second", "id x = x", "x: first = next = End"]) "id x" "(next = (end = ()))"
    it "unguarded recursive alias" $ rejects "type bad = bad\n" "unguarded"
    it "unknown unused type rejected" $ rejects "type bad = missing\n" "unknown type"
    it "wrong alias arity" $ rejects "type box 'a = value: 'a\nx: box = value = 1\n" "type arguments"
    it "non-exhaustive variant match" $ rejects "type choice = A | B\nf: choice -> int\nf x = match x with | A -> 1\n" "non-exhaustive"
    it "refutable payload does not cover a tag" $ rejects "type choice = some: int | None\nf: choice -> int\nf x = match x with | some = 0 -> 1 | None -> 2\n" "non-exhaustive"
    it "several cases for the same tag" $ valueIs
      "type choice = some: int | None\nf: choice -> int\nf x = match x with | some = 0 -> 10 | some = n -> n | None -> 20\n"
      "f (some = 0) + f (some = 3)" "13"
    it "non-regular recursive alias rejected" $ rejects "type nest 'a = next: nest (x: 'a)\n" "non-regular"
    it "inferred sum result" $ valueIs "choose n = if n == 0 then A else B\n" "choose 0" "(a = ())"
    it "void sum identity" $ valueIs "type choice = void | A | void\nx: choice = A\n" "x" "(a = ())"
    it "sum duplicate alternatives flatten" $ valueIs "type choice = A | A\nx: choice = A\n" "x" "(a = ())"
    it "sum duplicate incompatible alternatives rejected" $ rejects "type choice = x: int | x: ()\n" "type mismatch"
  describe "Errors and evaluation limits" $ do
    it "division by zero" $ rejects "x = 1 / 0\n" "division by zero"
    it "occurs check" $ rejects "f x = x x\n" "infinite inferred type"
    it "signature without definition" $ rejects "f: int -> int\n" "without definition"
    it "recursive strict value rejected" $ rejects "x = field = x\n" "recursive value"
    it "duplicate declarations" $ rejects "x = 1\nx = 2\n" "duplicate value"
    it "evaluation budget" $ do
      p <- expectRight (parseOK "loop x = loop x\n")
      env <- expectRight (evalProgram p)
      e <- expectRight (parseExpression "loop ()")
      case evalExpressionWithFuel 100 env e of
        Left (RuntimeError msg) -> msg `shouldContain` "step limit"
        Right _ -> expectationFailure "infinite loop was not stopped"

main :: IO ()
main = hspec spec
