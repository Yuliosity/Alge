# Alge: reference interpreter

Alge is an experimental, statically typed, expression-oriented programming
language built around labeled values, called **atoms**. Products of atoms form
records; sums of atoms form variants. Named arguments are records too, so the
same composition rules support both building data and partially applying
functions.

The goal is to make reusable functions over structured data easy to express,
while catching mistakes in record shapes and argument names before evaluation.
This reference interpreter is a testbed for exploring that design.

Key features:

* **Uniform structural types:** both records and variants are made from the
  same building blocks and are open for combining and extension.
* **Exact records by default:** unexpected fields are errors; open records and
  row polymorphism explicitly allow additional fields.
* **Functional core:** first-class functions, pattern matching, recursive data,
  and inference of polymorphic types.

A Haskell implementation with a Megaparsec parser, strict evaluation, and type
inference. Tested with GHC 9.12.2. Requires GHC and Cabal; dependencies are listed
in `alge.cabal`.

## Running

```shell
cabal build all
cabal test --test-show-details=direct
cabal run alge -- examples/lists.alge --types
cabal run alge -- examples/lists.alge --expr "result"
cabal run alge -- examples/lists.alge --expr "incAll (list = xs)"
cabal run alge -- examples/records.alge --types --expr "answer"
```

With no options, the interpreter prints declared values; functions appear as
`<function>`. `--types` prints polymorphic schemes, including any unresolved
row-composition constraints. `--expr` checks and evaluates an expression in the
file's environment. The entire file is type-checked before evaluation. The CLI
reads source files as UTF-8.

## Supported core

* `int` is the only primitive type; integers have arbitrary precision.
* `()`, `void`, labeled atoms, exact records, and structural variants.
* Transparent, parameterized, and guarded recursive type synonyms.
* Value declarations, curried functions, `fun`, and recursive functions.
* Separate signatures and annotations for values, arguments, and expressions.
* Projections, `match`, `if`, arithmetic, and comparisons.
* Type and row polymorphism, including partial application of named arguments.
* Open records using `>T`, `(x: int, 'r)`, and `(x: int, _)`.
* `//`, `/* ... */`, and nested `(* ... *)` comments.
* Products written as aligned lines on the right-hand side of `=` or `->`,
  including type synonym definitions.

```ocaml
type point = x: int, y: int

square n = n * n
id x = x

p: point =
  x = 3
  y = 4
(* same as p = (x = 3, y = 4) *)

normSquared (x: int, y: int) = x * x + y * y
answer = normSquared p
```

Write top-level declarations in the first column; `;` is also available as a
separator. Parentheses allow line breaks, but components must be separated by
commas. Function application binds more tightly than arithmetic; projection
binds more tightly than application. `/` truncates division toward zero;
division by zero is a runtime error.

Capitalized types and values (like `None`) are shortcuts for atoms with unit
payload (`none = ()` in expressions and `none: ()` in types). `True` and
`False` are these as well, rather than an additional primitive type.
Comparisons return their structural sum.

## Named arguments and rows

```ocaml
apply x f = fun y -> f (x, y)

add (n: int, m: int) = n + m
addTwo = apply (n = 2) add
answer = addTwo (m = 5)
```

`addTwo` has the exact type `(m: int) -> int`. Extra fields, a missing `m`, or
supplying `n` again are rejected before evaluation. Supplying every argument
returns a function from unit: `apply (n = 2, m = 5) add ()`.

Record type composition collapses shared compatible fields. Value composition
requires disjoint labels, even when the two field values are equal or both are
`()`. A standalone unit component is the identity; `field = ()` is a real field
and is preserved.

```ocaml
type colored = label: int, color: int
type shaped = label: int, shape: int
type both = colored, shaped

readColor: (>colored) -> int
readColor value = value.color

keep: (label: int, 'r) -> (label: int, 'r)
keep value = value
```

`readColor` accepts additional fields. In `keep`, the same row remainder links
the argument and result. An anonymous `_` in a type creates a fresh variable,
which is generalized by the usual top-level rules.

## Patterns

* `(x = a, y = b)` destructures an exact record.
* `(x = a, _)` ignores additional fields.
* `(x = a, rest)` binds the remaining record to `rest`.
* `(x, y)` and `(x: int, y: int)` are field-pattern puns when **all** components
  are names or annotated names.
* `(x: int)` is a single annotated argument, not a record with a field named `x`.
* `(x = a)` is an exact singleton record.

Expression punning is not implemented yet: write `f = f` explicitly.
In an expression, `(x, y)` composes the values of the two variables; interpreting
it as field punning would silently change the meaning of `apply`.

## Recursive data

The complete example is in `examples/lists.alge`:

```ocaml
type list 'a = None | cons: (head: 'a, tail: list 'a)

map: (f: 'a -> 'b, list: list 'a) -> list 'b
map (f: 'a -> 'b, list: list 'a) = match list with
  | None -> None
  | cons = xs ->
    cons =
      head = f xs.head
      tail = map (f = f, list = xs.tail)

incAll = apply (f = fun x -> x + 1) map
```

The signature of `map` is optional. Without it, inference produces a structural
recursive type printed using `mu`; it does not automatically choose a synonym
name. Tests also cover a fully unannotated, curried `map f list`.

Recursive types are compared by unfolding and coinductively tracking visited
pairs. Inference can produce guarded recursive data equations; the occurs check
rejects a type equation arising from `x x`. Recursive value definitions must be
functions because evaluation is strict.

## Type inference

The implementation uses Hindley–Milner inference with top-level generalization
and row constraints. Annotations, lambdas, and expected branch types are handled
bidirectionally; this is not a complete bidirectional system for arbitrary
higher-rank types.

Composing values creates a `merge(left, right, result)` constraint. If the fields
are not yet known, the constraint is retained in the function's polymorphic
scheme. At an `apply` call, the function's known full argument record and the
supplied fragment determine the exact remainder. Label-absence constraints
survive generalization and receive fresh variables whenever a scheme is
instantiated.

Record shape checking is exact, including records inside payloads. An atom may
be used as a value of an expected sum. Duplicate fields in type descriptions are
checked by unification; in a polymorphic description, this can equate type
variables rather than prove equality of independently quantified types.
Variables in a separate signature are universal: an implementation cannot
silently specialize `'a -> 'a` to `int -> int`.

## Current limitations

* Modules, mutation, local `let`, and mutually recursive functions are not
  implemented. Values and functions can refer to earlier declarations, and a
  function can refer to itself. Type synonyms are available regardless of their
  declaration order.
* Multi-field products cannot be mixed with sums at the same level.
  Distributivity, general intersections, and type subtraction are not supported.
* Polymorphic recursion inference, higher-rank types, and dependent types are
  not supported.
* Synonyms with unresolved composition of abstract products are rejected.
  Ordinary payload parameters and simple row remainders are supported.
* Parameterized recursive synonyms are restricted to regular forms: recursive
  arguments must be type parameters rather than growing type expressions.
* `match` exhaustiveness checking is conservative: every alternative needs a
  pattern that covers its entire payload, or a global catch-all. Multiple cases
  for the same alternative, including specific payload values, are allowed.
* Type errors are plain text without source spans. Parser errors include the
  filename, line, and column.
* The public evaluation API defaults to a limit of one million steps.
  `evalProgramWithFuel` and `evalExpressionWithFuel` allow a different limit.

## Project structure

* `Alge.Syntax`: source AST.
* `Alge.Parser`: Megaparsec parser and indentation rules.
* `Alge.Type`: types, rows, schemes, constraints, and pretty-printing.
* `Alge.Infer`: unification, inference, checking, and constraint solving.
* `Alge.Eval`: strict interpreter with lexical closures.
* `Alge`: loading a checked program and evaluating expressions.
* `test/Main.hs`: Hspec specifications for parsing, types, evaluation, and errors.

## Tests

The suite uses Hspec's `describe` and `it` to organize 83 examples by subsystem,
with standard expectations for successful results and expected failures.
Run the entire suite with:

```powershell
cabal test --test-show-details=direct
```

To run only a matching group or example, pass Hspec's `--match` option:

```powershell
cabal test --test-show-details=direct --test-option=--match --test-option="Named partial application"
```

Hspec reports individual failures and exits with a nonzero status if any example
fails.
