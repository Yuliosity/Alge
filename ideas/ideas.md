# Alge

- Very structural type system: everything — records, variants, modules, named parameters, row polymorphism — is built from the same basic blocks

## Basic syntax
- Comments: `(* *)` here just to reuse OCaml highlighting, probably mainstream `//` and `/* */` in real life
- Expression-based
- Layout rules to avoid excessive `,`:
  ```ocaml
  foo = a, b, c
  ```
  ≡
  ```
  foo =
    a
    b
    c
  ```

## Declarations

- `type x = <...>` for types
- `x: ty = <...>` or `x = <...>` for values

## Types

### Primitives
- `void`, `int`, `float`, `string` are types

### Atoms
- Atom is a WIP name for labeled values
- `label: ty` is a type
- `label = expr` where `expr: ty` is a value of type `label: ty`
- `Label` is sugar for `label: ()` (in type context) or `label = ()` (in value context)
  - Capitalized to distinguish with variable names
  - Another variant: `#label`
- Project: `(label = val).label` ≡ `val`

### Products (intersections?)
- `()` (unit) is a nullary product
- Atom is an unary product
- Type-level `,` combines two product types: 
  - `product1, product2` is a product
  - Identity: `(), ty` ≡ `ty, ()` ≡ `ty`
  - Commutativity: `ty1, ty2` ≡ `ty2, ty1`
  - (**ARGUABLE**) `label: ty1, label: ty2` flattens to `label: ty1` if `ty1` ≡ `ty2`, type mismatch otherwise
  - Associativity: `label1: ty1, (label2: ty2, ty3)` ≡ `(label1: ty1, label2: ty2), ty3`
- Value-level `,` combines two product values:
  - Identity: `(), val` ≡ `val, ()` ≡ `val`
  - Commutativity: `val1, val2` ≡ `val2, val1`
  - `(label = val1, label = val2)` doesn't flatten and produces an error, because it would require a provenance of value equality which is harder than for types
  - Associativity: `label1 = val1, (label2 = val2, val3)` ≡ `(label1 = val1, label2 = val2), val3`
- Project: `(label = val1, val2).label` still ≡ `val1`

### Sums (unions?)
- void type is a nullary sum
- Atom is an unary sum
- Type-level `|` combines two sum types:
  - `sum1 | sum2` is a sum
  - Identity: `void | ty` ≡ `ty | void` ≡ `ty`
  - Commutativity: `ty1 | ty2` ≡ `ty2 | ty1`
  - `label: ty1 | label: ty2` flattens to `label: ty1` if `ty1` ≡ `ty2`, type mismatch otherwise
  -  Associativity: `label1: ty1 | (label2: ty2 | ty3)` ≡ `(label1: ty1 | label2: ty2) | ty3`
- Value-level `|` isn't

### Parameteric polymorphism

- `'a` etc is a type variable
- `type t 'a = <...>`

### More structurality

Can we allow mixing `|` and `,` on the same level? It will bring a lot of new questions:
- Can `a, (b | c)` be ≡ `(a, b) | (a, c)`?
- How to deal with recursive types? E.g., `type list = None | (hd: int, tl: list)`

### Examples

```ocaml
type bool = True | False
type pair 'a 'b = fst: 'a, snd: 'b
type option 'a = none: () | some: 'a
type result 'a 'b = err: 'a | ok: 'b
type list 'a = None | cons: (head: 'a, tail: list 'a)
```

## Functions

Variants of syntax (will choose later)

```ocaml
square: int -> int =
  fun x -> x * x
```

```ocaml
square: int -> int
square x = x * x
```

## Patterns

- Primitive literals (`1`, `"lawl"`) are patterns, matching with corresponding values
- `label = pattern` is a pattern, matches with `label = val` if `pattern` matches `val`
  - Need a shortcut for `label = label` to bind a var to a label's name
- `label = pattern1, pattern2` is a pattern, matches with `label = val1, val2` if `pattern1` matches `val1` and `pattern2` matches `val2`
  - `pattern2` must not contain `label`
- `var` is a pattern, binding value to `var`
- `_` is the wildcard non-binding pattern

## Examples

```ocaml
concat = fun xs -> match xs with
  | None = _ -> ""
  | cons = (head = h, tail = t) -> h <> concat t (* <> appends strings *)
  (*
  Label puns:
  cons = (head, tail) -> head <> concat tail
  *)

map (f: 'a -> 'b, list: list 'a) = match list with
  | None -> None
  | cons = xs -> cons = (head = f xs.head, tail = map (f, list = xs.tail)

mapFancy f list = match list with
  | None -> None
  | cons = xs ->
    cons =
      head = f xs.head
      tail = mapFancy f xs.tail

apply (x: 'a) (f: ('a, 'b) -> 'c): ('b -> 'c) =
  fun y -> f (x, y)

incAll = apply (f = fun x -> x + 1) map
```

## Modules

- Modules are records/products of value fields (ordinary atoms) `name = definition` and type fields `type name = definition`
- Type level project: `(type ty = def, _).ty` ≡ `def`
- Need to define some restrictions to avoid dependent types at the moment
  - Type fields allowed only in the top level module/record or in values of other modules

### Example

```ocaml
geometry =
  type vec = x: float, y: float
  move v1 v2 = (x = v1.x + v2.x, y = v1.y + v2.y)

a: geometry.vec = (x = 1, y = 1)
b = geometry.move a a
```

# The rest is a very rough idea dump, not to be discussed seriously yet

## Mutability

`mut` specifier of a declaration enables the `var := expr` expression.

## ECS

```ocaml

type pos = {mut x: float, mut y: float}
type vel = {mut dx: float, mut dy: float}

move: pos, vel, _ -> ()
move v = do
    v.x += v.dx
    v.y += v.dy
end
```



## Other
To investigate:
- Division: `product1 / product2`
  - Remove atoms from a product
- Negation: `sum1 - sum2`
  - Remove atoms from a sum
