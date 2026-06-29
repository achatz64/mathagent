# Core Specification

Core is the backbone language for ma1. 

## Context

### Gentle introduction to types
Cantor describes a **set** as a well-defined collection of objects, called its elements. The intuition is that the elements come first and all of them together form the set. 

A **type** is a collection of objects too. Its objects are called terms and the notation is `x : X` for `x` is a term of `X`. In contrast to sets, the terms of a type may join later. 

For example, let's take all human first names as the collection of objects. We can form a set once we collect them all today. We can also declare the collection of human first names as type. Tomorrow a new human first name is given. It is well-identified as a term of the type, but we need to form a new set if we want to include it. 

There is a trade off between sets and types. We already know the elements of a set, but have no flexibility to discover new. Types can grow dynamically, but we might not really know which terms they contain.

## Syntax
Read the gentle [intro](#gentle-intro-to-types) first. 
Language has special symbols: `:`, `->`, `.`, `()`, `type`, `let`, `const`, `< >`, `;`, `,`, `have`, `//`, `#`.  
* `;` is the end of one statement. 
* `x : X` for `x` is a term of type `X`. For convenience, we can use `x_0, x_1 : X` for more than one terms of the same type.
* new type construction `X -> Y` for two types `X`, `Y`, imagine fcts from `X` to `Y`. 
* `f.g : X -> Z` for `f: Y -> Z` and `g: X -> Y`, imagine composition of fcts. For a term `g : Y`, we get `f.g: Z`. For longer chains we need to use brackets to clarify order, e.g. `(f.g).h` in contrast to `f.(g.h)` (see [here](#types-of-compositions-and-evaluations)). The symbol `.` is also used in `SomeName.x` for a name declared in `have` (see `have`).
* We need `( )` to clarify the order. For example `(X -> Y) -> Z` is not the same as `X -> (Y -> Z)`. Without brackets we imagine the arrows bounded from right to left, that is we can simply write `X -> Y -> Z` for `X -> (Y -> Z)`.  
* `type X;` for declaring a type, cannot be overwritten. The terms of `X` can naturally be considered as types too. 
* `let h = f.g;` for variable assignment for terms, which can be overwritten. A value is required; the signature-only form `let h : T;` is not allowed.
* `const h = f.g;` for variable assignment for terms, which cannot be overwritten, and will be exported. The signature-only form `const c : T;` is also allowed: it declares an exported, immutable constant of type `T` whose value is postulated (a primitive or axiom, no definition given).
* `m<X : T> : X -> Z` for generics, evidently we implicitly consider the terms of `T` as types again. Can be iterated `m<X : T><Y : X> : Y -> Z` and listed for convenience `m<X: T, Y: U>: X -> Y -> Z`. If used without type specification as in `m<X>: X -> X` for example, then it is defined for all types.
* type construction `X # Y` for two types `X`, `Y`, think of cartesian product.
* `have SomeName (somepath);` for import of all types and terms declared by `type` and `const` from `somepath`. The `SomeName` is optional, if given the types and terms in the file `somepath` are accessible via prepending `SomeName`; that is, if `X` is declared in `somepath` then `SomeName.X` is the name. If no `SomeName` is given then everything is imported with identical names.   
* `//` for starting a comment (one line and good until the end of line)

## Type checker

### Types of compositions and evaluations

Bracketed sub-expressions are evaluated first; the result is used as a single element in the surrounding chain. Within any bracket-free chain `e.f.g.h..`, evaluation proceeds left-to-right: we know `e: X -> Y`, and then:

1. if `f: T -> X` => composition: `(e.f).g.h..`
2. if `f: X` => evaluation: `(e.f).g.h..`
3. else the expression is not well-typed.