# Core Specification

Core is the backbone language for ma1.

During this phase Core is a **restricted subset of Lean 4**: every `.cor` file is
written so that Lean's type checker accepts it verbatim. This lets us check `.cor`
code with Lean until Core has its own checker, and it ties Core to a language that
is well known and widely used. Core nonetheless defines a **self-contained**
language: every type and term used is declared inside the `.cor` sources (via
`axiom`/`def`/`abbrev`), never silently borrowed from Lean's library, and Core
relies on no implicit Lean machinery (typeclass resolution, tactics, coercions,
elaboration sugar). The only thing Core takes from Lean is the bare type theory:
universes, function types, dependent function types, application, and composition.

This is the **lambda-free phase**: only the bare-minimum operators below are used.
No `fun`/`λ`, no `match`, no tactics, no `∀`/`∃` sugar — binders that quantifiers
need are spelled explicitly as dependent function types.

## Context

### Gentle introduction to types
Cantor describes a **set** as a well-defined collection of objects, called its elements. The intuition is that the elements come first and all of them together form the set.

A **type** is a collection of objects too. Its objects are called terms and the notation is `x : X` for `x` is a term of `X`. In contrast to sets, the terms of a type may join later.

For example, let's take all human first names as the collection of objects. We can form a set once we collect them all today. We can also declare the collection of human first names as type. Tomorrow a new human first name is given. It is well-identified as a term of the type, but we need to form a new set if we want to include it.

There is a trade off between sets and types. We already know the elements of a set, but have no flexibility to discover new. Types can grow dynamically, but we might not really know which terms they contain.

### Types of types, and dependent types
A type can itself be a term of another type. The type whose terms are (small)
types is the **universe** `Type`. So `X : Type` reads "`X` is a type", and then
`x : X` reads "`x` is a term of that type". `Type` is itself a term of a larger
universe (`Type : Type 1`), and `Prop` is the universe of propositions: a term
`P : Prop` is a proposition, and its terms are its proofs. `Prop` is
**impredicative** — for `X Y : Prop` the arrow `X → Y : Prop` again — so
propositions are closed under `→`, and every proposition doubles as the type of
its proofs (the "term = type" duality). `Prop` is also a genuinely *separate*
universe (`Prop ≠ Type`, so e.g. `Nat : Prop` is false), which isolates
propositions from data types. Core's classical propositions live there:
`abbrev PC := Prop`. (Resting on `Prop` inherits Lean's proof irrelevance and
impredicativity, which Core does not itself axiomatize — a mild departure from
Core's self-contained goal, accepted for now.)

A **dependent function type** `(x : X) → B` is a function type whose codomain `B`
may mention the argument `x`. When `B` does not mention `x` it degenerates to the
ordinary arrow `X → B`. Dependent function types are what let us write quantifiers
(a `∀` is a dependent function into a proposition), so Core needs them and Lean
supplies them — this is the reason for aligning Core's syntax with Lean.

## Syntax
Read the gentle [intro](#gentle-introduction-to-types) first.

Operators and keywords: `:`, `→` (ascii `->`), `∘`, `×`, `( )`, `Type`/`Sort`/`Prop`,
`def`, `abbrev`, `axiom`, `import`, `open`, `namespace`, `--`.

* `--` starts a line comment (good until end of line); `/- ... -/` is a block comment.
* There is **no statement terminator**: commands are separated by newlines and keywords (no `;`).
* `x : X` reads "`x` is a term of type `X`". In a binder it is parenthesised, `(x : X)`, and several names of the same type may be grouped: `(x y : X)`.
* `Type` is the universe of types; `X : Type` means `X` is a type, and then `x : X` is a term of it. `Prop` is the universe of propositions (its terms are propositions, whose terms are proofs) and is impredicative; `Sort` is the general universe. A universe is named with `abbrev`, e.g. `abbrev PC := Prop`.
* `X → Y` is the function type from `X` to `Y` (ascii `->` is also accepted). Arrows associate to the **right**: `X → Y → Z` means `X → (Y → Z)`. Use `( )` to override: `(X → Y) → Z` is different from `X → (Y → Z)`.
* `(x : X) → B` is a **dependent function type**: the codomain `B` may mention `x`. If `B` does not mention `x` it is the same as `X → B`.
* Application is **juxtaposition**: `f a` applies `f` to `a`. It associates to the **left**: `f a b` means `(f a) b`. For `f : X → Y → Z`, `a : X`, `b : Y`, we get `f a : Y → Z` and `f a b : Z`.
* Composition is `f ∘ g` (Lean's `Function.comp`): for `f : Y → Z` and `g : X → Y`, `f ∘ g : X → Z`. Composition and application are now **distinct** operators (Core no longer overloads a single `.` for both).
* `X × Y` is the product type (Lean's `Prod`); a pair is `(a, b)`, and the projections of `p : X × Y` are `Prod.fst p : X` and `Prod.snd p : Y`.
* `axiom c : T` declares an exported, immutable constant of type `T` whose value is **postulated** — a primitive or an axiom, no definition given. This covers both a primitive type, `axiom X : Type`, and a primitive term, `axiom c : T`.
* `def c : T := e` defines an exported, immutable constant `c` of type `T` with value `e` (the signature may be omitted: `def c := e`). If `e` depends on any `axiom`, prefix with `noncomputable` (`noncomputable def c := e`) — Lean refuses to generate runtime code for axiom-backed definitions, and Core objects are not meant to be run anyway. `def` can use generics as explained below.
* `abbrev c := e` defines a transparent (reducible) abbreviation, used for naming a type or universe, e.g. `abbrev PC := Prop`.
* **Generics are ordinary explicit parameters.** A polymorphic constant takes its type arguments as explicit parameters and they are supplied explicitly at every use site. `m (X : T) : X → Z` is declared with `(X : T)` and used as `m A`. Several may be grouped, `m (X : T) (Y : U) : ...`, or share a type, `(X Y : T)`. A *constrained* generic targets a specific universe, e.g. `(A B : Prop)` for parameters ranging only over propositions (Core's structural combinators use this, so they apply to propositions, not arbitrary types); an *unconstrained* parameter is `(X : Type)` (defined for all types). Type parameters and term parameters are thus uniform — exactly the unification that dependent types provide. (Core does **not** use Lean's implicit `{ }` arguments: nothing is left to inference.)
* `import M` brings in every declaration of module `M`. A file may wrap its declarations in `namespace N ... end N`; then a declaration `X` of that file is accessed as `N.X`, and `open N` makes it available unqualified.
* **Naming.** Names must not collide with Lean's prelude. For instance `id` is reserved by Lean, so the identity combinator is named `i_comb`.

## Type checker

### Lean linking

For now we have borrowed Lean's type checker, see `lean_link.md` for details.

### Application, composition and evaluation order
Bracketed sub-expressions are evaluated first; the result is used as a single
element in the surrounding expression. Otherwise:

1. **Application** `f a` is juxtaposition and associates left: `f a b = (f a) b`. It type-checks when the type of `a` matches the domain of `f`.
2. **Composition** `f ∘ g` type-checks when the codomain of `g` matches the domain of `f`, and has type `X → Z` for `g : X → Y`, `f : Y → Z`.
3. **Arrows** `→` associate right: `X → Y → Z = X → (Y → Z)`.

Unlike earlier drafts, a single operator no longer stands for both application and
composition: `f a` is always application and `f ∘ g` is always composition, so no
domain/codomain disambiguation rule is needed.
