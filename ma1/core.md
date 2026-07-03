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
universes, function types, polymorphism, application, and composition.

This is the **lambda-free phase**: no *anonymous* `fun`/`λ`, no `match`, no tactics,
no `∀`/`∃` sugar (quantifiers are the simply-typed `Forall`/`Exist` constants of
`classical_first_order_logic_new.cor`).
Abstraction survives only as the parameter telescope at the head of a `def`/`axiom` —
every function is a named, **closed** combinator whose body is built solely by
application and composition of constants and its own parameters. 

## Context

### Gentle introduction to types
Cantor describes a **set** as a well-defined collection of objects, called its elements. The intuition is that the elements come first and all of them together form the set.

A **type** is a collection of objects too. Its objects are called terms and the notation is `x : X` for `x` is a term of `X`. In contrast to sets, the terms of a type may join later.

For example, let's take all human first names as the collection of objects. We can form a set once we collect them all today. We can also declare the collection of human first names as type. Tomorrow a new human first name is given. It is well-identified as a term of the type, but we need to form a new set if we want to include it.

There is a trade off between sets and types. We already know the elements of a set, but have no flexibility to discover new. Types can grow dynamically, but we might not really know which terms they contain.

### Types of types, and dependent types
A type can itself be a term of another type. The type whose terms are (small)
types is the **universe** `Type`. So `X : Type` reads "`X` is a type", and then
`x : X` reads "`x` is a term of that type". `Prop` is the universe of propositions: a term
`P : Prop` is a proposition, and its terms are its proofs. `Prop` is
**impredicative** — for `X Y : Prop` the arrow `X → Y : Prop` again — so
propositions are closed under `→`, and every proposition doubles as the type of
its proofs (the "term = type" duality). Core's classical propositions live there:
`abbrev PC := Prop`. (Resting on `Prop` inherits Lean's proof irrelevance and
impredicativity, which Core does not itself axiomatize — a mild departure from
Core's self-contained goal, accepted for now.)

It is wrong to say quantifiers *force* dependent types — "a `∀` is a dependent
function into a proposition." That holds of the Curry–Howard *proof term* of `∀` (a
proof of `∀x. P x` is a dependent function `(x : X) → P x`), but **not** of the
quantifier itself. Two classical results place quantifiers in the simply-typed
world:

* **Church's simple type theory** (Church, 1940, *A Formulation of the Simple Theory
  of Types*, J. Symbolic Logic 5(2):56–68). Each quantifier is a *simply-typed*
  constant `∀_α : (α → o) → o`, with `o` the type of propositions and no dependent
  types anywhere; this is the basis of HOL (Isabelle/HOL, HOL Light). Core's
  quantifiers in `classical_first_order_logic_new.cor` are exactly such constants:
  `Forall (X Y : Type) (P : Pred (X × Y)) : Pred Y`, built only from `→`, `×` (product), and
  the fixed codomain `PC = Prop`.
* **Lawvere's adjoint characterisation** (Lawvere, 1969, *Adjointness in
  Foundations*, Dialectica 23:281–296; hyperdoctrines in Lawvere, 1970, *Equality in
  Hyperdoctrines…*, Proc. Sympos. Pure Math. XVII:1–14). `∀` and `∃` along a
  projection `X × Y → Y` are the right and left adjoints of weakening
  `Pred Y → Pred (X × Y)`. The two adjunction bijections *are* the intuitionistic
  `∀`-GEN / `∃`-GEN rules `ψ → ∀x P ⟺ ∀x(ψ → P)` and `∃x P → ψ ⟺ ∀x(P → ψ)`
  (`x ∉ ψ`), realised as `Forall.gen` / `Exist.gen`. Their side condition "`x` not
  free in `ψ`" is discharged **structurally** — `ψ : Pred Y` cannot mention the
  bound `x : X` — and substitution is reindexing along a base map `f : T → X`
  (`Forall.pull` / `Exist.push`, generalising PRED-1 / PRED-2), governed by the
  Beck–Chevalley condition.

So the *logic* needs no dependent types. Higher-order nesting like
`Pred (Pred (X × Y) × Z)` stays simply-typed: an arrow into the fixed `Prop` whose
*domain* may be built from `Prop` (Church's `o`) but whose *codomain* never varies
with the argument's value — that is higher-order logic, not dependency
(dependency = codomain varying with a *value*). Where dependent types become
genuinely unavoidable is narrower and *not* about `∀`/`∃`: it is **type families as
data** — a type in `Type` (not `Prop`) indexed by a value, e.g. `Vec : Nat → Type`
or `Fin n` (Martin-Löf, 1972; 1984, *Intuitionistic Type Theory*) — which the
`Prop`-fibre design here does not touch. Core still aligns its syntax with Lean's
dependent function types, because they are
needed there and remain the honest form of the Curry–Howard proof term when one
wants it.

## Syntax
Read the gentle [intro](#gentle-introduction-to-types) first.

Operators and keywords: `:`, `→` (ascii `->`), `∘`, `( )`, `×`, `Type`/`Prop`,
`def`, `abbrev`, `axiom`, `noncomputable`, `import`, `open`, `namespace`, `--`, `#check`.

* `--` starts a line comment (good until end of line); `/- ... -/` is a block comment.
* There is **no statement terminator**: commands are separated by newlines and keywords (no `;`).
* `x : X` reads "`x` is a term of type `X`". In a binder it is parenthesised, `(x : X)`, and several names of the same type may be grouped: `(x y : X)`.
* `Type` is the universe of types; `X : Type` means `X` is a type, and then `x : X` is a term of it. `Prop` is the universe of propositions (its terms are propositions, whose terms are proofs) and is impredicative. A universe is named with `abbrev`, e.g. `abbrev PC := Prop`.
* `X → Y` is the function type from `X` to `Y` (ascii `->` is also accepted). Arrows associate to the **right**: `X → Y → Z` means `X → (Y → Z)`. Use `( )` to override: `(X → Y) → Z` is different from `X → (Y → Z)`.
* Prod construction `X × Y` for any types. The terms of `X × Y` are exactly pairs of terms. We will use infrastructure operators to identify `X × Y -> Z` with `X -> Y -> Z` and `Z -> X × Y` with `(Z -> X) × (Z -> Y)`.
* Polymorphism: a definition or axiom may depend on generics as in `axiom myname (x0 : X0) (x1 : X1) ... ` followed by `:` (axioms and optionally defs) or `:=` (defs) and some body `e` in which `x0, x1, ...` can be ussed. `X1` may depend on `x0`, `X2` may depend on `x0, x1,...`. Note that the type of `myname` is the type of the body and may depend on `x0, x1,...`. 
* Application is **juxtaposition**: `f a` applies `f` to `a`. It associates to the **left**: `f a b` means `(f a) b`. For `f : X → Y → Z`, `a : X`, `b : Y`, we get `f a : Y → Z` and `f a b : Z`. If `f` is polymorphic, say `f (x0 x1 : X)`, then the parameters come first `f x0 x1 ...`. 
* Composition is `f ∘ g` (Lean's `Function.comp`): for `f : Y → Z` and `g : X → Y`, `f ∘ g : X → Z`. Composition and application are distinct operators. The convention for polymorphic `f, g` is that the generic paramaters must be supplied explicitly: say `f (x0 x1 : X)`, `g (y : Y)` then only `(f x0 x1) ∘ (g y)` is well-defined with explicitly defined `x0, x1, y`. 
* `axiom c : T` declares an exported, immutable constant of type `T` whose value is **postulated** — a primitive or an axiom, no definition given. This covers both a primitive type, `axiom X : Type`, and a primitive term, `axiom c : T`. Like `def`, an axiom may be polymorphic.
* `def c : T := e` defines an exported, immutable constant `c` of type `T` with value `e` (the signature may be omitted: `def c := e`). If `e` depends on any `axiom`, prefix with `noncomputable` (`noncomputable def c := e`) — Lean refuses to generate runtime code for axiom-backed definitions, and Core objects are not meant to be run anyway. `def` can take generic parameters as explained.
* `abbrev c := e` defines a transparent (reducible) abbreviation, used for naming a type or universe, e.g. `abbrev PC := Prop`.
* `import M` brings in every declaration of module `M`. A file may wrap its declarations in `namespace N ... end N`; then a declaration `X` of that file is accessed as `N.X`, and `open N` makes it available unqualified.
* **Naming.** Names must not collide with Lean's prelude. The examples rename several: `id`→`i_comb`, `Eq`→`SetEq`, `in`→`elem` (`in` is a Lean keyword), and `absurd`→`ex_falso`.
* `#check e` is a type-checker query: it elaborates `e` and reports its type. It is **scaffolding** with no effect on what a file defines (a by-product of Lean linking), used at the end of the example files to confirm signatures elaborate.

### Lambda lifting
The pattern is not allowed. For example if `def f (x : X) (y : Y) := e` and `t : X` then `(f t)` is not allowed (missing term `y`) and cannot be considered as a term in `Y -> ...`. The lean type checker will not catch this and it is up to discipline for now to enforce supply of all generic parameters until a native core syntax and type checker is available. 

## Type checker

This is a simply typed polymorphic language.

### Lean linking

For now we have borrowed Lean's type checker, see `lean_link.md` for details.

### Application, composition and evaluation order
Bracketed sub-expressions are evaluated first; the result is used as a single
element in the surrounding expression. Otherwise:

1. **Application** `f a` is juxtaposition and associates left: `f a b = (f a) b`. It type-checks when the type of `a` matches the domain of `f`.
2. **Composition** `f ∘ g` type-checks when the codomain of `g` matches the domain of `f`, and has type `X → Z` for `g : X → Y`, `f : Y → Z`.
3. **Arrows** `→` associate right: `X → Y → Z = X → (Y → Z)`.
4. **Relative precedence** is application > `∘` > `→`: application binds tightest, then composition, then the arrow. So `elem x a -> elem x b` parses as `(elem x a) → (elem x b)`, and `not_intro A B ∘ imply_elim A B` composes the two applications.

Unlike earlier drafts, a single operator no longer stands for both application and
composition: `f a` is always application and `f ∘ g` is always composition, so no
domain/codomain disambiguation rule is needed.