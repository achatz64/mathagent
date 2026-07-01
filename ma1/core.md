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

This is the **lambda-free phase**: no *anonymous* `fun`/`λ`, no `match`, no tactics,
no `∀`/`∃` sugar (quantifier binders are spelled as dependent function types).
Abstraction survives only as the parameter telescope at the head of a `def`/`axiom` —
every function is a named, **closed** combinator whose body is built solely by
application and composition of constants and its own parameters. Parameters may depend
on earlier ones *through their types* (the telescope stays closed), so this is
combinatory term structure over a *dependent* type theory, not pure `S`/`K`. It is
lambda calculus restricted to a **lambda-lifted (combinatory) form** — not a weaker
calculus, since every λ-term *admits* such a translation, but not a *normal* form
either: the translation is a choice (which subexpressions become defs, their arity and
capture order), unique only relative to a fixed lifting algorithm. Bracket abstraction
to a fixed `S`/`K` basis (`SK_combinators.cor`) is the sharper route but reaches only
the non-dependent, propositional fragment. This confinement of the λ to declaration
heads is the reverse of the anonymous `fun` that the **ma1** lambda language layers on
top (see [ma1.md](ma1.md)).

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

Operators and keywords: `:`, `→` (ascii `->`), `∘`, `( )`, `Type`/`Prop`,
`def`, `abbrev`, `axiom`, `noncomputable`, `import`, `open`, `namespace`, `--`, `#check`.

* `--` starts a line comment (good until end of line); `/- ... -/` is a block comment.
* There is **no statement terminator**: commands are separated by newlines and keywords (no `;`).
* `x : X` reads "`x` is a term of type `X`". In a binder it is parenthesised, `(x : X)`, and several names of the same type may be grouped: `(x y : X)`.
* `Type` is the universe of types; `X : Type` means `X` is a type, and then `x : X` is a term of it. `Prop` is the universe of propositions (its terms are propositions, whose terms are proofs) and is impredicative. A universe is named with `abbrev`, e.g. `abbrev PC := Prop`.
* `X → Y` is the function type from `X` to `Y` (ascii `->` is also accepted). Arrows associate to the **right**: `X → Y → Z` means `X → (Y → Z)`. Use `( )` to override: `(X → Y) → Z` is different from `X → (Y → Z)`.
* `(x : X) → B` is a **dependent function type**: the codomain `B` may mention `x`. If `B` does not mention `x` it is the same as `X → B`.
* Application is **juxtaposition**: `f a` applies `f` to `a`. It associates to the **left**: `f a b` means `(f a) b`. For `f : X → Y → Z`, `a : X`, `b : Y`, we get `f a : Y → Z` and `f a b : Z`.
* Composition is `f ∘ g` (Lean's `Function.comp`): for `f : Y → Z` and `g : X → Y`, `f ∘ g : X → Z`. Composition and application are now **distinct** operators (Core no longer overloads a single `.` for both).
* `axiom c : T` declares an exported, immutable constant of type `T` whose value is **postulated** — a primitive or an axiom, no definition given. This covers both a primitive type, `axiom X : Type`, and a primitive term, `axiom c : T`. Like `def`, an axiom may take explicit parameters, `axiom c (p : A) : T` (see *Parameterized declarations* below); nearly every axiom in `classical_first_order_logic.cor` and `set.cor` uses this form.
* `def c : T := e` defines an exported, immutable constant `c` of type `T` with value `e` (the signature may be omitted: `def c := e`). If `e` depends on any `axiom`, prefix with `noncomputable` (`noncomputable def c := e`) — Lean refuses to generate runtime code for axiom-backed definitions, and Core objects are not meant to be run anyway. `def` can take parameters (generics and ordinary/proof arguments alike) as explained below.
* `abbrev c := e` defines a transparent (reducible) abbreviation, used for naming a type or universe, e.g. `abbrev PC := Prop`.
* **Parameters are explicit; generics are just type-valued parameters.** A declaration takes explicit parameters `(x : X)` to the left of `:` — these may be terms, proofs, or types, treated uniformly (see *Parameterized declarations*). A polymorphic constant is the special case where a parameter is a type, supplied explicitly at every use site. `m (X : T) : X → Z` is declared with `(X : T)` and used as `m A`. Several may be grouped, `m (X : T) (Y : U) : ...`, or share a type, `(X Y : T)`. A *constrained* generic targets a specific universe, e.g. `(A B : Prop)` for parameters ranging only over propositions (Core's structural combinators use this, so they apply to propositions, not arbitrary types); an *unconstrained* parameter is `(X : Type)` (defined for all types). Type parameters and term parameters are thus uniform — exactly the unification that dependent types provide. (Core does **not** use Lean's implicit `{ }` arguments: nothing is left to inference.)
* `import M` brings in every declaration of module `M`. A file may wrap its declarations in `namespace N ... end N`; then a declaration `X` of that file is accessed as `N.X`, and `open N` makes it available unqualified.
* **Naming.** Names must not collide with Lean's prelude. The examples rename several: `id`→`i_comb`, `Eq`→`SetEq`, `in`→`elem` (`in` is a Lean keyword), and `absurd`→`ex_falso`.
* `#check e` is a type-checker query: it elaborates `e` and reports its type. It is **scaffolding** with no effect on what a file defines (a by-product of Lean linking), used at the end of the example files to confirm signatures elaborate.

### Parameterized declarations

A parameter list to the left of `:` binds arguments for the whole declaration. For
`def c (p₁ : A₁) … (pₙ : Aₙ) : B := e` (and likewise `axiom c (p₁ : A₁) … (pₙ : Aₙ) : T`):

* the **type** of `c` is the dependent function type `(p₁ : A₁) → … → (pₙ : Aₙ) → B`; the parameters become the leading Π-binders, and each `Aᵢ` may mention earlier `pⱼ` (a *dependent telescope*, e.g. `def SetEq_sym (a b : Sets) (h : SetEq a b) …` where `h`'s type mentions `a b`).
* the annotation `B` is the type of the **body** `e` with `p₁…pₙ` in scope — **not** the type of `c` itself.
* the value binds `p₁…pₙ` over `e`. The honest desugaring is `fun p₁ … pₙ => e`, but this phase has no `fun`, so a parameter list is the **only** way to give a value that binds variables: it is primitive syntax, not removable sugar.

Do not confuse the two binder roles. `(x : X) →` **inside a type** writes a ∀; `(x : X)` **left of `:`** is a parameter. They are *not* interchangeable:

* `def Subset (a b : Sets) : PC := (x : Sets) -> imply (elem x a) (elem x b)` gives the **relation** `Subset : Sets → Sets → PC`, used applied as `Subset x A`.
* `def Subset : PC := (a b x : Sets) -> imply (elem x a) (elem x b)` gives a **single closed proposition** `∀a∀b∀x. …`, which cannot be applied.

Moving the binders across `:=` collapses a `Sets → Sets → PC` family into a lone `PC`.

## Idioms (lambda-free phase)

### Building predicates without λ (lambda lifting)

Quantifier axioms take a predicate argument (`Forall`/`Exist … (P : Pred X)`), normally
supplied as `fun x => …`. With no `fun`, Core uses **lambda lifting**: the compiler
transformation that replaces an anonymous function by a named top-level one whose free
variables become extra leading parameters. Concretely, define a `def` whose **last**
parameter is the bound variable and whose leading parameters are the captured free
variables, then **partially apply** to the free variables to leave exactly a `Pred X`.

Example (Pairing, `set.cor`):

    def pairBody (a b c : Sets) : PC := (x : Sets) -> iff (elem x c) (or (SetEq x a) (SetEq x b))
    axiom pairing (a b : Sets) : Exist Sets (pairBody a b)

Here `c` (the intended bound variable) is last and `a b` are the lifted free variables, so
`pairBody a b : Sets → PC` is the predicate `Exist` needs. Nested quantifiers nest the
pattern (`unionWit` inside `unionBody`).

### Flip / reordering helpers

Partial application fixes only **leading** arguments, so to abstract over an argument that
is not leftmost, introduce a helper whose parameter order puts the intended bound variable
last. Example: `elem : Sets → Sets → PC` fixes its *first* argument, so to form the
predicate `· ∈ x` (abstracting the **left** operand) define

    def memOf (x w : Sets) : PC := elem w x

and use `memOf x : Pred Sets`. This is the `flip` combinator done by hand.

## Generics discipline: infrastructure vs. math

Sections *Parameterized declarations* and *Idioms* expose a tension. A parameterized
`def` **is** lambda abstraction (`def f (a : A) := e` ≡ `fun a => e`), so the parameter
syntax lets *any* definition introduce a bound variable and consume it in its body — a
λ. When this happens in ordinary mathematics (`def Subset (a b : Sets) := …`,
`def memOf (x w : Sets) := elem w x`), the λ has **leaked** out of the small set of
primitives that ought to own abstraction and into the open-ended math layer. Core is
then only superficially lambda-free: abstraction is everywhere, merely spelled as
parameter lists.

The discipline that fixes this splits the language into two layers.

1. **Infrastructure (the "syntax layer").** A fixed, well-defined vocabulary of
   *polymorphic primitives*: the combinators (`weakening` = K, `s_comb` = S,
   `exchange` = C, `i_comb` = I, composition `∘` = B — currently postulated at `Prop`
   in `SK_combinators.cor`, to be generalized to `Sort` so they cover `Sets` too), the
   quantifier/description formers (`Forall`, `Exist`, `the`), and the structural/logical
   rules (`imply_intro`, `and_elim_*`, …). **Only these may carry generics** (type
   parameters). Because they are a small, closed, standard set, they read as an
   *extended syntax* — notation for building types and threading arguments — rather than
   as ordinary definitions. Their genericity is polymorphism in a *type*, with no λ in a
   body: the formers and rules are axioms (no body at all), and the combinators are the
   designated home of abstraction.

2. **Mathematics (generics-free, variable-free).** Every mathematical definition and
   proof is written with an **empty parameter list** — `def foo := <closed expression>`
   — and no bound variables of its own. It is a **point-free** combination, by
   composition (`∘`), application (evaluation), and the infrastructure operations, of
   terms that were **already constructed** (earlier proofs or math terms). No math
   object introduces a new abstraction; it only recombines existing ones.

The resulting invariant:

> **generics ⟺ infrastructure.** The math layer carries no type parameters and no bound
> term variables; all abstraction lives in the fixed infrastructure vocabulary.

**Worked evidence.** `memOf`, `Subset`, `SetEq` (`set.cor`) rewrite to closed
point-free defs — e.g. `memOf := exchange Sets Sets PC elem`, and
`Subset := Bcomb … (Forall Sets) …` — each with *no* parameters; the combinators supply
every `Sets`/`PC` explicitly, and the math def stays generic-free. Each was verified to
type-check against the Core axioms.

### Infrastructure vocabulary

The fixed, generic vocabulary that Rule 1 admits — what the math layer is built from.
This is what identifiers like `Bdep`, `Arrow`, `Wcomb` above refer to.

**Value combinators.** The **essential basis is `I`, `K`, `S`** (with `S` in its
dependent form `Sdep`); everything else *derives* from these. All are in
`SK_combinators.cor` today (at `Prop`; **to be generalized to `Sort`** to cover `Sets`).

* `i_comb` (**I**) — `I a = a` (identity)
* `weakening` (**K**) — `K a b = a` (constant)
* `s_comb` (**S**) — `S f g a = f a (g a)` (share the argument)

Derived shorthands — convenient, **not primitive** (each is an `S`/`K` combination):

* `∘` (**B**) — `(f ∘ g) a = f (g a)` (compose; dependent form `Bdep`)
* `diagonal` (**W**) — `W f a = f a a` (contraction; dependent *codomain* only)
* `Φ f g h a = f (g a) (h a)` (`= S (B f g) h`), used in point-free `Subset`
* `exchange` (**C**) — `C f b a = f a b` (flip; **non-dependent only** — see below)

`exchange` in particular must *not* be treated as a basis combinator. It is redundant
(`C = S ([x]M) (K N)` covers its role) and has **no dependent form**, yet its
non-dependent type is perfectly valid, so nothing about `exchange` or its non-dependent
uses is flagged. Worse, Core's *own* proposed checker (see *Type checker*) is specified
only for **simple arrows** — it does not model dependent application — so it would **not
catch a dependent misuse of `exchange` at all**. (Lean, the convenience checker of this
phase, does reject such misuses, but Lean is **not** Core's checker.) Confining `C` to
non-dependent positions is therefore purely a **discipline** obligation. That is why the
basis is `I`/`K`/`S` and `C` is a mere convenience.

**Dependent combinators.** Needed when a codomain depends on a *value* (the extra
`Sort`-valued arguments are the type families). **To be added:**

* `Bdep` — dependent compose: for `g : A → β` and `f : (b : β) → C b`, gives
  `(a : A) → C (g a)`.
* `Sdep` — dependent share: for `B : A → Sort`, `C : (a : A) → B a → Sort`,
  `f : (a : A) → (b : B a) → C a b`, `g : (a : A) → B a`, gives `(a : A) → C a (g a)`.

**Which dependent forms go through** (all checked in Lean). The principle: a combinator's
dependent generalization type-checks **exactly when it never requires a later-bound
variable in an earlier binder's type**.

* `I`, `K`, `B`, `S`, `Φ` apply their arguments in binding order, so forward
  dependencies stay in scope — all go through (`S` is the fully dependent one; `K`'s
  discarded argument may have an `a`-dependent type; `B`/`Φ` thread through fixed middle
  types with dependent codomains).
* `W` reuses one value in two slots, which forces the two argument types to be *equal
  and non-dependent*; only its **codomain** may depend (`Wdep : (a:A) → C a a`).
* `C`/flip is the **sole exception** — the one combinator that *permutes* arguments.
  Flipping `f : (x : X) → P x → Z` would place `x` out of scope in the moved binder, so a
  "dependently flipped" type does not exist (verified: rejected). Harmless, since `C`
  enters bracket abstraction only as the `x ∉ N` optimization of `[x](M N)`, always
  replaceable by `S ([x]M) (K N)` with dependent `S`.

So the **essential** dependent basis is `I`, `K`, and dependent `S` (`Sdep`); `Bdep`/`Φ`
are handy, `C`/`W` are non-dependent (resp. dependent-codomain-only) conveniences.

**Type-level formers.** The combinators thread arguments through types that these build:

* `Arrow X Y := X → Y` — the function-type former as an *applicable* constant (**to be
  added**; lets a type-λ like `fun X => X → X` become `W Arrow`).
* `Forall X (P : Pred X)`, `Exist X (P : Pred X)` — the Π/∃ formers (axioms,
  `classical_first_order_logic.cor`).
* `the X E (P : Pred X)` — description (axiom, `definite_description.cor`).
* `Pred X := X → PC` (abbrev).

**Logical structural rules.** The connectives and their intro/elim — `and`, `or`, `not`,
`imply` with `*_intro`/`*_elim`, plus `excluded_middle`, `double_negation_elim`,
`Forall_intro`/`_elim`, `Exist_intro`/`_elim` — all axioms in
`classical_propositional_logic.cor` / `classical_first_order_logic.cor`.

Minimality vs. computation is the knob below: `S` and `K` alone generate
`I`/`B`/`C`/`W`, so the combinators *can* be a two-axiom core; but realizing the derived
ones (and `Bdep`/`Sdep`/`Arrow`) as **transparent** defs is what lets math terms reduce.
The formers and structural rules are genuine axioms regardless.

**Two honest caveats.**

* *Completeness.* The dependent case — a math term whose *type* depends on a value
  argument (`induction … n : P n`) — is **not** an obstruction. It is handled by the
  **dependent** combinators (dependent composition / `S`), whose type-family arguments
  are themselves point-free. Verified: the genuinely dependent
  `(P : Pred Sets) → (n : Sets) → P n → P n` rewrites fully point-free as
  `Bdep Sets PC (Wcomb PC PC Arrow) Icomb` — no value binders, the residual type-λ
  eliminated via `W` and an `Arrow` former — and is defeq to `fun P n p => p`. The price
  is that the infrastructure must also carry **type-level** formers/combinators
  (`Arrow`, `W`, the Π-former `Forall`), not just value-level `S`/`K`. The only open
  part is bookkeeping: confirming this infrastructure closure stays a fixed, finite
  vocabulary across the whole corpus — every case seen so far does.
* *Axiom vs. computation.* Making a former an **axiom** is what makes it a pure,
  non-leaking primitive — but an axiom does not reduce, so terms built on it are opaque
  (`Subset a b` no longer unfolds to `∀x …`; one reasons about it via `Forall_elim` /
  `Forall_intro`, verified). Realising the combinators as *transparent* notation instead
  lets math terms compute, at the cost of a (harmless, lambda-lifted) body. The formers
  (`Forall`, `Exist`, `the`) are genuine axioms; whether the **combinators** are axioms
  or transparent notation is the remaining knob.

## Type checker

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

### Dependent application — a specification gap

The rules above are stated for **simple arrows** only. They do not yet describe
**dependent application**: for `f : (x : X) → B x`, the result type of `f a` is
`B[a/x]` (the codomain with the argument substituted), and checking a telescope
`(p₁ : A₁) … (pₙ : Aₙ)` requires tracking scope so that each `Aᵢ` sees the earlier
`pⱼ`. None of this is captured by "the type of `a` matches the domain of `f`."

This matters because the entire point-free-with-dependent-combinators program
(`Sdep`, `Bdep`, the type families, the `Prop → Type` discipline) lives in dependent
type theory. So Core's proposed checker is **currently under-specified for exactly the
cases that carry the design** — e.g. it would not, as written, catch a dependent misuse
of `exchange`. During this phase Lean supplies the missing dependent checking (see *Lean
linking*); a native Core checker will need an explicit dependent-application rule
(substitution into the codomain + telescope scoping) added here. Wherever this document
says a term was "verified" or "type-checks", that means **Lean accepted it** — a
convenience, not a statement about Core's own (simpler, incomplete) checker.

### Definitional equality (reduction during checking)

Type checking compares types up to **definitional equality**, so the checker silently
performs:

* **delta** — unfolding a `def` or `abbrev` to its body. `abbrev` unfolds eagerly; a `def` unfolds when needed to make two types match. Both are relied on: `iff` is a `def`, yet `h : iff A B` is accepted where `and (imply A B) (imply B A)` is expected (`iff_mp`), and `ExistUnique …` (a `def`) is fed to `and_intro`/`and_elim`.
* **beta** — applying such an unfolded definition to its arguments by substitution, e.g. `omega_spec emptyset` reduces `sepBody Inf omegaPred omega` and substitutes `emptyset`.

`abbrev` and `def` therefore differ only in the *eagerness* of unfolding, not in whether a
name is equal to its body.
