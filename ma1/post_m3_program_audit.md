# Post-M3 program audit: Program C

`proof_search.md` is the frozen record of Program PS.  This file is the
authoritative specification and status record for Program C.

## Goal

Program C proves that contextual FOL/HOL is a proof-relevant presentation of
Core with explicit object variables and assumptions.  It must cover the Core
terms, formulas, and proofs accepted by the native checker, rather than a
selected collection of examples.

For translations `a` (contextual to Core) and `b` (Core to contextual), the
required correspondences are:

```text
terms:    b(a(t)) = normalize(t)       a(b(e)) =defeq e
formulas: Gamma | [] |- iff phi (b(a(phi)))
          CoreThm (Pred.iff P (a(b(P))))
proofs:   Gamma | Delta |- phi
          iff Core has a checked proof of a(Gamma | Delta |- phi)
```

The proof object is an inspectable tree
`Deriv E Gamma Delta phi : Type`.  Provability is its propositional truncation:

```text
Proves E Gamma Delta phi := Nonempty (Deriv E Gamma Delta phi)
```

There is no raw-Core or theorem-specific escape constructor.

## C0 one-shot foundation

The first implementation fixes the target types before quotation begins.

1. Types include function types.  The signature records typed, fully-applied
   function heads and typed predicate heads.  Constants are nullary functions;
   application of a function-valued term is represented separately.
2. Term and formula *shapes* are proof-erased and have decidable structural
   equality, so substitution and proof search can use them as keys.
3. Accepted terms/formulas carry `Type`-valued evidence.  In particular, a
   description shape is accepted only with a `Deriv` of its exact
   unique-existence formula.  The proof-free shape is internal data, not an
   accepted contextual term.
4. Description initially mirrors the existing Core infrastructure exactly:
   `hasChar`/`ExistUnique`/`the`/`the_spec` and the negative
   `hasCharNeg`/`ExistUniqueNeg`/`theNeg`/`theNeg_spec` path from
   `definite_description.cor`.  Genuinely arbitrary `iota x. P(x)` is outside
   this foundation and is a later compiler/infrastructure obligation.
5. `Deriv` mirrors every rule of the existing contextual calculus, separates
   closed ground axioms from parameterized contextual `TheorySchema` rules,
   and adds only the two generic description specification rules.  A schema
   records its schematic telescope, object context, and contextual conclusion.
   It contains neither raw Core evidence nor named theorem shortcuts.
6. The existing proof-search development remains usable through explicit
   erasure/compatibility adapters while it is migrated.  The old inductive
   `Proves : Prop` is removed only after all consumers use `Nonempty Deriv`.

### Exit condition

The C0 foundation exits when the final function/description syntax and
`Deriv` type check, descriptions cannot be constructed without derivation
evidence, every old calculus rule has a `Deriv` constructor, compatibility
adapters keep the Lean project building, and the boundary below is stated
without a completeness claim.

## Immediate next step: Core to Deriv

Immediately after C0, implement quotation of Core terms, formulas, and checked
proofs into the fixed syntax and `Deriv`.  Core beta rules enter here: they
normalize explicit combinator applications and justify the two round trips.
Whenever a checker-accepted expression cannot be quoted, the failure must be
classified as a missing contextual constructor or missing beta rule; it may not
be bypassed with raw syntax.

Only after bidirectional translation and beta adequacy may actual statements
and proofs from `set_constructions.cor` be claimed as a correspondence test.
Manually reproving analogous contextual statements tests expressiveness but
does not establish correspondence with those Core proofs.

## Core-to-Deriv one-shot status

`formalization/ContextualHOL/CoreQuote.lean` now defines the first checked
functional boundary:

```text
quoteCheckedDecl : CoreChecker.Env -> CoreChecker.Decl ->
  Except QuoteError QuotedDeriv
```

`QuotedDeriv` contains the checked Core type and body together with `E`,
`Gamma`, `Delta`, `phi`, and an actual value of `Deriv E Gamma Delta phi`.
It is not a raw-Core certificate. Transparent Core definitions are normalized;
proposition parameters enter `Gamma`, proof parameters enter `Delta`, opaque
native axiom instances become generic contextual theory schemas, native proof
application becomes `mp`, and native proof composition is expanded with the
contextual `K` and `S` constructors.

This one-shot intentionally fixes only the minimal propositional path. It
classifies, rather than hides, the currently unimplemented cases:

* object terms and arbitrary predicate application require the function and
  predicate refunctionalization pass;
* proof-producing object functions require a further contextual constructor;
* Core `Forall`/`Exist` encodings require contextual-binder beta recognition;
* `the`/`the_spec` and the negative description path require the dedicated
  proof-dependent description beta pass. They may not pass through a generic
  theory or raw-term shortcut.

Consequently this is a checked Core-to-`Deriv` function, but not yet the total
Core-to-`Deriv` theorem required by Program C. The next falsifiable milestone is
to remove the four classified cases above, beginning with refunctionalization
and description, while preserving the same result type.

The present Lean function is `noncomputable` only because the mutually
recursive term/formula shapes do not yet expose a constructive
`DecidableEq`; it uses classical structural equality while assembling the
dependent package. Replacing that equality instance is required before this
same function can be run as a native quotation executable.

## `set.cor` theory-schema/environment one-shot

`formalization/ContextualHOL/SetTheoryQuote.lean` implements the next bounded
one-shot.  It checks and recursively loads the real `ma1/set.cor` import graph,
then refunctionalizes the canonical predicate/context encoding into a
`ProgramC.Env`.  Native expressions occur only at the input boundary; the
successful result contains only contextual types, terms, formulas, schema
telescopes, and theory data.

The refunctionalizer recognizes `Pred.term`, `Forall`, `Exist`, predicate and
propositional connectives, `sub2`, `inst`, composition, projections, pairing,
and `Cart.weakening`, with transparent named definitions unfolded one head
step at a time.  It does not dispatch to prewritten formulas by theorem name
and has no opaque formula fallback.

The resulting vocabulary is the base type `Sets`, binary predicate `elem`, and
nullary function `Inf`.  It translates all ten set axioms.  Source object
parameters remain in each schema's `objects : Ctx`; separation records the
unary schematic predicate `separation.phi`, and replacement records the binary
schematic predicate `replacement.phi`.  `deriveTheory` reconstructs
`FormulaEvidence` and an inspectable `DerivRaw.schema` tree for each translated
open schema.  The executable `quote_set_theory` currently reports:

```text
quoted 10 set theory schemas
constructed 10 contextual Deriv trees
```

This milestone is the declaration/environment translation, not yet quotation
of arbitrary downstream applications of those schemas.  At use sites, object
specialization remains visible through contextual substitution; implementing
typed predicate/function-schema substitution for applications such as a
particular use of separation or replacement is the next proof-quotation
obligation.  No completeness claim for arbitrary dependent Core declaration
telescopes is made here.

## Falsifiers

Program C fails if any checker-accepted in-scope Core expression requires a raw
escape, if description can be formed without unique-existence derivation data,
if a Core proof cannot be represented by an inspectable derivation tree, or if
a translation theorem silently excludes function or description cases.
