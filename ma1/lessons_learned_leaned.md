# Lessons learned — Lean style & conventions

Distilled from building `test.lean` (Peano addition via unique choice). Rules first,
rationale and gotchas after.

## Naming

**Capitalization encodes which level an identifier lives at** (adopted from Mathlib).


| Case | Level | Means | Example |
|---|---|---|---|
| `UpperCamelCase` | `Prop` / `Type` / `… → Prop` | a **type or a statement** — includes Prop-valued *predicates* (a `def`/`structure` returning `Prop`) | `Peano`, `IsAddition`, `InductionHyp`, `IsSlice`, `ExistsUnique` |
| `lowerCamelCase` | data | a **function or value** (a `def` returning data) | `identity`, `addition`, `Construct.get` |
| `snake_case` | proof term | a **proof** (a term inhabiting a `Prop`) | `addition_existence`, `fun_unique`, `cond`, `spec`, `hcond` |


Rules:

1. **Case first, then decide whether the Prop even needs a name.** A predicate gets
   `UpperCamelCase` (`IsAddition f` reads as an assertion, not a noun). But a proof's
   *type* is already its statement, so don't give a Prop its own name unless it's used
   *as a value* — passed to a combinator, reused as a hypothesis, or read at a
   boundary. Otherwise inline it as the theorem's type (e.g. `theorem addition_existence
   : Construct.ExistsUnique IsAddition`, no separate `AdditionExistence` def).
   The rule applies at every level, including `let`-bound predicates inside a proof
   (`IsSlice`, `SliceExists`): capitalizing them tells the reader "this is a Prop" at a
   glance.
2. **`spec` is only for `Construct.get_spec`** — the property read back off a chosen
   element. Don't reuse it for arbitrary condition proofs.
3. **No `proof_` prefix on theorems.** The theorem name *is* the proof; name it for
   what it asserts (`addition_existence`, not `proof_addition_existence`).
4. Prefer descriptive `have` names that read like a proof sketch.

## Structure vs. `∧` (mandatory rule)

**If a `Prop` bundles ≥2 conditions and is *not* confined to a `let` inside a proof,
it MUST be a `structure` with named fields — never a nested `∧`.**

```lean
structure IsAddition (f : N → N → N) : Prop where
  zero_zero  : f zero zero = zero
  succ_left  : (n m : N) → f (next n) m = next (f n m)
  succ_right : (n m : N) → f n (next m) = next (f n m)
```

- Rationale: at a **boundary** (anything outside reads the fields) `h.succ_left n m`
  beats counting into `h.right.left n m`. `IsAddition` is what callers of
  `addition_spec` see, so its fields must be named.
- Anonymous constructor `⟨_, _, _⟩` still builds a structure and it drops into
  `Construct.ExistsUnique` unchanged (a structure is just a `X → Prop`).

**Exception:** a Prop defined in a `let` inside a proof, never accessed outside it,
may stay a bare `∧` (e.g. `IsSlice` — only `slice_addition_unique`, a few lines away,
touches its `.left`/`.right`). Structure ceremony has no payoff with no boundary to
cross.

Slogan: **structure at the interface, `∧` for throwaway internal conjunctions.**

## Classes — the way forward for structures with examples

We bundle data + laws in a `class`, not a fixed axiomatic
namespace. The class is the interface; each `instance` **discharges the laws from
its own construction** — so they become theorems downstream of `Nat`/ZFC/Peano, not
fresh axioms. A generic lemma written once then serves every instance, and
`extends` gives hierarchy reuse.

### Class field hygiene

Order and name the fields so the class reads top-to-bottom as "here is the data,
here are the laws it obeys":

1. **Data first, conditions second.** All the carriers/operations/constants
   (`op`, `unit`, `neg`), *then* all the laws (`op_assoc`, `op_comm`, `op_neg`).
   Never interleave.
2. **Each condition's name starts with the data it constrains**, so the field name
   points back at its operation: `op_assoc`, `op_comm`, `op_unit`, `op_neg` all lead
   with `op`. This makes `#print`-ing the class and dot-access self-documenting.
3. **Exception:** a law genuinely about no single operation keeps a descriptive name
   — e.g. `induction` in `Peano` ranges over an arbitrary predicate `β`, not any one
   operation, so there is no data name to lead with.

```lean
class AbGroup (G : Type) extends CommMonoid G where
  neg    : G → G                                  -- data
  op_neg : (a : G) → op a (neg a) = unit          -- law, named for `op`
```

## Unique choice: the `get` / `get_spec` pattern

`Construct.get`/`get_spec` are unique choice — the definite-description analogue of
`Classical.choose`/`choose_spec`, but **strictly weaker** (no Diaconescu → no LEM), so
they keep the development off `Classical.choice`.

- `get c` extracts the element; `get_spec c : p (get c)` proves it satisfies the
  predicate. That is how you "introduce the spec."
- `Construct.ExistsUnique p` = `∃ x, p x ∧ ∀ y, p y → y = x`. A proof is a triple
  `⟨witness, proof_of_condition, proof_of_uniqueness⟩`; the uniqueness slot has type
  `∀ y, p y → y = witness`.
- **Cross-instance facts route through the uniqueness lemma, not `get_spec`.**
  `get_spec` gives each instance's own recurrence for free; anything relating
  *different* instances (e.g. slice `n` to slice `next n`) must go through the
  "at most one solution" lemma (`slice_addition_unique`).


