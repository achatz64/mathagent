# Overview 

The source file is typically a latex file. It is the single source of truth.  

The canonical acceptance target is a lean file `*.lean` in the `lean` folder.  It must compile with `lake build {target}` without
`sorry`, `admit`, `gap`, or any other incomplete-proof token. The only target-level assumptions are the [documented  dependencies](#axiom-handling), no result proved in the source is axiomatized.

Typically an audit will be performed to verify completeness and faithfulness of the target file. 

# Source inventory 

In the lean target search for `INVENTORY-SCRIPT`to find a path to a script to be that reproducibly extracts source environments, labels, and
section context while excluding exercises and solutions. Use it to prevent selective coverage.

# Lean search 

Semantic search isn't supported; the checked-out Mathlib source is present.
Search it with ripgrep (`rg 'orderOf_dvd_card|finrank_compositum' Mathlib`),
inspect the declaration in context, then check a paper-facing wrapper. This
is faster and cognitively cheaper than treating semantic search as the
default for every result.

# Translation strategy

## Strong library theorem, faithful paper wrapper

The wrapper records the source's intended interface while delegating proof to the
more general Mathlib theorem. This style minimizes custom proof terms while keeping the final API audible.

## Bundle the mathematical object, not its prose encoding

Prefer Lean's bundled objects (`OrderIso`, `MulEquiv`, `Subgroup`) over
unbundled encodings (two direction-proofs, a homomorphism-plus-properties
tuple, a carrier set with repeated closure lemmas). The bundle's type exposes
exactly which structure is preserved and keeps proof construction small.

## Missing APIs and source proofs

Search Mathlib thoroughly, including neighboring declarations and stronger or
differently bundled formulations. If no faithful construction exists,
implement it from the source semantics. If no theorem exists, formalize the
source proof using prior faithful translations and lower-level Mathlib APIs,
closing routine omitted steps yourself. Search failure, proof plumbing, and
implementation cost are not blockers.

Again, the lesson is that absence of a statement-compatible Mathlib theorem is
not itself a blocker: use lower-level APIs to formalize the source proof, while
keeping every source clause visible in the resulting declaration types.

Flag an `AUDIT-GAP` only for an essential defect such as a false statement,
missing hypothesis, circular argument, or semantics that cannot be recovered.

## Bridging (shape-mismatch transport)

Bridging is proof work whose content is exhausted by type shapes — transport
between presentations of what mathematics treats as one object. Mismatches are
surfaced by workers and paid once: the worker reports the two presentations and
the exact transported statement; main decides the general statement, its shape,
and its home, and sends the signature back to the worker's session. Workers
never declare bridge lemmas or self-approve tags.

- A bridge is tagged only by main, and only when its statement is mathematically
  vacuous and its proof forced. Distinct transported pairs are distinct
  mismatches; the same transport asked twice — including a generalized
  re-statement of it — is not. When a literal-derivation demand is rejected,
  record the rebuttal beside the audit marker.
- Prefer hypotheses over instance synthesis: state the needed equation as an
  explicit hypothesis; instance paths that resolve only for particular type
  terms do not generalize.
- Home a bridge where its consumers can reach it by file scope; re-home when a
  consumer site predates the bridge.
- The per-consumer call-site cost of a bridge (named arguments, hypothesis
  arguments, coercion shims, instance shells) is ledger design debt, not an
  audit gap; reduce it by bridge design when it dominates the per-chapter cost.

An external theorem not proved in the source may instead be a named dependency
axiom when its exact assumptions and conclusion are recoverable from the text,
an unambiguous well-known formulation, or an identifiable reference. Document
the provenance, state only what is needed, and keep it visible to
`#print axioms`; vague dependencies remain gaps, and source-proved results must
not be axiomatized. See [here](#axiom-handling).

# Linter issues

Additionally to verifying build, address [Lean linter issues](LEAN_LINTER.md). `@[nolint …]` use is only allowed in cases of false positives: you need to add detailed documentation and explicitly mention that it is a "false positive".   

# Conventions
Stable TeX labels or other source identifiers (lines, etc.) occur in source
comments, while Lean names follow Mathlib conventions.  

# Axiom handling
An axiom is permitted only for a mathematical
dependency cited but not proved by the source; every such axiom must be named,
documented, and visible to `#print axioms`. For example
```lean
/-- GT `ns04`.  This is deliberately an audible axiom: Feit--Thompson is an
external dependency cited without proof in the source, and is absent from
Mathlib.   
-/
axiom feitThompson : feitThompsonStatement
``` 

# Mistakes in the source argument

Subagents and the main agent must flag mistakes in the source argument (wrong
proof steps, false claims, gaps the source glosses over). A flagged mistake is
recorded in the docstring of the affected Lean declaration (or, if no
declaration exists yet, in the ledger note): what the source asserts, why it is
wrong. If an alternative proof of the source's claim is found, its route is
outlined in the same docstring and the formalization proceeds with it (the
statement stays faithful; only the proof route differs — record that the route
differs). If no alternative proof is found, give up on the item: record the
mistake and the give-up in the ledger, and do not silently repair or restate
the source. Never paper over a source mistake by proving a different claim
under the source's label.

# Faithfulness and audit gaps

- Source claims should be visible in Lean types, not only comments or proofs.
- Split compound claims when one bundled type does not expose their existence,
  uniqueness, converses, equations, or corollaries.
- Generic library results may be used internally, but source-facing wrappers
  should preserve relevant assumptions and conventions.

Audits will flag violations with `AUDIT-GAP` in the lean target (easy to search with `rg -n 'AUDIT-GAP' lean/{target}.lean`.). 

A main formalization agent may close an `AUDIT-GAP` or leave it with a blocker explanation in target, but must not reclassify it as `AUDIT-DEFERRED`; deferral is a separate scope decision.

After closing or refuting a batch of `AUDIT-GAP` markers, run the next audit pass over the remediation delta; the audit loop terminates only when a pass reports no actionable findings (the auditor has the last word).

# Commands to avoid context bloat

1. Read only the relevant regions of the source. Again: NEVER READ THE ENTIRE FILES! THEY CAN BE HUGE.

# Obligation to Mathlib and other external libraries

When development exposes a reusable strengthening of a library theorem or a
missing general-purpose interface, record it in the output Lean file under
`Improvements for Mathlib` or `Improvements for {external library}` in general. Each entry should identify:

1. the existing external library declaration and source file;
2. the proposed stronger statement or API;
3. a plausible proof route, distinguishing checked project code from a sketch;
4. relevant project declarations or source references.

Do not treat these upstream suggestions as source-faithfulness gaps, and do not
overstate a speculative proof as checked. Project-specific wrappers do not need
an entry merely because they are absent from the external library.

## Criteria for obligation candidates

Before recording an entry under `Improvements for Mathlib` (or another external
library), apply two checks. Both must hold for the entry to be substantive.

- *Content check (not a wrapper).* The proposed upstream statement must be more
  than an existing library theorem plus a small structural wrapper — for example,
  adding a `k`-linear / `AlgEquiv` / `toAdditive` layer to a `RingEquiv`- or
  set-level result. If a library composition reproduces the target's declaration
  with the same axioms and a shorter proof, the entry is overstated: the library
  already covers it "up to the epsilon" of the wrapper, and the target should
  delegate rather than record an obligation.
- *Absence check.* Before concluding a gap, search the external libraries
  comprehensively for the concept (broad `rg` across the libraries, not only the
  obvious namespace), since bounded name-guessing repeatedly misses the route.
  A reliable negative result is a broad grep returning no candidate combined
  with REPL replay of the would-be wrapper from the target's actual import
  closure (not the all-`Mathlib` REPL root, which hides missing imports).

