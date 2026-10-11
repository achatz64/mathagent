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

**Search failure is NOT a blocker.** Search Mathlib thoroughly (neighboring
declarations, stronger or differently bundled formulations); if no
statement-compatible theorem exists, that is the normal case, not an
obstacle: formalize the source proof from lower-level Mathlib APIs and prior
faithful translations, closing routine omitted steps yourself, and keep every
source clause visible in the resulting declaration types. Proof plumbing and
implementation cost are not blockers either.

Flag an `AUDIT-GAP` only for an essential defect: a false statement, missing
hypothesis, circular argument, or semantics that cannot be recovered.

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

An axiom is permitted only for a mathematical dependency cited but not proved
by the source. Every such axiom must be named, documented (with provenance:
which source cite, why absent from Mathlib), and visible to `#print axioms`.
Source-proved results must never be axiomatized.

# Mistakes in the source argument

Flag mistakes in the source argument (wrong proof steps, false claims, glossed-
over gaps); record in the affected declaration's docstring — or in the ledger
note if no declaration exists yet — what the source asserts and why it is
wrong. If an alternative proof is found, outline its route in the same
docstring (statement stays faithful; record that the route differs). If none
is found, give up on the item: record the mistake and the give-up in the
ledger. Never silently repair the source or prove a different claim under its
label.

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
`Improvements for Mathlib` (or the corresponding section for another external
library). Each entry identifies the existing declaration (with source file),
the proposed stronger statement or API, a plausible proof route (marking what
is checked vs sketch), and relevant project/source references. These are not
source-faithfulness gaps; never overstate a sketch as checked. A
project-specific wrapper alone is not an obligation.

Both checks must hold for an entry to be substantive:

- *Content check (not a wrapper).* The statement must be more than an existing
  theorem plus a small structural wrapper (e.g. a `k`-linear / `AlgEquiv` /
  `toAdditive` layer on a `RingEquiv`- or set-level result). If a library
  composition reproduces the declaration with the same axioms and a shorter
  proof, delegate rather than record an obligation.
- *Absence check.* Search the external libraries comprehensively (broad `rg`
  across the libraries, not only the obvious namespace; bounded name-guessing
  misses routes), then REPL-replay the would-be wrapper from the target's
  actual import closure — not the all-`Mathlib` root, which hides missing
  imports.

