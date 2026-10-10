# Overview 

The source file is typically a latex file. It is the single source of truth.  

The canonical acceptance target is a lean file `*.lean` in the `lean` folder.  It must compile with `lake build {target}` without
`sorry`, `admit`, `gap`, or any other incomplete-proof token. The only target-level assumptions are the [documented  dependencies](#axiom-handling), no result proved in the source is axiomatized.

Typically an audit will be performed to verify completeness and faithfulness of the target file. 

# Source inventory 

In the lean target search for `INVENTORY-SCRIPT`to find a path to a script to be that reproducibly extracts source environments, labels, and
section context while excluding exercises and solutions. Use it to prevent selective coverage.

# Lean search 

Semantic search isn't supported currently. The checked-out Mathlib source is already present.  Ripgrep searches such as
```text
rg 'quotientKerEquivRange|card_mul_index|orderOf_dvd_card' Mathlib
```
return relevant declaration sites in well under a second.  

- It is excellent for theorem-title fragments, docstrings, namespaces, and
  already-guessed identifiers.
- It exposes neighboring declarations, often revealing the intended API
  better than isolated search hits.

The low-effort pipeline:

1. use the source inventory to obtain a mathematical signature;
2. guess one or two interface words and search local docstrings/source;
3. inspect the declaration in context;
4. check a paper-facing wrapper.

This is faster and cognitively cheaper than treating semantic search as the
default for every result.

# Translation strategy

## Strong library theorem, faithful paper wrapper

The wrapper records the source's intended interface while delegating proof to the
more general Mathlib theorem. This style minimizes custom proof terms while keeping the final API audible.

## Bundle the mathematical object, not its prose encoding

The source often describes a theorem as several sentences and a diagram.  Lean
usually already has a bundled object carrying all those laws:

- an `OrderIso` is better than separately proving both directions of subgroup
  correspondence and inclusion preservation;
- a `MulEquiv` is better than a tuple containing a homomorphism plus injectivity
  and surjectivity;
- a `Subgroup` construction is better than a carrier set plus repeated closure
  lemmas.

Choosing the right bundle is the most effective way to keep proof construction small.  It also makes statement fidelity easier to review: the bundle's
type exposes exactly which structure is preserved.

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

Bridging is proof work whose content is exhausted by the shapes of the things it
connects — work arising wherever Lean's type discipline distinguishes what
mathematics treats as one thing (two type-level presentations of one object, a
statement and the API signature it must fit, two ambient fields, an instance
mismatch). The audit-side definition and checks live in AUDIT.md ("Bridging
audit"); this section records the main agent's protocol, ratified 2026-10 after
the Chapter III / FiberProduct remediation cycles.

- **Mismatches are surfaced by workers, paid once by main.** A worker that must
  re-perform a transport an existing bridge already provides reports the shape
  mismatch instead of improvising glue; main decides the general statement, its
  shape, and its home, and sends the exact signature back to the worker. Workers
  never declare `BRIDGE` lemmas or self-approve tags (see SUBAGENTS.md).
- **Tag approval.** Every `BRIDGE` tag is main's decision. Tag a declaration
  only if its statement is mathematically vacuous and its proof forced. When
  rejecting a literal-derivation marker, record the rebuttal in a remediation
  note: four distinct restriction maps are four distinct pairs of presentations
  (a rebuttal); one transport asked twice is not.
- **One statement = one mismatch.** Do not cover two distinct mismatches with
  one statement, and do not pay one mismatch with two tags (audit check 3). A
  generalization paid by hypothesis instead of instance synthesis is still one
  mismatch.
- **Generalize away instance paths, not to abstraction for its own sake.**
  Lesson: a bridge stated for concrete target-local types failed to generalize
  to abstract siblings because target-local instance declarations do not
  synthesize for fresh variables (FT.map_map_sup failed with
  `Algebra ↥B ↥(E ⊔ L)` for the abstract `B`, which the concrete instantiation
  `B := L` only satisfied via target-local paths). Re-stating the bridge for
  arbitrary commutative rings with the needed equation as an explicit hypothesis
  (FT.map_map_comp: `rw [Polynomial.map_map, hcomp]`) removed the
  instance-synthesis dependency at call sites entirely. Prefer hypothesis-shaped
  statements whenever a bridge's proof relies on instance synthesis that only
  works for particular type terms.
- **Consumers precede use.** Home a bridge where its consumers can import it by
  file scope. The audit re-homes bridges when a consumer site predates the
  bridge (lesson: map_map_comp was born in the FiberProduct section while its
  consumers lived in earlier sections; audit re-home 033c21d moved it to
  FactoringPolynomials).
- **Consumer harness cost is a separate budget.** The bridging audit amortizes
  the transport cost: one mismatch, one declaration, one tag. The per-consumer
  call-site cost — named arguments, hypothesis arguments, coercion shims such as
  repeated `have hcoe … := Subtype.ext rfl`, letI instance shells — is design
  debt, tracked in the ledger as refactor candidates, not an audit gap and not a
  bridging decision. Do not flag consumer verbosity; reduce it by bridge design
  (hypothesis-shaped statements) when it becomes the dominant per-chapter cost.
- **Remediation discipline.** Close `AUDIT-GAP` markers in a flagged-only pass:
  exactly the flagged items, each disposition documented in a remediation note
  beside the marker (BRIDGE tag / rewire to consume an existing bridge /
  documented rebuttal), then build and commit. Do not remediate unflagged sites
  proactively. Flag-first keeps audit deltas small and lets the audit surface
  independent misses on its own: a deliberately untouched unflagged twin was
  caught by the audit's pattern scan while remediation paid only flagged work.
- **Audit interface.** Commit messages for the auditor carry rules and mode
  only — never findings, regions, line numbers, or expected results. Every
  remediation note names the FT label(s) touched; a new bridge names its
  consumer family in the docstring so the pattern scan can exempt declared
  consumers.

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

# Faithfulness and audit gaps

- Source claims should be visible in Lean types, not only comments or proofs.
- Split compound claims when one bundled type does not expose their existence,
  uniqueness, converses, equations, or corollaries.
- Generic library results may be used internally, but source-facing wrappers
  should preserve relevant assumptions and conventions.

Audits will flag violations with `AUDIT-GAP` in the lean target (easy to search with `rg -n 'AUDIT-GAP' lean/{target}.lean`.). 

A main formalization agent may close an `AUDIT-GAP` or leave it with a blocker explanation in target, but must not reclassify it as `AUDIT-DEFERRED`; deferral is a separate scope decision.

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

