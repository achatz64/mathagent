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

An external theorem not proved in the source may instead be a named dependency
axiom when its exact assumptions and conclusion are recoverable from the text,
an unambiguous well-known formulation, or an identifiable reference. Document
the provenance, state only what is needed, and keep it visible to
`#print axioms`; vague dependencies remain gaps, and source-proved results must
not be axiomatized. See [here](#axiom-handling).

# Linter issues

Additionally to verifying build, address Lean linter issues.  

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

1. Read only the relevant regions of the source.

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
