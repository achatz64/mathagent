Read for audit agent. 

# Provenance audit

At the beginning of the target after the imports there must be a `# Provenance` section conform with this [standard](PROVENANCE.md).

# Coverage audit

Basic coverage test by using a script. Use search for `COVERAGE-SCRIPT` in lean target to find the path. 

# Compilation audit

Checks that the target builds with `lake build {target}` and the cononical file contains no incomplete-proof token (`sorry`, `admit`, etc.). 

Additionally, linter issues need to be flagged as `AUDIT-GAP` in the target and by specifying the issue. All `@[nolint ...]` use cases must be well-documented and clearly flag the application as `false positive` of the linter.

# Axioms audit

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

# Semantic audit

Check statement fidelity. Put an actionable `AUDIT-GAP` beside the partial declaration; reserve
  `AUDIT-DEFERRED` for intentional omissions in the final ledger.

- Source claims should be visible in Lean types, not only comments or proofs.
- Compound claims should be split when one bundled type does not expose their existence,
  uniqueness, converses, equations, or corollaries.
- Generic library results may be used internally, but source-facing wrappers
  should preserve relevant assumptions and conventions.
- A build checks Lean correctness; declaration types determine faithfulness.

# Documentation audit

Is the inline documentation satisfactory in terms of quantity and quality. Is the documentation spot on and helpful?  

# Obligation to external library audit

In the lean target there are comment sections on 
`Improvements for {external library}` (e.g. Mathlib). Each entry should identify:

1. the existing external library declaration and source file;
2. the proposed stronger statement or API;
3. a plausible proof route, distinguishing checked project code from a sketch;
4. relevant project declarations or source references.

Project-specific wrappers must not be included merely because they are absent from the external library.
