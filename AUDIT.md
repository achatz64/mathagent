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

# Coding conventions audit

We follow the Mathlib conventions as outlined [here](https://leanprover-community.github.io/contribute/naming.html).

When choosing names, it is important to choose names that make sense and feel natural in the context of the [documentation string](#documentation-audit). For example, for a simple construction in combinatorics, which will later be used in the context of ring theory, a name like `elementaryPrimes` is not adequate, because the construction will have nothing to do with primes, only the application.  

# Documentation audit

Is the inline documentation satisfactory in terms of quantity and quality? 

Following criteria must be satisfied:
- All construction's and proof's documentation must explain the idea in textbook math terms. 
- Theorems, lemmas etc. must have a textbook math documentation of the statements and the ideas entering the proof. If no new idea enters in the proof (e.g. unpacking, repacking) then the documentation must declare it as trivial. 
- The documentation of a construction or a proof must not contain contend relating to other defs or proofs with the only exception of listing dependencies and where they enter. For example, it a thm A will be used by another thm B in the future, then the documentation of B may mention A, but A may not mention B. 
- State the nature of the construction, statement or proof in the surrounding contex. For examples: `technical lemma`, `main theorem of this section`, `auxiliary construction`, `key lemma`, `key construction`, etc. [TODO: enum to be specified]. 

# Bridging audit

Bridging is proof work whose content is exhausted by the shapes of the things it
connects — work arising wherever Lean's type discipline distinguishes what
mathematics treats as one thing (e.g. two type-level presentations of one object,
a statement and the API signature it must fit, two ambient fields, an instance
mismatch). Bridging cost must be paid once per shape mismatch and reused; the main
agent owns the bridging strategy and approves every `BRIDGE` tag.

A declaration may be tagged `BRIDGE` only if its statement is mathematically
vacuous (a paper would not state it) and its proof is forced — given the endpoints
and the ambient API, it admits no mathematical choice: no construction, estimate,
counting, own algebraic identity, or strategic case analysis. Mixed declarations
(transport plus authorial step) are content, not bridges; definitions are notation
(main's design), outside this audit.

Checks (in a full audit, checks 1 and 4 are performed by targeted search; the
file is never read end-to-end for this audit):

1. **Untagged bridges.** A declaration is a bridge candidate if its proof is
   dictated by the types involved — every step drawn from generic machinery
   (extensionality, congruence, coercion and instance lemmas, definitional
   equalities, transport between the presentations named in the statement), with
   no mathematical step of its own. Locate candidates by searching for such
   proofs, then judge each candidate only for: mathematically vacuous statement,
   forced proof, substantial code. A vacuous, forced, substantial candidate
   without a `BRIDGE` tag → `AUDIT-GAP` (missing `BRIDGE` tag). Rejections are
   per-declaration with a stated reason; a support lemma of a source-stated
   theorem is judged independently — it is never rejected by virtue of the
   chapter or theorem it supports.
2. A tagged declaration whose proof is not forced → `AUDIT-GAP` (impure bridge);
   remedy: split or untag as content.
3. Two `BRIDGE` tags covering the same shape mismatch → `AUDIT-GAP` (unpaid reuse).
4. **Pattern scan.** For each tagged bridge and each check-1 candidate, extract
   the terms in its statement and proof that name the two presentations it
   connects, and search the file for their inline re-performance; hits outside
   the declaration's own consumers → `AUDIT-GAP` (unpaid reuse). Names of generic
   tactics are not fingerprints; a verbatim proof fragment recurring across
   declarations is always one. Matching is up to binder renaming: a fragment
   (witness terms, transported statements, local `have` bodies) that recurs in
   another declaration with only bound-variable and local-hypothesis names changed
   is a fingerprint hit — verbatim text identity is not required. In particular,
   an untagged declaration that inlines the transport of a tagged bridge's
   statement terms under different binder names is unpaid reuse.
5. **Delta audit.** With the delta small and the existing bridges and strategies
   known from prior audits, identify minimality violations on read: new code that
   re-performs a transport an existing bridge provides, instead of calling it, is
   flagged; new shape mismatches are surfaced to the main agent rather than judged.

# Obligation to external library audit

In the lean target there are comment sections on 
`Improvements for {external library}` (e.g. Mathlib). Each entry should identify:

1. the existing external library declaration and source file;
2. the proposed stronger statement or API;
3. a plausible proof route, distinguishing checked project code from a sketch;
4. relevant project declarations or source references.

Project-specific wrappers must not be included merely because they are absent from the external library.

# Speed up with delta audits

If a full audit is not explicitly demanded then please find the last audit commit by an audit agent and perform a delta audit on new modifications. This is more efficient in audit ping pong between audit agent and main agent.

