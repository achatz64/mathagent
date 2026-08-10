# GT formalization exploration

## Objective and acceptance criterion

The source is `test/GT/GT.tex`, a 10,254-line group-theory text.  The current
scope excludes exercises, supplied solutions, the examination, raw
multiplication tables, and algorithms whose intended mathematical interface is
not yet clear.  Referenceable mathematical results are translated faithfully;
the Lean declaration may be more general when Mathlib already provides the
stronger result.  Existing constructions are normally reused directly rather
than hidden behind aliases.

The canonical acceptance target is `GT.lean`.  It must compile without
`sorry`, `admit`, or `gap`.  An axiom is permitted only for a mathematical
dependency cited but not proved by the source; every such axiom must be named,
documented, and visible to `#print axioms`.  Stable TeX labels occur in source
comments, while Lean names follow Mathlib conventions.  Scratch experiments
are not subject to the canonical target's completeness condition.

## Source inventory

`tools/gt_inventory.py` is a deliberately small, dependency-free source
inventory.  It tracks chapter/section context, environment kind, line range,
labels, and normalized text.  It excludes exercise and solution material by
default.  This is not a general LaTeX parser: it is a reproducible extraction
stage specialized to the environment discipline used by this document.

The first pass found 254 in-scope structured environments:

| Kind | Count |
|---|---:|
| definition | 6 |
| proposition | 48 |
| theorem | 38 |
| corollary | 25 |
| lemma | 25 |
| example | 45 |
| remark | 20 |
| plain | 34 |
| aside | 10 |
| summary | 3 |

There are 136 theorem-like environments.  By chapter:

| Chapter | Results |
|---|---:|
| Basic Definitions and Results | 32 |
| Free Groups and Presentations; Coxeter Groups | 9 |
| Automorphisms and Extensions | 6 |
| Groups Acting on Sets | 25 |
| The Sylow Theorems; Applications | 7 |
| Subnormal Series; Solvable and Nilpotent Groups | 19 |
| Representations of Finite Groups | 38 |

This inventory is useful even without a provenance system: it prevents an LLM
from unconsciously selecting only easy, famous theorems and calling the chapter
complete.  It also separates three different tasks that otherwise get mixed:

1. interpret the paper statement;
2. find the corresponding library interface;
3. elaborate a checked wrapper.

## Search experiments

### LeanExplore cold and warmed behavior

All LeanExplore calls used the attached MCP server, `limit: 10` or a stated
larger limit, and `rerank_top: 0`.  End-to-end warm-up measurements used a host
monotonic clock.

| Query | Outcome | End-to-end time |
|---|---|---:|
| `commutativity of addition` (cold) | 10 results | 149.649 s |
| `Nat.add_comm` | 10 results | 12.741 s |
| `continuity of a function on a compact set` | 10 results | 9.494 s |
| `prime number divisibility` | 10 results | 6.855 s |

The warmed median was 9.494 seconds; all three warmed calls exceeded the
five-second warm-query threshold.

A later group-theory batch used `search_summary`, `limit: 20`, and
`rerank_top: 0`:

| Query | End-to-end time | Useful behavior |
|---|---:|---|
| Cayley theorem, semantic phrasing | 49.674 s | Poor: the desired declaration was not near the front |
| Lagrange cardinality/index identity | 23.945 s | Good: `Subgroup.card_mul_index` appeared |
| element order divides finite group order | 13.558 s | Good: `orderOf_dvd_card` appeared |
| quotient by kernel equivalent to range | 19.780 s | Good: `QuotientGroup.quotientKerEquivRange` appeared |

The important distinction was not “natural language versus names,” but
**interface-shaped query versus textbook-title query**.  Phrases containing the
actual output objects—`card`, `index`, `kernel`, `range`, `quotient`—worked much
better than asking for a famous theorem by title.  With reranking disabled, a
query such as “Cayley theorem” has too many semantically adjacent permutation
declarations.  Once a candidate namespace is known, lexical declaration-name
matching is much more dependable.

### Local source lookup as a complementary index

The checked-out Mathlib source is already present.  Ripgrep searches such as

```text
rg 'quotientKerEquivRange|card_mul_index|orderOf_dvd_card' Mathlib
```

returned relevant declaration sites in well under a second.  This method has
different strengths from LeanExplore:

- It is excellent for theorem-title fragments, docstrings, namespaces, and
  already-guessed identifiers.
- It exposes neighboring declarations, often revealing the intended API
  better than isolated search hits.
- It cannot bridge a large vocabulary gap.  LeanExplore remains valuable when
  the paper and Mathlib conceptualize the result differently.

The low-effort pipeline is therefore asymmetric:

1. use the source inventory to obtain a mathematical signature;
2. guess one or two interface words and search local docstrings/source;
3. use LeanExplore only when the vocabulary bridge is genuinely needed;
4. inspect the declaration in context;
5. check a paper-facing wrapper.

This is faster and cognitively cheaper than treating semantic search as the
default for every result.

## Lean execution experiments

## Translation strategy

### Strong library theorem, faithful paper wrapper

The wrapper records the book's intended interface while delegating proof to the
more general Mathlib theorem.  Examples include:

- Lagrange via `Subgroup.card_mul_index` in `Nat.card` form, which also handles
  infinite groups uniformly;
- element order divisibility via `orderOf_dvd_natCard`;
- first and second isomorphism theorems as explicit `MulEquiv` definitions;
- subgroup correspondence as an `OrderIso`;
- Nielsen--Schreier through Mathlib's `IsFreeGroup` instance;
- Schur--Zassenhaus through the complement API;
- Maschke through semisimplicity of the group algebra.

This style minimizes custom proof terms while keeping the final API readable.

### Bundle the mathematical object, not its prose encoding

The paper often describes a theorem as several sentences and a diagram.  Lean
usually already has a bundled object carrying all those laws:

- an `OrderIso` is better than separately proving both directions of subgroup
  correspondence and inclusion preservation;
- a `MulEquiv` is better than a tuple containing a homomorphism plus injectivity
  and surjectivity;
- a `Subgroup` construction is better than a carrier set plus repeated closure
  lemmas.

Choosing the right bundle is the most effective way to keep proof construction
near zero.  It also makes statement fidelity easier to review: the bundle's
type exposes exactly which structure is preserved.

### Proof compression by interface selection

After the semantic-audit correction pass and its follow-up retrieval batch,
the file contains 144 top-level declaration commands in 1,839 lines. Most
proofs remain a direct application,
instance synthesis, or a small adapter around a stronger library object, but
the audit demonstrated that wrapper count is not a useful proxy for statement
fidelity.  Several adapters replace a whole textbook proof:

- a multiplication bijection plus normality becomes an internal direct-product
  `MulEquiv`;
- finite abelian structure is exposed as products of `ZMod` factors;
- the orbit partition is an equivalence to a dependent sum, from which the
  class formula is obtained by cardinality;
- the five-way finite nilpotency `List.TFAE` simultaneously covers the
  normalizer, maximal-subgroup, Sylow-normality, and direct-product views;
- semisimplicity is expressed both by complemented submodules and by a direct
  sum of simple submodules;
- Wedderburn--Artin is represented by algebra equivalences rather than prose
  about matrix coordinates;
- the character formulas use Mathlib's `FDRep` categorical hom-space directly.

The correction pass added three deliberately non-wrapper proofs.  The
prime-square classification constructs a `ZMod p` vector-space structure in
the noncyclic case and recovers dimension two from cardinality.  The specified
simple-submodule complement theorem follows the book's maximal-subfamily
argument via `zorn_subset`.  The class-function development factors characters
through `ConjClasses` and derives linear independence from the character
pairing.  These are useful counterexamples to the first-pass assumption that
all important results would be available as direct Mathlib wrappers.

## Semantic-audit correction pass

### Semantic faithfulness

- Source claims should be visible in Lean types, not only comments or proofs.
- Split compound claims when one bundled type does not expose their existence,
  uniqueness, converses, equations, or corollaries.
- Generic library results may be used internally, but source-facing wrappers
  should preserve relevant assumptions and conventions.
- Put an actionable `AUDIT-GAP` beside the partial declaration; reserve
  `AUDIT-DEFERRED` for intentional omissions in the final ledger.
- A build checks Lean correctness; declaration types determine faithfulness.

Developers can locate local work with `rg -n 'AUDIT-GAP' lean/GT.lean`.

The first coverage pass was syntactic: it established that every source label
occurred somewhere in the target.  A subsequent independent audit compared
the proposition under each label with the Lean type.  It found a systematic
failure mode: a true, convenient Mathlib consequence was sometimes tagged with
a compound TeX label even though essential clauses were absent.  No proof was
false, but label occurrence had been mistaken for statement coverage.

The repair pass therefore checked each compound result clause by clause:
existence, equations, uniqueness, preserved structure, hypotheses, and
corollaries. A source hook was kept on a declaration only when its type exposed
the relevant obligation.
This produced, among others:

- a list-product characterization of generated subgroups, not only leastness;
- the finite Cayley embedding into permutations of `Fin n`;
- coset determination and equal-or-disjoint lemmas;
- the normality of products and the explicit conjugate-set description of
  normal generation;
- an `∃!` quotient universal property with the commuting equation;
- arbitrary-surjection correspondence, index preservation, normality, and the
  induced quotient isomorphism;
- both directions of the commuting and normal internal-product criteria;
- a genuinely equivariant transitive-action equivalence;
- cardinal-valued orbit--stabilizer, avoiding `Nat.card`'s collapse on
  infinite types;
- arbitrary-action kernel maximality, the finite orbit-sum formula, the block
  criterion, and both strict block-stabilizer inclusions;
- uniqueness of disjoint cycle decompositions;
- classification of prime-square groups as `C_(p²)` or `C_p × C_p`;
- existence and uniqueness in module Jordan--Hölder;
- the specified-family version of the semisimple complement theorem and the
  missing sums clause;
- the exact simple/isotypic/unique-simple-type equivalence;
- the exact algebraically closed division-algebra theorem and the actual group
  algebra specialization;
- class functions, character linear independence, and a basis constructor for
  a complete enumeration of simple representations.

The follow-up batch then tested the report's proposed hybrid pipeline on labels
which the first pass had left only in the omission ledger. Semantic retrieval
located exact or nearly exact APIs for the cyclicity criterion, the
element-order characterization of `p`-groups, normal subgroups of symmetric
groups, Sylow-normalizer control, and Sylow subgroups of subgroups. Narrow REPL
adapters turned these into checked formulations of `it20a`, `ga13c`, `ga32`,
`st8`, and `st11t`. A second Sylow pass established `st10` (the product of the
Sylow subgroups when each is unique) and the full overgroup statement `ns18`.
The same batch added `r41` through trace additivity and obtained `r20` and
`r22` from the isotypic-module API.

The remaining `p`-group existence theorem `ga15` was not a wrapper at all.  A
short quotient induction nevertheless fit the available interfaces: after a
normal subgroup of order `p^m` is constructed, its properness makes the
quotient nontrivial; the quotient centre contains an element of order `p` by
Cauchy's theorem; its cyclic subgroup is central and hence normal; and the
preimage-cardinality theorem gives a normal subgroup of order `p^(m+1)`.  The
only awkward adapter was an explicit equivalence between the subtype of a
subgroup `comap` and the subtype of a set-theoretic preimage.  This is a useful
example of a paper proof becoming inexpensive once library results cover its
mathematical steps, even though no theorem with the final signature exists.
Source-adjacent inspection also exposed `ns15` almost verbatim as Mathlib's
kernel-in-the-centre bound on nilpotency class; the quotient projection reduces
the book's corollary to a two-line adapter.

The character-sum results `it24` and `it25` illustrate a more innovative
interface choice. Unit-valued characters are kept bundled as monoid
homomorphisms; orthogonality is reduced to Mathlib's theorem that a nontrivial
finite-group homomorphism into an integral domain has zero sum. The dual sum is
stated with `finsum`, avoiding an arbitrary `Fintype` choice in the public
signature, and the proof temporarily installs the finite dual supplied by the
roots-of-unity hypothesis. This is both closer to the mathematical indexing
and more robust as a reusable API.

Two high-cost semantic gaps remain explicit rather than hidden. Mathlib has a
canonical isomorphism-invariant `CommGroup.freeRank`, which is enough to expose
the right invariant for the rank clause of `it21`, but it does not currently
provide uniqueness of the invariant-factor or elementary-divisor lists. In
representation theory, character orthogonality and the final basis-from-cardinal
linear algebra are checked, but the enumeration theorem `r32(a)` is still
needed to instantiate the basis with a complete set of simple representations.
These are theorem-development tasks, not wrapper-discovery tasks.

### Lean REPL versus integrated builds

The correction pass refined the execution strategy.  Compact but typeclass-
sensitive statements were prototyped in `lean-repl`; this was particularly
effective for the prime-square classification.  Four local iterations exposed
two issues cheaply: `Mathlib.Algebra.Field.ZMod` was a required narrow import,
and inferred module instances had to be named explicitly to avoid a scalar-
structure diamond.  The successful local check took about four seconds after
the import base was warm.

The Zorn proof for the specified-family complement exceeded the REPL's fixed
60-second request limit.  Moving it to the integrated target was more
effective: each build returned concrete lattice and set-rewrite errors, and
the final proof compiled without any gap.  The practical routing rule is now:

1. REPL for statements small enough to elaborate well inside the timeout;
2. project build for long tactic terms, Zorn arguments, or proofs that exercise
   a large cumulative environment;
3. never retry a timed-out large REPL term unchanged.

A useful general REPL workflow for locating an existing action is: search the
Mathlib source for the mathematical operation and its likely carrier type;
inspect nearby declarations and scoped-instance attributes; then use small
`#check`/`#synth` probes in a minimal example, trying the likely acting group
(and quotient or opposite variants) explicitly.  For `ga08` this distinguished
the available `ConjAct G` action from the initially assumed direct `G` action,
and exposed the accompanying stabilizer lemma before any custom definitions
were attempted.

### Axiom audit

Feit--Thompson (`ns04`) is cited by the text but not proved there and is absent
from Mathlib.  Merely defining its proposition did not establish the cited
result.  The corrected target therefore declares one explicit axiom,
`feitThompson : feitThompsonStatement`.  This is intentional and audible.  No
result proved in the source is discharged by an axiom.

### Split compound claims only at reusable boundaries

Numbered prose parts are not automatically separate Lean theorems.  They are
split when Mathlib exposes independent reusable interfaces, and kept bundled
when one equivalence or order isomorphism already packages the result.  This
avoids label-driven declaration design while still permitting coverage audits.

## Process observations

The host-visible process inspection found exactly one configured LeanExplore
launcher:

```text
lean-explore mcp serve --backend local
```

and its expected `python -m lean_explore.mcp.server --backend local` child.  No
competing local-backend launcher was present.  Slow search latency therefore
cannot be attributed to duplicate servers in this session.

## Coverage as executable negative space

The source inventory found 136 theorem-like environments carrying 142 distinct
labels (some environments also label displayed equations).  `tools/gt_coverage.py`
intersects those source labels with stable labels in comments in `GT.lean`.
Its final output is:

```json
{
  "theorem_like_environments": 136,
  "source_labels": 142,
  "labels_mentioned_in_target": 142,
  "unmentioned_labels": [],
  "all_included_environments": 254,
  "all_source_labels": 271,
  "all_labels_mentioned_in_target": 142,
  "all_unmentioned_labels": ["... 129 labels ..."]
}
```

This result is deliberately **not** called “142 proved theorems.”  It only
certifies coverage of labels in theorem-like environments.  A broader audit
found 271 labels across all 254 included environments: only the same 142 are
mentioned in the target, leaving 129 labels in definitions, examples, plain
prose, remarks, summaries, and asides unaccounted for.  Some are merely
constructions, examples, or historical notes, but many contain referenceable
mathematical claims.  They must be classified explicitly rather than silently
excluded by the theorem-like filter.

For theorem-like environments, a label is either attached to a checked
declaration or appears in the explicit omission ledger at the end of the
target.  The ledger records why the first experiment did not create a
statement-compatible wrapper: implementation-specific word encodings,
paper-specific extension machinery, exact Coxeter results absent from the
current library interface, or substantial new theory beyond a low-effort
adapter.

This negative-space audit is useful, but the semantic and all-environment
audits proved that it is only a first-line guard.  It prevents two common
failure modes:

1. silently ignoring hard results while reporting only famous successes;
2. manufacturing proposition constants and counting them as proved facts.

It does not prevent a third failure mode: attaching a label to a proper
consequence.  The clause matrix is required for that.  The cited
Feit--Thompson result also showed that an uninhabited proposition definition is
not evidence of a theorem; the corrected target uses the explicit, permitted
axiom described above.

### Coverage levels

The experiment naturally produced four useful levels:

| Level | Meaning | Typical artifact |
|---|---|---|
| construction reuse | Mathlib already owns the object | direct use of `FreeGroup`, `PresentedGroup`, `Sylow`, `FDRep` |
| checked wrapper | statement-compatible result is proved | `theorem` or structure-preserving `def` |
| explicit dependency axiom | cited dependency is stated and visibly assumed | `feitThompson` |
| explicit omission | no low-effort faithful interface was found | stable label in the omission ledger |

A future provenance system should store this level, not a single Boolean
“covered” field.  Conflating statement transcription, proof occupancy, and
construction reuse would make the audit misleading.

## Pipeline variants and their measured tradeoffs

### Variant A: semantic search first

This required the fewest identifier guesses but had the worst latency and the
largest irrelevant result payload.  It is appropriate only when the vocabulary
gap is real.

### Variant B: lexical source adjacency first

This was the winning default.  Search for two interface nouns, inspect the
surrounding 20–40 lines, then copy the exact generalized signature.  Neighboring
declarations frequently exposed an entire theorem family: Sylow conjugacy,
congruence, divisibility, normality, and Frattini's argument were discovered in
one local region.

### Variant C: declaration-cluster batching

Wrappers were written in clusters sharing imports and then checked by one
integrated build.  This increased the number of errors per build but reduced
interactive overhead.  It worked especially well for semisimple modules and
characters, whose statements share elaborate typeclass contexts.

### Variant D: statement-first placeholders

This is useful for cited dependencies, but dangerous as a completion metric.
The experiment uses it only for Feit--Thompson and does not turn paper-proved
results into axioms or unoccupied constants.  A proved partial interface and an
explicit omission are both preferable to a mislabeled theorem.

### Recommended hybrid

1. mechanically inventory labels and mathematical signatures;
2. classify constructions versus results before searching;
3. use local source adjacency for known vocabulary;
4. use LeanExplore only to bridge vocabulary;
5. batch by import frontier and declaration family;
6. integrate with a project build;
7. run the forbidden-token and label-negative-space audits;
8. report proved, proposition-only, reused, and omitted statuses separately.

## Reproducibility checks

The final audit includes all of the following:

1. `lake build GT` succeeds from the `lean` project (2424 jobs after the added
   `ZMod` field frontier);
2. the canonical file contains none of the forbidden incomplete-proof tokens;
3. the sole project-level assumption is the documented Feit--Thompson
   dependency; no paper-proved result is axiomatized;
4. inventory counts regenerate from `tools/gt_inventory.py`;
5. all theorem-like labels are accounted for by `tools/gt_coverage.py`, while
   its all-environment fields expose the 129 labels still requiring classification;
6. wrapper comments retain stable TeX labels while declarations use
   Mathlib-style names;
7. `git diff --check` reports no whitespace errors in the experiment files.

Reproduction commands from `lean/`:

```text
lake build GT
python3 tools/gt_inventory.py --summary ../test/GT/GT.tex
python3 tools/gt_coverage.py ../test/GT/GT.tex GT.lean
rg -n '\b(sorry|admit|gap)\b' GT.lean
rg -n '^axiom ' GT.lean
```

## Current conclusions

1. Semantic retrieval is most useful as a vocabulary bridge, not as the default
   declaration lookup mechanism.
2. Local source search plus neighboring-source inspection currently offers the
   best effort-to-information ratio.
3. Bundled Mathlib equivalences and order isomorphisms collapse multi-paragraph
   textbook proofs into auditable declarations with almost no custom proof.
4. Lean REPL import latency must be treated as a resource with a hard failure
   boundary; module-frontier batching is safer than chapter-frontier batching.
5. A mechanical inventory prevents silent disappearance only when every
   relevant environment kind is included; semantic statement fidelity still
   requires a clause-level audit, and label coverage alone is not evidence of
   formalization.
6. The most honest completion metric is multi-valued: reused construction,
   checked wrapper, explicit dependency axiom, proved partial interface, or
   explicit omission.
7. When a direct wrapper is unavailable, targeted mathematical development can
   still be low effort if the proof is routed through the right abstraction:
   finite-field dimension for `ga16`, lattice maximality for `r8`, and linear
   functionals for character independence.
