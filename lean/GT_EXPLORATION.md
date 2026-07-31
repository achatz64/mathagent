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
`sorry`, `admit`, `gap`, or accidental project axioms.  Stable TeX labels occur
in source comments, while Lean names follow Mathlib conventions.  Scratch
experiments are not subject to the canonical target's completeness condition.

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

### Cumulative import attempt

The first Lean REPL experiment requested a cumulative base containing:

- `Mathlib.GroupTheory.FreeGroup.NielsenSchreier`
- `Mathlib.GroupTheory.Index`
- `Mathlib.GroupTheory.OrderOfElement`
- `Mathlib.GroupTheory.QuotientGroup.Basic`
- `Mathlib.GroupTheory.SchurZassenhaus`

The request exceeded the MCP server's fixed 60-second request timeout.  A retry
against the same registered import base also timed out.  The host process tree
and `lean_repl_status` showed that the MCP server remained alive but its worker
had been stopped.  There was no stderr and no competing REPL process.

This behavior follows the server implementation: a timeout calls
`_abort_locked`, which terminates the worker.  The configured `--warm` option
warms only the empty import base because no `--warm-import` arguments are
present.  It does not make a later broad import set cheap.

### Consequence for a low-effort workflow

A single “convenient” broad REPL base is fragile under a fixed timeout.  The
better experiment design is:

- start with the narrowest module containing the candidate declaration;
- group several checks that share that module;
- add one missing module at a time;
- reserve a full project build for the integrated target.

There is a useful inversion here: broad imports reduce *prompt effort* but can
increase *tool failure cost*.  The best unit of batching is not “one chapter”;
it is “one import frontier.”

### Integrated build experiments

The REPL timeout made a project build the reliable integration oracle.  Import
choice mattered much more than proof size.  An early `import Mathlib` version
was still compiling after more than four minutes and was abandoned.  Replacing
it with declaration-owning modules produced the following observed sequence:

| Target state | Jobs | Result | Reported target time |
|---|---:|---|---:|
| first narrow-import prototype | 1887 | elaboration errors | about 99 s |
| corrected narrow prototype | 1887 | success | 23 s |
| expanded algebra/character target, cold frontier | 2423 | elaboration errors | 66 s |
| subsequent correction passes | 2423 | errors or success | 16–36 s |
| final semantic pass before the audit comments | 2423 | success | 28 s |

The expanded import frontier is substantially more expensive but remains
predictable.  More importantly, failed target builds returned all elaboration
errors together.  For this workload, a 30-second build poll plus continued
session polling had lower human effort than submitting dozens of isolated REPL
checks, even though a successful narrow REPL would have lower theoretical
latency.

One orchestration failure was also informative: losing track of yielded shell
session identifiers accidentally started redundant builds.  They were stopped
before continuing.  The robust driver treats the first command's session ID as
state and polls that exact session until it exits; it never launches a second
build merely because the first poll returned no output.  This is a general
agent-tool lesson: an empty poll result is not evidence that a process ended.

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

The final file contains 86 declarations in 766 lines.  Most proofs are a direct
application, instance synthesis, or a small adapter around a stronger library
object.  Several adapters replace a whole textbook proof:

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

The only custom algebraic proof of any size is the internal direct-product
adapter.  Even there, the mathematical step is isolated to the fact that
elements of disjoint normal subgroups commute; Mathlib supplies that lemma and
the complement bijection.

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
  "unmentioned_labels": []
}
```

This result is deliberately **not** called “142 proved theorems.”  It certifies
that no labeled result silently disappeared.  A label is either attached to a
checked declaration or appears in the explicit omission ledger at the end of
the target.  The ledger records why the first experiment did not create a
statement-compatible wrapper: implementation-specific word encodings,
paper-specific extension machinery, exact Coxeter results absent from the
current library interface, or substantial new theory beyond a low-effort
adapter.

This negative-space audit is more useful than a raw declaration count.  It
prevents two common failure modes:

1. silently ignoring hard results while reporting only famous successes;
2. manufacturing proposition constants and counting them as proved facts.

The cited Feit--Thompson result illustrates the second point.  It is represented
by `feitThompsonStatement : Prop`, because the book cites it without proving it
and Mathlib does not supply it.  The target does not claim an inhabitant and
does not add a project assumption.

### Coverage levels

The experiment naturally produced four useful levels:

| Level | Meaning | Typical artifact |
|---|---|---|
| construction reuse | Mathlib already owns the object | direct use of `FreeGroup`, `PresentedGroup`, `Sylow`, `FDRep` |
| checked wrapper | statement-compatible result is proved | `theorem` or structure-preserving `def` |
| proposition only | cited dependency is stated but not claimed | `feitThompsonStatement` |
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
The experiment used it only for Feit--Thompson and explicitly declined to turn
paper-proved missing results into unoccupied constants.  The omission ledger
is more honest for those results.

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

1. `lake build GT` succeeds from the `lean` project (2423 jobs in the final
   semantic build);
2. the canonical file contains none of the forbidden incomplete-proof tokens;
3. no project-level assumptions are introduced; the one unavailable cited
   result is an uninhabited proposition definition;
4. inventory counts regenerate from `tools/gt_inventory.py`;
5. all theorem-like labels are accounted for by `tools/gt_coverage.py`;
6. wrapper comments retain stable TeX labels while declarations use
   Mathlib-style names;
7. `git diff --check` reports no whitespace errors in the experiment files.

Reproduction commands from `lean/`:

```text
lake build GT
python3 tools/gt_inventory.py --summary ../test/GT/GT.tex
python3 tools/gt_coverage.py ../test/GT/GT.tex GT.lean
rg -n '\b(sorry|admit|axiom|gap)\b' GT.lean
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
5. A mechanical source inventory plus an explicit omission ledger is the
   simplest available defense against selective formalization while the
   repository has no provenance system.
6. The most honest completion metric is multi-valued: reused construction,
   checked wrapper, proposition-only dependency, or explicit omission.
