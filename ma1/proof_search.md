# Proof Search: Testing Core as a Search Language

## Position in the roadmap

This is the next program after **M3**, ahead of M4.  It is intentionally
independent of generated-vs-handwritten repository integration: M4 will give a
larger real-file corpus later, but it is not a prerequisite for testing whether
Core is a useful proof-search representation at all.

Required inputs:

* **M1:** a live, finite beta-infrastructure basis, rather than beta-cleaning
  axioms hidden in a mathematical development;
* **M2:** a mechanical correspondence from every supported syntactic/semantic
  bridge to checked Core evidence;
* **M3:** contextual HOL proof lifting, including the quantifier and structural
  cases, so that a search action can be compiled to a Core theorem.

M4 is a later consumer: its generated contextual-HOL fragments should become a
real-mathematics benchmark suite for the methods below.

## Question

Core is not justified as a search language merely because its grammar has
finitely many constructors.  With a fixed finite signature, ordinary typed
lambda terms, Lean terms, and Core terms all have that property, while their
sets of terms remain infinite.

The question to test is instead:

> For a useful fragment of contextual HOL, can Core support a *canonical,
> analytic, goal-directed* search procedure whose redundant states are
> controllably identified and whose actions have bounded, indexed choices?

"Analytic" has a concrete meaning here: the formula and type material in a
search state must come from a finite closure of the input goal, assumptions,
and imported rule library, except at explicitly isolated quantifier witness
steps.  Raw enumeration of growing Core proof terms is not analytic and is not
the proposed engine.

Certification is a non-negotiable output condition, but not the feature under
test.  The feature under test is the size and structure of the search state
space.

## Search boundary

The first engine, `CoreSearch0`, has a deliberately frozen boundary:

* Input is a checked contextual-HOL sequent `Gamma | Delta |- phi` together
  with a finite, declared import library.
* Search states are contextual goals plus unresolved subgoals and metavariable
  constraints.  They are **not** partially built arbitrary Core terms.
* A state may use only the fixed logic/infra basis and explicitly imported math
  theorems.  It may not create a new `axiom`, `def`, or derived theorem during
  search.
* The output is a derivation in a search calculus, replayed initially as a
  deep CoreThm derivation with its named live-Core dependencies. M3 proves
  that certificate boundary; it does not yet emit surface .cor proof terms.
  A later end-to-end emission gate can add that interoperability layer without
  changing the search calculus or making M4 a prerequisite.

The initial fragment is propositional contextual HOL plus the already-lifted
structural representation.  Quantifier witnesses are introduced only in the
later witness milestone.

## Certified normal forms

"Normalization" is split into four different operations.  They must not be
merged into an uncheckable simplifier.

| Name | Object normalized | Basis | Required evidence |
|---|---|---|---|
| N0 | contextual source AST: binder order, context product, implication chain, variable names | contextual syntax and renderer | syntactic equality |
| N1 | transparent `def`/`abbrev` unfolding permitted by Core | Core checker | checker definitional equality |
| N2 | closed `PC` propositions and exposed sequent closures | M1 beta basis, M2 Core correspondence, M3 context transport | emitted Core proof of `iff P P'` |
| N3 | search state: sorted/subsumed assumptions, focused goal shape, solved-goal removal | search-calculus theorems | derivation-preserving map between states |

N2 is deliberately restricted.  Core has no equality at arbitrary `Type`, so
it is unsound as a design claim to rewrite arbitrary maps merely because they
denote the same map in the intended model.  A N2 rewrite is permitted only when
the finite live basis supplies the required `PC` observation and M2 can name or
emit its evidence.

Each normalizer must satisfy the following, for its declared domain:

```text
normalize S = S'  =>  SearchDerivable S <-> SearchDerivable S'
normalize (normalize S) = normalize S
```

For N2 the first line is obtained by Core proofs in both directions.  The
implementation must record the rewrite trace; replaying it must reconstruct
the Core certificate.  The first prototype uses an oriented, terminating rule
set with a syntactic decrease measure.  An e-graph is explicitly postponed:
it can be considered only if every e-class edge carries a replayable Core
certificate and its congruence closure is proved valid for the chosen domain.

## Milestones

### PS1 — Search syntax and certified normalization

**Goal.** Define CoreSearch0 states, a finite rule-library interface,
matching/indexing, and N0--N3.

**Initial implementation.** Search.lean now fixes the pre-normalization
boundary: a propositional-fragment test, finite list formula closure, and
finite conclusion-directed logical candidates. Its typed Step relation gives
backward transitions for hyp, implication, conjunction, disjunction, and iff;
step_sound replays every such transition into the M3 contextual Proves calculus.
step_core_replay then packages it as conditional deep CoreThm evidence under
the existing M3 lifting certificates.

**First N2 slice.** N2Rule fixes six live reindexing schemas: unary,
and, or, implication, iff, and negation. N2Edge records the selected basis
name and its exact CoreThm certificate; N2Path now also carries checked
connective-congruence traces. The executable n2RootStep? matcher recognizes precisely those six
left-hand sides and returns only the displayed forward orientation. n2Normalize uses a
structural size budget; its output has a replayable Core certificate, satisfies
the declared binder-opaque normal-form test, and is syntactically idempotent.
Thus this N2 domain meets the stated normalizer laws. Quantifier-headed terms
remain opaque: binder movement is the separate Beck-Chevalley gate for a later
N2 extension.

**Boundary finding.** Negation is hypothesis-only for now. The M3 calculus has
no falsity-forming rule from which a sound not-introduction action could be
compiled; PS2 must give a separate justified classical focused treatment.

**Methods.**

* Reuse M3's typed contextual syntax rather than parse `.cor` text during
  search.
* Index imported rules by normalized conclusion head connective and by typed
  relation/constant head.  Candidate retrieval is then a finite lookup, not a
  scan of all declarations.
* Use first-order pattern matching over the reified contextual AST.  Higher
  order matching/unification is outside PS1; rules that would require it are
  rejected from `CoreSearch0` and counted as a boundary failure, not hidden by
  a heuristic.
* Implement N2 as a list of named, oriented rewrites.  A rewrite returns both
  the next state and the M2 reference/proof term used to justify it.

**Theorems.**

```text
finiteCandidates: normalized state S -> List (Action S)
normalizationSound: normalize S = S' ->
  (SearchDerivable S <-> SearchDerivable S')
normalizationIdempotent: normalize (normalize S) = normalize S
actionCoreThmSound: Action S S' -> CoreThm (close S) follows from close S'
```

**Exit condition.** Every state transition and every rewrite is replayable as
live Core evidence; candidate selection is finite and typed; no rewrite is
justified only by the informal intended model.

**Falsifier / pivot.** If useful normal forms require arbitrary-map equality,
an unbounded beta-rule family, or higher-order matching before even the
propositional fragment runs, Core's present representation is not suitable as
the search state.  Retain it as a certificate language and move search up to
the contextual syntax.

### PS2 — Analytic propositional search

**Goal.** Replace the Hilbert-shaped propositional proof search implicit in
M3 with a focused sequent/search calculus.

M3's Hilbert rules remain the lifting target.  They are not assumed to be good
search moves: backwards use of K/S-style schemas creates arbitrary intermediate
formulas.  PS2 adds a separate, goal-directed calculus and compiles its proof
to the M3 calculus/Core.

**Methods.**

* Define invertible decomposition rules for implication, conjunction,
  disjunction, negation, and iff; use a focus discipline for non-invertible
  choices.
* Keep the current contextual `Gamma | Delta |- phi` shape.  Assumptions are
  represented by their canonical implication chain only at Core-emission time,
  not used as the search data structure.
* Memoize normalized states.  A state key contains the normalized context,
  multiset/set discipline for assumptions (as justified by the calculus), and
  focused goal; it never contains its proof history.
* Prove the conversion to/from the M3 propositional fragment before using
  tactics or cost heuristics.  Heuristics may choose an action order but may
  not change the calculus.

**Theorems.**

```text
focusedSound: Focused G -> Proves G
focusedComplete: ProvesProp G -> Focused G
subformula: every formula in a Focused derivation of G is in Closure(G)
finiteStateProp: quotienting propositional states by N0--N3 yields a finite set
```

`Closure(G)` is explicitly the finite set of subformulas of the goal and
assumptions, together with the finite declared rule schemata instantiated from
those subformulas.  The final theorem gives a terminating decision procedure
for the chosen propositional fragment, not for all Core.

**Exit condition.** A breadth-first implementation terminates on every input
in the fragment, is sound and complete for ProvesProp, and replays to
checked CoreThm evidence through M3.

**Falsifier / pivot.** If translating ordinary short propositional proofs
requires intermediate formulas outside `Closure(G)`, or N2/N3 cannot merge
the syntactically different states generated by mere context plumbing, then
Core provides no analytic advantage for the first tractable fragment.

### PS3 — Quantifier witnesses and fair search

**Goal.** Isolate the genuinely unbounded part of proof search instead of
pretending it is normalized away.

**Methods.**

* Search uses a growing, typed witness pool `T0 subset T1 subset ...` built
  only from the frozen import signature, contextual variables, and allowed
  fully-applied term formers.
* Use iterative deepening on a lexicographic budget: witness-pool stage,
  focused proof depth, then certificate size.  This is fair and reproducible.
* Index quantified rules by predicate/type head; record which witness and
  which M3 quantifier/structural rule produced each transition.
* First test instantiation and existential introduction separately.  Do not
  add unrestricted Skolemization or new choice constants to the search engine.

**Theorem.**

```text
fairCompleteness:
  if a finite supported Focused proof of G uses witnesses W,
  then W is contained in some Tk and fair search eventually finds a proof of G.
```

This is a semidecision result.  No termination or global efficiency claim is
made for quantified HOL.

**Exit condition.** The boundary between finite analytic search (PS2) and
witness generation (PS3) is explicit in code and theorems; standard M3
quantifier examples replay without new depth-specific search rules.

**Falsifier / pivot.** If ordinary contextual quantifier use requires
unbounded new type shapes, partial applications forbidden by Core, or a new
beta rule per witness/context depth, then the Core term language is obstructing
search rather than constraining it usefully.

### PS4 — Growth experiments and decision

**Goal.** Measure whether the proved search properties make a practical
difference before expanding M4's integration scope.

**Methods.**

Run the same engine and frozen library on parameterized families, first made
from M3 examples and then from M4-generated fragments:

* implication/assumption-chain depth `n`;
* nested context/substitution/weakening depth `n`;
* nested quantified instantiation depth `n`;
* repeated use of pairing, union, separation, power-set, and infinity facts.

For every family and budget, record:

```text
solved / unsolved, normalized states visited, raw states generated,
candidate actions considered, state merges, witness-pool stage,
time, Core certificate size, and replay success.
```

Run ablations: raw search, N0+N1 only, N0--N2, and N0--N3.  This identifies
whether a claimed benefit comes from Core's representation or merely from a
handwritten derived theorem.

**Decision rule.** Core remains the search-language candidate only if:

1. PS2 establishes a nontrivial finite analytic fragment;
2. PS3 preserves one finite rule family across increasing context depth;
3. N2/N3 materially control state growth on the plumbing families; and
4. the mathematical families require reusable rule schemas rather than
   theorem-specific search code.

Otherwise, preserve Core as the certificate target and use contextual HOL (or
another goal language) as the search representation.  M4 then proceeds as a
translation/lint program without assuming that Core itself is the engine.

## Start condition

Do not begin implementation while M3 is still changing.  Once M3 terminates,
first audit its deliverables against the dependencies above: complete lifting,
the CoreThm correspondence boundary, and the exact available contextual
proof constructors. Then begin PS1, followed by PS2, where the completed M3
propositional layer supplies stable interfaces.
