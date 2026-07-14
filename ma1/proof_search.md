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

**Deliberate proof-term omission.** The engine does not enumerate every Core
proof term whose type is the current goal. It explores only the analytic moves
of the search calculus. After a search derivation is found, a deterministic
compiler generates the administrative K/S/`axCP`, context-transport, and beta
plumbing required by the M3/Core certificate. Those generated terms are proof
evidence, not alternative search actions or memoized states. This separation
preserves soundness provided every search derivation has a checked compiler
replay. Completeness remains the separate `ProvesProp -> Focused` obligation.
The separation becomes a failure if replay needs theorem-specific
invention, an unbounded new schema family, or unacceptable certificate growth;
PS4 measures that boundary explicitly.

The initial fragment is propositional contextual HOL plus the already-lifted
structural representation.  Quantifier witnesses are introduced only in the
later witness milestone.

## Certified normal forms
Normalization is split by representation. N0 and N3 compose into the search-
state normalizer consumed by candidate generation and memoization. N2 acts
only after translation, on emitted Core propositions. These operations must
not be merged into an uncheckable simplifier. Surface-Core definitional
comparison is a separate interoperability gate described below.

| Name | Object normalized | Basis | Required evidence |
|---|---|---|---|
| N0 | frozen contextual source AST: context order/product and implication closure | contextual syntax and renderer | syntactic equality |
| N2 | translated closed `PC` propositions and exposed sequent closures at emission time | M1 beta basis, M2 Core correspondence, M3 context transport | emitted Core proof of `iff P P'` |
| N3 | search state: sorted/subsumed assumptions, focused goal shape, solved-goal removal | search-calculus theorems | derivation-preserving map between states |

N2 is deliberately restricted.  Core has no equality at arbitrary `Type`, so
it is unsound as a design claim to rewrite arbitrary maps merely because they
denote the same map in the intended model.  A N2 rewrite is permitted only when
the finite live basis supplies the required `PC` observation and M2 can name or
emit its evidence.

The consumer-facing search contract is explicit:

```text
SearchDerivable S := State.proves S
State.normalize S := N3 (N0 S)
State.normalize S = S'  =>  SearchDerivable S <-> SearchDerivable S'
State.normalize (State.normalize S) = State.normalize S
```

N2 is not part of `State.normalize` and therefore does not merge search states
or contribute to state-space finiteness. `State` stores contextual `Formula`,
whereas N2 redexes exist in the translated `CPred`; there is no `CPred ->
Formula` reification and M3 supplies `Proves -> CoreThm`, not a reflection from
arbitrary Core evidence back into `Proves`. N2 instead satisfies its own
emission contract: normalization is idempotent and records a trace whose replay
constructs `CoreThm (iff P P')`. The first prototype uses an oriented,
terminating rule set with a syntactic decrease measure. An e-graph is
explicitly postponed: it can be considered only if every e-class edge carries
a replayable Core certificate and its congruence closure is proved valid for
the chosen domain.

### Surface-Core interoperability gate (formerly N1)

Transparent def/abbrev unfolding belongs to the native Core checker, not to
the current search-state representation. CoreSearch0 states contain typed
contextual formulas and deep CPred/CoreThm evidence; they contain no checker
Expr, declaration body, or unresolved transparent definition. Consequently,
checker definitional equality has no SearchDerivable preservation or
idempotence obligation in PS1 and does not block the search-utility program.

The native checker may retain n1Compare? / n1DefEq as an executable,
hole-rejecting boundary check. It is required when comparing generated and
handwritten .cor, importing rules directly from surface Core, or emitting
surface certificates, and is therefore an interoperability/M4 concern. The
current checker normalizer is partial and regression-checked, not proved
terminating or idempotent. A proof of that checker is required only if a future
design puts surface Expr objects inside search; doing so is an explicit
search-boundary change, not unfinished PS1 normalization.

## Milestones

### PS1 — Search syntax and certified normalization

**Goal.** Define CoreSearch0 states, a finite rule-library interface,
matching/indexing, the composite N0/N3 state normalizer, and the N2 emitted-
proposition normalizer.

**Initial implementation.** Search.lean now fixes the pre-normalization
boundary: a propositional-fragment test, finite list formula closure, and
finite conclusion-directed logical candidates. Its typed Step relation gives
backward transitions for hyp, implication, conjunction, disjunction, and iff;
step_sound replays every such transition into the M3 contextual Proves calculus.
step_core_replay then packages it as conditional deep CoreThm evidence under
the existing M3 lifting certificates.

**Finite-library interface.** Rule is a typed backward transition with its
contextual soundness proof. A declared library is a finite List Rule, and
ruleCandidates enumerates only its applicable transitions. Each returned
RuleApplication replays to deep CoreThm evidence through M3; it does not rely
on implicit weakening or dynamically created declarations.

**Logical-library integration.** logicalTransition? now decides hypothesis
membership and all liftability side conditions, then returns the exact child states
for each built-in logical action. logicalTransition?_step reconstructs the
existing certified Step from every successful computation. LogicalAction.all
is proved exhaustive and logicalLibrary maps that finite enumeration into the
generic rule interface; State.ruleCandidates therefore returns only applicable,
replayable logical transitions.

**First index slice.** FormulaHead classifies the nine formula constructors.
Every Rule declares a finite key list and proves that any successful
transition matches one of those keys. RuleIndex.build precomputes a wildcard
bucket and one bucket per constructor; lookupFormula reads only the wildcard
bucket and the selected constructor bucket, rather than scanning declarations.
RuleIndex.mem_lookupKey_add verifies insertion is retrievable for every key form, while logicalIndex_lookup proves the complete logical index
returns exactly the former conclusion-directed enumeration.

**Typed-symbol refinement.** RuleKey has relation, predicate, and term-constant
keys carrying declaration names and Core type signatures. State.symbolKey? uses
the same lookupRel? and lookupPred? operations as M3 formula checking.
Term.termConstantKey? likewise accepts only declared constants through
lookupConst?; variables and raw embedded terms do not masquerade as constants.
RuleIndex has typed association buckets for all three key forms. The
relation/predicate/term-constant retrieval theorems prove that every matching
typed insertion is returned by State lookup. logicalIndex_lookupState proves
these imported-rule buckets do not change the built-in logical candidate set.

**First-order matcher.** `TermPattern` metavariables range only over complete
typed contextual terms; repeated occurrences must receive the same syntactic
term and type. `FormulaPattern` covers the propositional constructors and
fixed relation/predicate positions, but deliberately has no binder case and no
symbol-position metavariable. `matchFormulaPattern?` is deterministic and a
successful result carries an exact reconstruction equation from the returned
substitution. Executable regressions cover repeated-variable success,
inconsistent repetition, and type mismatch. Binder and higher-order matching
are unrepresentable at this boundary.

**Imported-rule enforcement.** `PatternRule.toRule` is the CoreSearch0 import
path. It constructs the low-level certified transition only after the
restricted matcher succeeds, and proves both declared-key coverage and
contextual soundness transfer. The lower-level `Rule` interface remains for
the built-in logical transitions, whose matchers and soundness proofs are
defined directly. Thus an imported rule cannot silently substitute a
higher-order unifier while still claiming to be a CoreSearch0 pattern rule.

**PS1 exit audit.** N0, N2, and N3 have executable idempotence and
derivability-preservation evidence on their declared domains; N2 traces replay
live CoreThm certificates. Candidate libraries and every index lookup are
finite lists. Built-in and imported applications replay through contextual
soundness and M3 lifting. Typed relation, predicate, and term-constant buckets
have no-lost-candidate theorems, and imported rules are restricted to the
first-order pattern language. The declared PS1 exit condition is therefore
met; quantified/binder matching remains the explicit PS3 extension gate.

**First N0 slice.** For the frozen propositional CoreSearch0 boundary, the typed
source AST is already canonical: connective association and context order are
structural, and the available logical transitions introduce no binders or fresh
variable names. State.n0 is therefore syntactic identity, with proved
State.n0_proves_iff and State.n0_idempotent laws. State.n0Closed? is the
deterministic checked renderer boundary: it maps variables to projections,
constructs Ctx.obj, builds the assumption implication chain, and closes the
context in list order; checked sequents are proved to produce a result. This N0
does not quotient alpha-equivalent quantified states. Such quotienting requires
a renaming-preservation theorem and is an explicit extension gate before PS3,
not a hidden assumption in propositional finiteness.

**First N2 slice.** N2Rule fixes six live reindexing schemas: unary,
and, or, implication, iff, and negation. N2Edge records the selected basis
name and its exact CoreThm certificate; N2Path now also carries checked
connective-congruence traces. The executable n2RootStep? matcher recognizes precisely
those six left-hand sides and returns only the displayed forward orientation. n2Normalize uses a
structural size budget; its output has a replayable Core certificate, satisfies
the declared binder-opaque normal-form test, and is syntactically idempotent.
Thus this N2 domain meets the stated normalizer laws. Quantifier-headed terms
remain opaque: binder movement is the separate Beck-Chevalley gate for a later
N2 extension.

**First N3 slice.** State.n3 is an executable last-occurrence deduplication
of assumptions. It proves exact membership preservation, no duplicates,
idempotence, and a two-way transfer of the contextual Proves judgment.

**Structural finding.** Arbitrary assumption weakening is not a valid generic
M3 transformation: the named all-introduction and context rules carry
freshness obligations over the full assumption list. N3 must therefore
preserve assumption membership exactly; imported-rule application must carry
its own checked structural derivation rather than rely on blanket weakening.

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
* Implement N2 as a list of named, oriented rewrites. A rewrite returns both
  the next emitted proposition and the M2 reference/proof term used to justify
  it; it does not rewrite the source search state.

**Theorems.**

```text
finiteCandidates: normalized state S -> List (Action S)
normalizationSound: normalize S = S' ->
  (SearchDerivable S <-> SearchDerivable S')
normalizationIdempotent: normalize (normalize S) = normalize S
actionCoreThmSound: Action S S' -> CoreThm (close S) follows from close S'
```

**Exit condition.** Every state transition and every N2/N3 rewrite is replayable
as live Core evidence; N0 transformations are justified by syntactic equality;
candidate selection is finite and typed; no rewrite is justified only by the
informal intended model.

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

**Decision — primitive classical negation, tested now (not a fragment).**
Negation is the only genuinely classical and potentially non-analytic part of
the language, so PS2 takes it on directly rather than proving a negation-free
fragment that would pass while saying little about the actual thesis.  M3's
`Proves` reaches negation only through `axCP` (Łukasiewicz contraposition
`(¬ψ→¬φ)→(φ→ψ)`, `Calculus.lean`); there is no `⊥` constructor.  We do **not**
add `⊥` to M3: that would change the already-checked target calculus and blur
the test.  A negation-free certified fragment is retained only as the honest
fallback **if PS2 is falsified**, never as the intended PS2 result.

**First sub-milestone (strict gate).**  In order:

1. Define the two-sided / multi-conclusion focused representation needed to
   express primitive `not`; the single-conclusion `Gamma | Delta |- phi` shape
   cannot move a negated hypothesis across the turnstile cleanly.  A refuted
   branch must be represented **without** introducing a falsity constant.
2. Prove **cut / MP admissibility** for that multi-conclusion focused system —
   this is the gate, because the completeness induction over `Proves` must
   reconstruct `mp`, and the K/S/CP reconstructions depend on it.
3. Prove focused derivations of M3's K, S, and especially `axCP`.
4. Prove search stays **subformula-bounded**, and separately prove that
   compilation stays inside a fixed finite replay-template closure with an
   explicit size bound.

The load-bearing join to M3 is the compile-*back* translation of a
multi-conclusion sequent `Delta |- phi_1, ..., phi_n` to single-conclusion
`Delta |- phi_1 ∨ ... ∨ phi_n` (equivalently `Delta, ¬phi_1, ..., ¬phi_{n-1} |-
phi_n`); this step is precisely where `axCP` is consumed.

**Implementation status (increment 1a — `ContextualHOL/Focused.lean`, builds
clean, no `sorry`).**  Done: the two-sided `FSequent` (`ante |- succ`) and its
**falsity-free `denote`** — a nonempty succedent is the right-nested disjunction
`rightOr`, and the empty succedent is given the meaning "the antecedent is
absurd" (proves every well-typed formula), so no `⊥` constant enters M3.  Also
done: the propositional Hilbert meta-theory the soundness proof consumes
(`pImpId` from K/S, `pOrInl/Inr/Elim`, and assumption-monotonicity `pMono`).

The completeness/soundness target is a new inductive **`ProvesProp`**: the
Hilbert base restricted to the propositional rules, with `ProvesProp.toProves`
injecting it into full `Proves` for Core replay.  This is forced, not stylistic:
full `Proves` carries the quantifier/context rules (`allIntro`, `ctxWeaken`, …)
whose freshness obligations over the assumption list make `pMono` — required by
every left rule — false in general (the PS1 structural finding on assumption
weakening).  This is exactly the `ProvesProp` named in the theorem list below.

**Done (increment 1b — `analyticSound` proven, full build clean, no `sorry`):**
the classical negation kernel and soundness of the analytic LK substrate.

* *Classical kernel.*  Everything classical is derived purely from `axCP`
  `(¬ψ→¬φ)→(φ→ψ)` plus the deduction theorem (`impIntro`), with **no `⊥` and no
  added axioms**: `pEF` (ex falso `⊢¬a→(a→b)`), `pCM` (consequentia mirabilis
  `⊢(¬p→p)→p`, the base case — its derivation nests an `axS` contraction over an
  `axCP` instance, which is what breaks the DNE/DNI mutual circularity), `pDNE`
  (`⊢¬¬p→p`), `pRaa` (reductio: `φ⊢ψ` and `φ⊢¬ψ` give `⊢¬φ`), and `pByCases`
  (classical case split). These constructions may contain formulas that are
  not search subformulas, such as `¬(¬p→p)`. They are deterministic
  administrative content in compile-back and are never offered as search
  choices or inserted into search-state keys.
* *Calculus + soundness.* `FDeriv` is the unfocused two-sided analytic LK
  substrate, not yet the focused calculus. Its rules are `id`, `negR`, `negL`,
  `impR`, `impL`, `andR`, `andL`, `orR`, `orL`, `iffR`, and `iffL`,
  with the principal formula at the head of its side. Primitive `iff` expands
  only to its two directional implications and replays through `axIffI/L/R`.
  `analyticSound : FDeriv G -> denote G` is proven by induction, one soundness
  lemma per rule; `analyticSoundSingle` then gives the concrete one-goal bridge
  `FDeriv <Delta,[phi]> -> Proves Delta phi`. Each rule handles the ⊥-free
  empty-succedent case explicitly:
  `negL`/`impL`/`orL`/`andL` genuinely produce/consume the empty succedent
  (refuted branch) with no falsity constant, discharging it via `pEF`/`pRaa`.
  The right rules consume the succedent-disjunction algebra (`pRightOr_mem`,
  `pOrComm`, `pOrAssocL`) and the classical shifts consume `pByCases`.

**In progress (increment 1c — reprioritized: replay guards first).** The audit
of increment 1b established that primitive negation pushes *zero* non-analytic
content into focused search states or choices — the entire classical payload
(`pCM`'s `¬(¬p→p)` etc.) lives in the deterministic compile-back. That relocates
the pre-registered falsifier from search (b) to replay: the compiler-template
family must stay *fixed* (c) and certificate growth must stay *bounded* (d).
Because those payload formulas are exactly where the stress-test's teeth now
live, they are adjudicated *before* cut-admissibility, not after — proving cut
over an unadjudicated certificate family would build on unverified ground.

Since `ProvesProp` is `Prop`, its intermediate formulas and size are erased, so
the guards cannot even be *stated* over the produced certificate. And `FDeriv` is
a many-constructor `Prop`, so Lean forbids recursing from it into `Type` — a
`FDeriv → PPTerm` compile is impossible, not merely awkward. The substrate is
therefore two `Type`-valued mirrors, both now in place and green:

* **`PPTerm`** mirrors `ProvesProp` (same 15 constructors) with
  `PPTerm.toProvesProp` erasure (search stays in `Prop`) and `PPTerm.size`.
* **`FTrace`** mirrors `FDeriv`'s rule structure in `Type` — the actual data a
  search produces — with `FTrace.toFDeriv` erasure to the `Prop` judgement.

**Done (increment 1c core — `compile` built and sound, full build clean, no
`sorry`).** The whole propositional kernel is re-homed onto `PPTerm` as the
named `ReplayTemplate` set (18 templates: base combinators, the classical
`pEF`/`pCM`/`pDNE`/`pRaa`/`pByCases`/`pMono`, and the succedent/cut algebra), and
`compile : FTrace → ReifiedDenote` produces real certificate data, with
`compileSoundSingle : FTrace ⟨A,[φ]⟩ → Proves A φ` (the certificate erases to
genuine M3 evidence).  It is implemented against the **witness representation**
below (not the `∀query` trap), so `negR` is linear by construction.

`ReifiedDenote ⟨A,φ::Θ⟩ = PPTerm A (rightOr φ Θ)`. The **empty-succedent
(refuted-branch) representation is the load-bearing design decision**, and a
structural analysis of the existing `sound*` nil cases settles it:

* The obvious shape `ReifiedDenote ⟨A,[]⟩ = ∀ query, wt → PPTerm A query` (a
  "prove-any-query" function) is the **exponential trap**. `soundNegR` at nil is
  `pRaa (ih φ) (ih ¬φ)` — it instantiates the refutation **twice**, at `φ` and
  `¬φ`, each call copying the whole sub-certificate. A
  `negR`/left-rule/`negR` chain of depth `k` compounds that ×2 into `2^k`:
  certificate size **exponential in derivation depth**, i.e. falsifier (d)
  *fires*. It also creates the query-closure problem (the function can be asked
  outside `ReplayClosure(G)`).
* The correct shape is an **explicit contradiction witness**
  `ReifiedDenote ⟨A,[]⟩ = Σ ψ, wt ψ × PPTerm A ψ × PPTerm A (¬ψ)`. Then `negR` at
  nil applies `pRaa` to the witness pair *directly* — each cert used **once** —
  so `negR` is **linear**, the ×2 is gone. The witness `ψ` is always a specific
  antecedent-derived formula (it originates at `negL` as the negated hypothesis
  and only propagates to antecedent-subformulas), so `ψ ∈ SearchClosure(G)`
  always: **the unbounded-query problem disappears** — there is no arbitrary
  query to quantify over. The `∀query` function is in fact never needed: `negR`
  is the only rule bridging a nil premise to a non-nil conclusion, and it needs
  exactly `¬φ`.

**Correction (the size recurrence, measured on the actual compiler — active
falsifier-(d) test).** The witness representation removes the *unconditional*
`negR`-at-nil doubling, but it does **not** by itself give a polynomial tree
bound. The empty-succedent `impL` and `orL` branches each embed one child
certificate in **both** halves of the produced `Contradiction`:
`impL`-nil threads `dψ` (which contains `compile t`) into both `posρ` and
`negρ`; `orL`-nil calls `c2.explode` (carrying `c2.pos`,`c2.neg`) in both
outputs. The doubled branch is **fixed** by the rule (`t` for `impL`, `u` for
`orL`) — the "choose the larger branch" mitigation is *not available*: `impL`'s
two premises have different logical roles, unlike symmetric `orL`. So nesting a
doubled branch gives `S(d) = 2·S(d−1)+O(1) = 2^d`: **as a tree, `PPTerm.size` is
exponential in derivation depth.** The earlier "`n^1.58`" claim was wrong and is
retracted.

**Resolution — the context-discharged memoized-replay cost model (falsifier (d)
moved to falsifier (c)), and a correction to a first over-statement.** A first
pass framed this as "`let`-sharing makes the certificate value a DAG, so `size`
overcounts." That framing was rejected on audit and is **not** a valid discharge:
a Lean `let` shares a value at *evaluation* time but gives neither shared Core
proof syntax nor a memoizing replayer, so for the implemented `PPTerm` **tree**
the `2^d` bound still stands until a real memoized replay is defined. The honest
model is an explicit memoizing replay whose **cache key is the fully
context-discharged conclusion** of each node: a node `PPTerm Γ Δ φ` replays the
closed theorem `Δ ⊢ φ` in deduction-theorem normal form — the single closed
formula `Δ.foldr imp φ`. Two nodes are the *same* replayable sub-theorem exactly
when this closed formula agrees; keying on the bare conclusion `φ` (ignoring `Δ`)
is **unsound** — it conflates `a ⊢ φ` with `⊢ φ` and under-counts. The
`let`-shared duplicate branches that make `size` exponential have identical
`(Γ,Δ,φ)`, hence identical discharged key, so memoization collapses exactly them.
Substrate landed and `lake build`-clean (12/12, no sorry/admit/axiom):
`Formula.atoms`; `dischargeKey Δ φ` (deduction-normal-form key); `PPTerm.nodeKeys`
(the *discharged* key of every node); a local `dedup` (no Mathlib in this repo);
and `PPTerm.replayCost := (dedup t.nodeKeys).length` — now an actually-checked
def, not a doc formula (an earlier note claimed `replayCost` had landed; it had
not — only the comment existed. Corrected.). **Key reuse is now a real, checked
round trip** (per the follow-up audit — a bare metric is not the cost of an
implemented replay): `PPTerm.weaken` (Type-level assumption weakening, the
`PPTerm` analogue of `pMono`), `PPTerm.discharge : LiftsAllF Γ Δ → PPTerm Γ Δ φ →
PPTerm Γ [] (dischargeKey Δ φ)` (iterated `impIntro`; the `LiftsAllF` premise
supplies the per-antecedent well-typedness `PPTerm` does not itself enforce), and
`PPTerm.instantiate` (the inverse: weaken the closed proof back under `Δ`,
re-apply hypotheses by `mp`). The key is "closed **w.r.t. assumptions**" — it may
still depend on the fixed contextual variables in `Γ`. This **reduces the size
falsifier (d) to the closure falsifier (c)**: `replayCost` is polynomially bounded
**iff** the set of distinct discharged keys is finite/poly-bounded.

*Antecedent well-typedness invariant (landed).* `discharge`/`instantiate` need
`LiftsAllF Γ Δ` at each node's context, and a bare `PPTerm` carries no *global*
antecedent invariant — so counting `replayCost (compile t)` as reusable keys
required proving that a well-typed *root* context forces every node's context to
be well typed. `PPTerm.CtxsWT` (the per-node `LiftsAllF` predicate) plus
`PPTerm.ctxsWT : LiftsAllF Γ Δ → t.CtxsWT` do this by structure: the only
context-growing constructor, `impIntro`, already carries the `isSome` witness for
the formula it adds, so `LiftsAllF.cons` re-establishes the invariant at each
child. Because `ctxsWT` is universally quantified over `PPTerm` values it applies
verbatim to certificates built through `pMono`/`pRightOr_mem` (no unfolding of
those combinators — only their result contexts need to lift). `compileCtxsWT`
hands this to the search layer for actual traces, given the root antecedent typing
`LiftsAllF Γ A` (trivial `LiftsAllF.nil` at the empty top goal). So every node key
of a compiled trace is now *provably* dischargeable/instantiable, not merely
dischargeable under manually supplied typing evidence. (Doc correction from the
audit: `dischargeKey [a,b] φ = b → (a → φ)` — the list head, i.e. the
most-recently-added assumption, ends up *innermost*, not outermost.) These
operations certify **reusability of a key**; they are *not yet* a memo table or a
shared Core-emission graph, so `replayCost` remains a well-specified **target**
cost model, an *achieved* replay cost only once a memoizing replayer is defined
against `discharge`/`instantiate`.

*Context transport (landed and checked).* The earlier concern that `pMono`
or `pRightOr_mem` might independently generate an exponential key family has
now been isolated and discharged. `ReplayShape = (introduced assumptions,
conclusion)` records a node relative to the root assumption list, and
`nodeKeys_eq_renderShapes` proves that discharged keys are exactly these shapes
rendered against that root. `nodeShapes_pMono` and `shapeCost_pMono` prove
that weakening preserves the full relative-shape list and its distinct count
exactly. `size_pRightOr_mem_le` and
`nodeShapes_pRightOr_mem_length_le` prove that right-disjunction packing does
not duplicate its input and adds at most `2 * (tail.length + 1)` nodes/shapes.
The focused module builds with these theorems and no `sorry`/`admit`.

*Bridge to the advertised metric (landed).* All transport bounds are stated on
`shapeCost` (distinct *root-relative* shapes), but the advertised cost is
`replayCost` (distinct *rendered* keys). `PPTerm.replayCost_le_shapeCost` closes
that gap: within one certificate `nodeKeys = nodeShapes.map (renderReplayShape D)`
(a single root context `D`), so rendering can only merge distinct shapes, never
split them — hence `replayCost ≤ shapeCost` (via `dedup_map_length_le` +
`mem_dedup`). So any `shapeCost` bound transfers to `replayCost`; `shapeCost` is
in fact the better model — it is `pMono`-invariant, where `replayCost` (rendered)
is not.

*Step 2(a) — the collapse core (landed and checked).* The 2^d source is the
empty-succedent `orL`/`impL` compile arms (not `pMono`/`pRightOr_mem`): `orL`
embeds `c2.explode` **twice** (`c2.explode c1.wwt` and `c2.explode (wtNot c1.wwt)`),
doubling `size`. The mathematical content of why this does **not** double
`shapeCost` is now proved, in three landed layers:

1. *`dedup` is set-determined.* `nodup_length_le` (a Mathlib-free pigeonhole via
   `List.erase`), `dedup_nodup`, `dedup_length_le_of_subset`, `dedup_length_congr`,
   `dedup_append_length_le` (subadditivity), `dedup_append_self_length`
   (duplication is free), and `dedup_map_length_of_injective` (an injective
   relabelling — e.g. the uniform `pushReplayShape` suffix push under `impIntro` —
   preserves the count exactly). These are the tools; `(dedup _).length` counts a
   *set*, so duplicating a sublist cannot grow it.
2. *Generic per-node structural bounds.* `shapeCost_impIntro_le`
   (`≤ 1 + child`, via the injective push), `shapeCost_mp_le`
   (`≤ 1 + t + u`), and the existing `shapeCost_pMono` (`= child`). Every compile
   combinator (`pOrElim`, `pEF`, `explode`, `pOrLcut`, …) is a fixed composition of
   `mp`/`impIntro`/`pMono`/`hyp`/axioms, so these compose to a "fixed local family +
   deduped premise families" bound — **except** at the doubling arm, where naive
   subadditivity over `pos ++ neg` would double-count the shared `c2` (confirmed:
   subadditivity alone gives 2× per level = 2^d).
3. *The anti-doubling collapse.* `collapse4` (and the raw-admin `shared_collapse`):
   a shape list `L ⊆ A ++ X1 ++ X2 ++ X3 ++ X4` has distinct count
   `≤ |A| + Σ (dedup Xi).length`, each child counted **once, deduplicated**. With
   `L = pos ++ neg`, `X3, X4` = the twice-embedded `c2.pos/c2.neg` shapes (uniformly
   `push ψ`-transported in *both* halves), the doubling is charged once. This is the
   rigorous statement of "the double `explode` collapses in `shapeCost`."

*Step 2(a) — the `orL` arm instantiated concretely (landed and checked).* The
`collapse4` core is now instantiated against the real `compile` output for the
representative hardest arm — the empty-succedent `orL` node with the double
`explode`. Landed in `Focused.lean`, all `grind`/`omega`-closed, `sorry`-free,
`lake build` 18/18:

* `Contradiction.shapeCost c := (dedup (c.pos.nodeShapes ++ c.neg.nodeShapes)).length`
  — the **joint** distinct-shape count (pos and neg deduped *together*). Joint dedup
  is essential: it is what makes the shared, identically-`push ψ`-transported second
  premise `c2` count once across both certificates.
* `pOrLcut_nodeShapes_subset` / `explode_nodeShapes_subset` — each combinator's shapes
  land in a fixed child-free admin family (`orLcutAdmin`, 7 shapes; `explodeAdmin`,
  `2 + |pEF| = 11` shapes) plus `push`-transported copies of the premise families.
  Both proved by `simp only [… nodeShapes …]; intro a ha; simp only [mem lemmas]; grind`.
* `orL_empty_shapeCost_le` — the payoff: a **coefficient-one** recurrence. Routing the
  membership `pos.nodeShapes ++ neg.nodeShapes ⊆ ADMIN ++ (c1.pos++c1.neg).push φ ++
  (c2.pos++c2.neg).push ψ` (one `grind`), then `dedup_length_le_of_subset`,
  `dedup_append_length_le`, and `dedup_map_length_of_injective` (injective `push`
  preserves the count) give
  `shapeCost(result) ≤ ADMIN.length + shapeCost c1 + shapeCost c2`.
* `orL_empty_shapeCost_le_const` — numeral form `≤ 36 + shapeCost c1 + shapeCost c2`
  (`ADMIN.length = 7+11+7+11 = 36`). The additive term is a **fixed constant**
  independent of the (possibly `2^d`) subtree sizes: the concrete refutation of
  falsifier (d) *for this arm*. Coefficient one — not two — because the shared `c2`
  is embedded in both certificates under the **same** injective `push ψ`, so its shape
  *set* is charged once. (Bounding `c.pos.shapeCost + c.neg.shapeCost` separately would
  reintroduce the `2×`; the joint measure is what avoids it.)

*Step 2(a), continued — the `impL` empty arm + the unified measure (landed and checked).*
Same recipe, second double-embedding arm, all `grind`/`omega`-closed, `sorry`-free,
`lake build` 18/18:

* `impL_empty_shapeCost_le` / `impL_empty_shapeCost_le_const` — the empty-succedent
  `impL` node. Structurally *asymmetric* to `orL`: the `φ`-side premise compiles to a
  **single** `PPTerm A φ` (call it `ih1`) while the `ψ`-side premise compiles to a
  `Contradiction` `cu` on `ψ :: A`. The compiled node shares `ih1` between both output
  certificates via the common `dψ = mp hφ hyp (pMono ih1)` node. Kept as
  set-containment, that shared `ih1` (mixed measure: `ih1.shapeCost`, the single-cert
  count) and the joint `cu` (`cu.shapeCost`) are each charged **once**:
  `shapeCost(result) ≤ impLcutAdmin.length + cu.shapeCost + ih1.shapeCost`, numeral form
  `≤ 8 + cu.shapeCost + ih1.shapeCost` (`impLcutAdmin` = 4 fixed shapes per certificate,
  the `ψ`/`φ.imp ψ` overlap listed in both = 8). Coefficient one on both premises.
* `ReifiedDenote.shapeCost` — **the single distinct-shape measure**, dispatching on the
  succedent (`⟨_,[]⟩ ↦ Contradiction.shapeCost`, `⟨_,_::_⟩ ↦ PPTerm.shapeCost`). This is
  the one statement the eventual compiler bound will be phrased against, covering both
  the refuted (empty) and derived (nonempty) branches uniformly — per the audit.

*Step 2(a), continued — the weight the global bound must use (landed and checked).*
**A fixed constant `K` against a node-counting trace size is FALSE** (Codex audit of the
impL commit, 2026-07-12, verified here): an `FTrace.id` is *one* trace node regardless of
its succedent length, but `compile` replays it through `pRightOr_mem`, whose certificate
grows linearly with the succedent tail (`PPTerm.shapeCost_pRightOr_mem_le`:
`shapeCost ≤ t.nodeShapes.length + 2·(tail.length+1)`). So a one-node identity trace
compiles to an arbitrarily wide certificate — no `K · (node count)` bound can hold.
Landed the fix:

* `FTrace.weightedCost` — internal rule nodes cost 1; an **`id` leaf costs its succedent
  width** `S.length` (the only list-traversing replay op in `compile` is `pRightOr_mem`
  at `id`; every other combinator — `pMono` (shape-preserving), `pByCases`, `pOrElim`,
  `pAndLcut`, `pEF`, … — adds `O(1)` nodes).
* `id_shapeCost_le_weighted` — the base case a fixed `K` cannot satisfy, now proved:
  `ReifiedDenote.shapeCost (compile (id …)) ≤ 3 · (id …).weightedCost`. The `pRightOr_mem`
  width growth is exactly absorbed by the succedent-width charge (`1 + 2·|S| ≤ 3·|S|`).

*Step 2(a), continued — the full per-combinator `shapeCost` layer (landed and checked,
2026-07-12).* Every `PPTerm` combinator that `compile` emits now has a proved
**coefficient-one** distinct-shape bound `shapeCost(comb … children) ≤ Kᵢ + Σ
children.shapeCost` (each child counted once, contradiction `pos`/`neg` jointly), via two
uniform techniques: **(i) membership-routing + joint dedup** — every relative shape lands
in a fixed admin family or an injective-`push` copy of a child's family (`pAndLcut`,
`pIffLcut`, `pOrLcut`, `pOrElim`, `pOrInl`, `pOrInr`, `pImpK`, `pImpTrans`); and **(ii)
skeleton composition** — chain `shapeCost_mp_le`/`shapeCost_impIntro_le`/`shapeCost_pMono`
over the combinator's own sub-combinators, charging each closed piece (`pCM`, `pDNE`,
`pEF`, axioms) by `shapeCost ≤ size` (`PPTerm.shapeCost_le_size`, a constant computed by
`simp [size]`): this closes the two deep ones, `pRaa` (`≤ 100 + hp + hn`) and `pByCases`
(`≤ 200 + h1 + h2`), and `pOrAssocL`. Together with the pre-existing `mp`/`impIntro`/
`pMono`/`pRightOr_mem` bounds, **all** combinators in `compile` are covered. Every lemma is
`sorry`-free and the module builds.

*Step 2(a) COMPLETE — the arm recurrences + the weighted global induction (landed and
checked, 2026-07-13).* The global bound `shapeCost_compile_le_weighted :
ReifiedDenote.shapeCost (compile tr) ≤ 250 · tr.weightedCost` is **proved** (one structural
induction over `FTrace`, `sorry`-free, module builds). Every `compile` arm is dispatched to
its per-arm coefficient-one bound + `omega`. What made it not purely mechanical: the
induction's measure on a refuted (empty-succedent) child is the **joint**
`Contradiction.shapeCost c = dedup(c.pos ++ c.neg)` (this joint dedup is what defeats the
`orL`/`impL`-empty *double-embedding* falsifier). An arm consuming **both** `c.pos` and
`c.neg` of a child contradiction therefore needs a **joint** bound `≤ Kᵢ +
Contradiction.shapeCost c`, never the sum `sc(c.pos)+sc(c.neg)` — which can be `2×` the joint
and, since empty-succedent arms chain, would reintroduce a `2^depth` blow-up (falsifier (d)).
The joint empty-succedent lemmas now proved:

* `orL`/`impL`-empty (pre-existing): `orL_empty_shapeCost_le_const` (`≤ 36 + c1 + c2`),
  `impL_empty_shapeCost_le_const` (`≤ 8 + cu + ih1`).
* `andL`/`iffL`-empty (`⟨pAndLcut c.pos, pAndLcut c.neg⟩` etc.): `andL_empty_shapeCost_le` /
  `iffL_empty_shapeCost_le` (`≤ 18 + Contradiction.shapeCost c`), routing `c.pos`/`c.neg`
  jointly through the cut's *small* admin (`pAndLcutAdmin`/`pIffLcutAdmin`) under the
  injective double `push` — the exact `orL`-empty pattern.
* `negR`-empty (`pRaa hφ c.wwt c.pos c.neg`, result a single `PPTerm`) — the one real
  subtlety, resolved: `negR_empty_shapeCost_le` (`≤ 100 + Contradiction.shapeCost c`). The
  **sum**-form `shapeCost_pRaa_le` (coefficient 2) is **not** used. The joint-ness is
  confined to one small subset lemma `PPTerm.shapeCost_pRaa_hself_joint`: `pRaa` embeds
  `c.pos` and `c.neg` **together** inside the single `impIntro φ` forming `⊢ φ → ¬φ` (via
  `hself = mp hψ (mp _ (pEF) hn) hp`), whose `nodeShapes ⊆ closed_small ++ (hp ++ hn)`
  (`closed_small` = two `mp`-targets + `pEF`'s 9 fixed shapes, length 11); the enclosing
  `pCM`/`pDNE`/`pImpTrans` wrapper is then charged by ordinary **sum** composition.
* `negL`-empty (`⟨φ, pMono ih, hyp⟩`): one PPTerm child, `neg = hyp` a leaf —
  `negL_empty_shapeCost_le` (`≤ 1 + ih.shapeCost`), coefficient one already.

The nonempty-succedent + distinct-children (`andR`/`iffR`-empty) arms are fixed combinator
expressions charged by the sum-form combinator bounds: `negR`/`negL`/`impR`/`impL`/`andR`/
`iffR` nonempty (`pByCases`/`pOrElim` compositions, constants 30–250), `andL`/`orL`/`iffL`/
`orR` nonempty via the single `pAndLcut`/`pOrLcut`/`pIffLcut`/`pOrAssocL` bounds, `orR`-empty
the identity, `andR`/`iffR`-empty the `mp∘mp` intro. `weightedCost (node) = 1 + Σ premise
weightedCosts` and the `id` base case charged by succedent width close the induction (each
arm's `Kᵢ ≤ 250`; the `id` leaf `≤ 3·width`). One Lean plumbing note worth keeping: the child
IH is `ReifiedDenote.shapeCost (compile t) ≤ …` while each arm lemma's RHS is
`PPTerm`/`Contradiction.shapeCost (compile t)` — **defeq but not syntactic** (the succedent
index `rightOr φ (χ0::Θ')` vs `or φ χR`), so `omega` cannot bridge them directly. Feed the IH
through `Nat.add_le_add_left ih _` / `Nat.add_le_add …` (defeq handled at the proof-term
level) and leave `omega` only the pure arithmetic `Kᵢ + 250·Σw ≤ 250·(1 + Σw)`.

*Sharpened exit condition (per Codex audit, 2026-07-12).* `collapse4` + the per-arm
recurrences establish a bound **linear in the weighted `FTrace` (tree) cost**
(`FTrace.weightedCost`) — **not** in a plain tree-node count, which is exactly what the
`id`/`pRightOr_mem` counterexample disproves (a one-node `id` leaf compiles to a
width-`|S|` certificate). `FTrace` is currently a *tree*, so `weightedCost` is a weighted
tree measure and the recurrence shows linearity in *weighted tree-trace* cost only. This
is **distinct from** linearity in a *trace-DAG* size: claiming the latter requires PS2 to
first introduce an actual DAG representation + memoization theorem (a separate,
not-yet-built artifact). Do not merge "weighted FTrace cost" and "trace-DAG size" in the
prose. Either bound is in turn narrower than — and must not be conflated with — a
polynomial in the original search problem: `weightedCost tr` itself can be exponential in
the search problem. So the honest reading of 2(a) is: *the compiler adds no second
exponential on top of its (weighted) tree trace.* Falsifier (d) is refuted **relative to
the weighted tree trace**. The next question — whether analytic search admits a
*polynomially* bounded **memoized trace DAG** — is now **abandoned as a target**
(see *DAG-size resolution* below): the memoized state space is **finite**
(a `≤ 4^{|Sub(G)|}` design argument — the theorem `finiteStateProp` must still
establish it — and finiteness is all termination, the actual exit condition,
requires) while a *polynomial* bound is complexity-theoretically **unjustified and
not to be expected** (it would imply `coNP ⊆ P`, i.e. `P = NP`). The achievable and
needed search-side artifact is therefore the **finite**-state bound
(`finiteStateProp`), not a polynomial one; plus a DAG trace representation + an
actual memoizing replayer against `discharge`/`instantiate`. Until
then `replayCost` remains a checked target metric, not an achieved Core-emission cost.
Then proceed to `replayClosure`, cut-admissibility (of `FDeriv`, not the vacuous
MP-admissibility of `ProvesProp`), the focus discipline, `focusedComplete`, and
subformula-boundedness.

*DAG-size resolution (2026-07-12) — finite is the target; polynomial is abandoned
as complexity-theoretically unjustified.* The recurring "central falsifier" was
whether the **memoized analytic-search DAG** — the set of distinct sequents /
discharged keys reachable from a goal `G`, onto which memoization collapses the
exponential search *tree* — is **polynomially** bounded in `|G|`. The polynomial
target is dropped; the finite bound is the real, and sufficient, goal:

1. *Finite (the target — all the exit condition needs; still to be proved as
   `finiteStateProp`).* Every reachable sequent is a pair of sub-**sets** of the
   signed subformula closure `Sub(G) = SearchClosure(G)` (analyticity: each rule
   replaces a principal formula by strict subformulas and introduces nothing
   outside the closure). So the reachable set has size `≤ 4^{|Sub(G)|}` —
   **finite**. This is at present a *design argument*, not yet a theorem: it
   depends on proving closure under the rules, set-normalized contexts, and that
   the final focused rules introduce nothing further — which is exactly what
   `finiteStateProp` must establish. Finiteness is what termination of a memoizing
   breadth-first search needs, so the **exit condition** (termination + soundness +
   completeness) rests on `finiteStateProp`, not on any polynomial claim.

2. *Polynomial (abandoned — complexity-theoretically unjustified, not disproved
   here).* A **polynomial** bound on that DAG would collapse `coNP` into `P`. If
   every `G` had a reachable-sequent DAG of `≤ p(|G|)` nodes, that DAG is computable
   in `poly(|G|)` time (BFS: `≤ p(|G|)` nodes, each with `≤ 2·|Sub(G)|`
   rule-successors), and a monotone least fixpoint over it (mark `id`-axioms,
   propagate through rules) decides derivability in `poly` time. The calculus is
   sound and complete for classical propositional provability (`ProvesProp` over
   the `K`/`S`/`axCP` basis is classical, so its decision problem is `coNP`-complete
   `TAUT`), so this would put a `coNP`-complete problem in `P`, i.e. `P = NP`. This
   is decisive evidence *against* the polynomial target — no such bound should be
   expected — but it is a **conditional** implication (`P = NP`), not an
   unconditional proof that the bound is false. Note the two available unconditional
   lower bounds do **not** close this: Haken's exponential bound is for *resolution*,
   and if this analytic multi-conclusion calculus *subsumes* resolution it is the
   **stronger** system, so lower bounds transfer strong→weak, not weak→strong — a
   stronger proof system can have *shorter* proofs, so Haken gives no lower bound
   here. An unconditional exponential lower bound for this exact normalized focused
   state graph has not been proved (proving one is Frege/sequent-system proof
   complexity, substantially harder than resolution and not attempted here).

*Consequence for PS2.* The correct search-side target is the **finite** state
bound (`finiteStateProp`) giving **termination**, not a polynomial one.
"Polynomially bounded memoized trace DAG" is struck as a goal — complexity-
theoretically unjustified (⟹ `P = NP`) for any complete procedure over a
`coNP`-hard fragment, and not worth pursuing. This does **not** weaken PS2:
a certifying decision procedure for classical propositional logic is *expected* to
be worst-case exponential. PS2's value is **soundness + completeness + termination
+ a certificate that adds no *further* exponential** (the linear-in-weighted-trace
compiler result), not polynomial-time decision. `replayCost`/`weightedCost` are
accordingly **finite** checked metrics, not polynomial ones. The earlier
"`replayCost` polynomially bounded **iff** distinct discharged keys poly-bounded"
reduction still holds, but its right-hand side is not to be expected (poly ⟹
`P = NP`); the honest, provable reading is "`replayCost` is *finite*, bounded by
`|ReplayClosure(G)|`."

*Finite-state branch — steps 1–3 + step-4 set-key hypergraph landed and checked (2026-07-14,
`ContextualHOL/FiniteState.lean`).* Per the audit, finiteness is proved for the **analytic
state** (`FSequent`, intended to underlie the later focused calculus), not the `FDeriv`
trace language, in the order: (1) state + transitions; (2) closure into signed `Sub(G)`;
(3) normalized set-key + the `≤ 4^{|Sub(G)|}` count; (4) memoized BFS + termination. Steps
1–3 are now proved, `sorry`-free:

* **Signed subformula closure** `Formula.searchClosure`: immediate subformulas *plus*, for
  each `iff φ ψ`, the two implications `imp φ ψ`/`imp ψ φ` that the `iff` rules expose (added
  as elements, so the recursion stays structural on `φ`,`ψ` — `imp φ ψ` is not a subterm of
  `iff φ ψ` and has equal size, so neither structural nor size recursion could recurse
  *through* it). Key lemma `Formula.mem_searchClosure_trans`: the closure is downward closed
  (`b ∈ a.searchClosure → a.searchClosure ⊇ b.searchClosure`) — the two `iff`-implication
  subcases are discharged directly, the constructor-child cases by IH.
* **Transitions** `FStep : FSequent → FSequent → Prop`: the 15 backward analytic rules as
  premise-generation (principal at the head of its side; reordering to any position is
  deferred to state normalization). `SearchClosed C` / `FSequent.InClosure C S`.
* **Closure preservation (step 2)** `FStep.inClosure`: every `FStep` maps an in-closure
  state to an in-closure state — search never leaves `Sub(G)`. This is the analyticity
  fact the `4^{|Sub(G)|}` count rests on. Because `FSequent` still stores lists (ordering +
  duplicates), the count is *not* over raw sequents but over a normalized key (step 3).
* **Normalized key + finite bound (step 3)** `normKey C S = (C.filter (∈ ante), C.filter
  (∈ succ))`: `C` filtered by each side, collapsing order and duplicates to a **pair of
  sub-sets of `C`**. It is canonical (`normKey_congr`: depends only on the ante/succ sets)
  and, on in-closure states, faithful (`mem_normKey_ante_iff`: loses no formula). A
  self-contained powerset `powerList` (`length_powerList = 2^{|C|}`, `filter_mem_powerList`;
  no Batteries `List.sublists`) gives the master list `allKeys C` of `2^{|C|}·2^{|C|} =
  4^{|C|}` keys, and `finiteStateProp` proves every `normKey C S` lands in it. `FStepStar`
  (reflexive–transitive closure) + `FStepStar.inClosure` lift this to reachability
  (`reachable_key_faithful_finite`), and `goalClosure G` / `searchClosed_goalClosure` /
  `initial_inClosure` assemble `C` for a goal (`finiteStateProp_goal`). Membership uses a
  `DecidableEq`-only Bool test `memb` (core's list `Decidable (·∈·)` needs `LawfulBEq`,
  which `Formula` doesn't derive); `4^n = 2^n·2^n` and the two-arg powerset count are
  hand-proved (no Mathlib `ring`/`mul_pow`).
* **Step 4 (in progress) — the normalized AND/OR hypergraph on set-keys.** A finite
  normalized-state *envelope* (step 3) is not yet a memoized search *algorithm*. The audit's
  original framing was "coherence gate then hyperedge gate then typed bridge," and a first
  `FStepArb` (permute a side then step at the head → any member principal;
  `FStep.toArb`/`FStepArb.of_seqPerm`/`FStepArb.inClosure`) landed as a reordering-coherence
  foundation. **But a two-way one-step simulation of `FStepArb` by a deduplicated key relation
  is provably false**: deduplication *changes* the operational rule — contraction is baked into
  the set level, not a missing lemma. (Counterexample: an antecedent with two copies of
  `and p q`; raw `FStepArb` applies `andL` to one copy leaving `{and p q, p, q}`, the dedup
  representative has one copy and yields `{p, q}` — different keys.) So step 4 defines the rule
  **directly on set-keys** (2026-07-14, `FiniteState.lean`, sorry-free):
  * `sremove` (set-level deletion of a formula) + `mem_sremove`.
  * `KStep : FSequent → List FSequent → Prop` — 10 backward rules; principal chosen *anywhere*
    in a side (membership, not head), deleted at set level, components added; the four
    two-premise rules (`andR`,`orL`,`impL`,`iffR`) emit a **two-element premise list = one
    AND/OR hyperedge** (retained, not flattened to `S → S'` edges).
  * `KProvable : FSequent → Prop` — AND/OR reachability: identity axiom, or *some* rule reduces
    to a hyperedge whose premises are *all* provable (`∀ P ∈ ps, KProvable P`).
  * `KStep.inClosure` — every hyperedge premise stays in the closure `C` (gate-2 analyticity;
    mirror of `FStep.inClosure`), so reachable keys are the same `≤ 4^{|C|}` finite set.
  * `KStep.respects_setEq` — the rule is **well-defined on sets**: `SetEq`-equal keys fire
    `SetEq`-equal hyperedges (pointwise `SetEqAll`). This is the *full* quotient (reordering
    **and** duplicate multiplicity) that the one-step `FStepArb` quotient could not reach —
    the real fix.
  * *Remaining (recorded as TODO in the module):* **correspondence** `KProvable ↔`
    `FTrace`/`ProvesProp` derivability, proved with explicit contraction/exchange
    admissibility (a normalized-hyperderivation ↔ real-derivation theorem, *not* a raw
    one-step equivalence), and the **typed bridge** re-attaching `FTrace`'s
    `liftFormula?`/`LiftsAllF` guards. Then memoized AND/OR evaluation over the `≤ 4^{|C|}`
    keys (terminating by the finite bound) is the decision procedure.
  (`FiniteState.lean` is built via the explicit `lake build ContextualHOL.FiniteState`
  target, like `Focused.lean` — neither is in the default `lake build` module set.)

For a *meaningful* fixed-family theorem (c), `compile` is structured from a
finite named `ReplayTemplate` set (`pEF`,`pCM`,`pDNE`,`pRaa`,`pByCases`, `∨`/`∧`
plumbing) — "all certificates use the 15 primitive `PPTerm` constructors" is
vacuous. Then `replayClosure` (`PPTerm.formulas ⊆ ReplayClosure(G)`, reusing
`Search.lean`'s `Formula.subformulas`) and the `replaySize` recurrence. Only
then: cut/MP admissibility, the focus discipline, `focusedComplete`, and
subformula-boundedness.

**Methods.**

* Define invertible decomposition rules for implication, conjunction,
  disjunction, and iff; use a focus discipline for non-invertible choices.
  Primitive `not` is handled by the two-sided representation above, compiled to
  `axCP`, not by an intuitionistic `¬`-introduction (M3 has no falsity rule).
* Use a two-sided / multi-conclusion search shape internally; compile it to the
  single-conclusion `Gamma | Delta |- phi` M3 sequent at Core-emission time via
  the disjunction/negation translation.  Assumptions are represented by their
  canonical implication chain only at that emission boundary, not used as the
  search data structure.
* Memoize normalized states.  A state key contains the normalized context,
  multiset/set discipline for assumptions (as justified by the calculus), and
  focused goal; it never contains its proof history.
* Prove the conversion to/from the M3 propositional fragment before using
  tactics or cost heuristics.  Heuristics may choose an action order but may
  not change the calculus.

**Theorems.**

```text
analyticSound:   FDeriv G -> denote G
analyticSoundSingle: FDeriv <Delta,[phi]> -> Proves Delta phi
focusedSound:    Focused G -> Proves G
focusedComplete: ProvesProp G <-> Focused G
cutAdmissible:   focused MP/cut is admissible in the multi-conclusion system
subformula:      every formula in a Focused derivation of G is in SearchClosure(G)
replayClosure:   every compiler-introduced formula is in ReplayClosure(G)
replaySize:      compilation has an explicit size recurrence/bound
finiteStateProp: normalizing propositional states to a set-key (normKey, a pair of
                 subsets of SearchClosure(G)) yields ≤ 4^{|SearchClosure(G)|} keys
                 [PROVED, ContextualHOL/FiniteState.lean — over FSequent's normKey, the
                 order/duplicate-insensitive set-key; supersedes the earlier N0+N3 framing]
```

The completeness target is deliberately **internal**: `ProvesProp G` is M3's own
propositional provability over the K/S/`axCP` basis, not classical validity
under boolean valuations.  This makes it a `Focused ↔ Proves`-restricted
equivalence that is checkable against M3, and avoids a separate semantic
completeness result.

`SearchClosure(G)` is the finite signed-subformula closure of the goal and
assumptions, extended by the two directional implications of every primitive
`iff` subformula. It bounds formulas that may occur in focused states and
actions;
the empty succedent is permitted as an internal refutation state, not reified
as a new M3 formula. This is the closure used by memoization, the subformula
theorem, and `finiteStateProp`.

`ReplayClosure(G)` extends `SearchClosure(G)` with instances of a fixed finite
compiler-template family, initially K, S, `axCP`, `pEF`, `pCM`, DNE, reductio,
and the required disjunction/context plumbing. It may therefore contain
administrative formulas such as `¬(¬p→p)` which never occur in focused search.
Its obligations are replayability, finiteness, and a checked size bound—not the
search-calculus subformula property. The final theorem gives a terminating
decision procedure for the chosen propositional fragment, not for all Core.

**Exit condition.** A breadth-first implementation terminates on every input
in the fragment, is sound and complete for ProvesProp, and replays to
checked CoreThm evidence through M3.

**Falsifier / pivot.** These are pre-registered, not discovered mid-proof.
Primitive negation in the present Core/M3 representation is judged to obstruct
analytic search if it forces any of: (a) a falsity constant or empty-succedent
object reified inside M3; (b) formulas outside `SearchClosure(G)` in focused
states or choices; (c) a replay-template family that grows with theorem or
context depth rather than remaining fixed; or (d) replay certificates whose
measured growth makes the separation practically useless. N3 failing to merge
states generated by mere context plumbing is likewise a falsifier. 

### PS3 — Quantifier witnesses and fair search

**Goal.** Isolate the genuinely unbounded part of proof search instead of
pretending it is normalized away.

**Methods.**

* Before memoizing quantified states, either extend N0 with a proved alpha-renaming-preservation theorem or keep binder names frozen from the input and witness policy; do not quotient by an unproved alpha key.
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
time, Core certificate size, search-derivation-to-certificate expansion ratio,
replay-template instances, and replay success.
```

Run state-space ablations: raw search, N0 only, and N0+N3. Separately run N2
off/on at Core emission and compare certificate size and replay cost. This
separates state canonicalization from certificate normalization and identifies
whether a claimed benefit comes from the Core representation or merely from a
handwritten derived theorem. The surface-Core definitional-equality gate is
also measured separately at import/emission boundaries; neither it nor N2
changes the search-state count. The same measurements must distinguish focused
search nodes from deterministically generated administrative Core nodes; an
unbounded replay schema family or uncontrolled expansion fails the claimed
search/certificate separation even when focused-state counts are small.

**Decision rule.** Core remains the search-language candidate only if:

1. PS2 establishes a nontrivial finite analytic fragment;
2. PS3 preserves one finite rule family across increasing context depth;
3. N3 materially controls state growth on the plumbing families, while N2
   materially reduces emitted certificate size or replay cost; and
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
