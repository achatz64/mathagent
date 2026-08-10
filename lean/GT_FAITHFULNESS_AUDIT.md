# GT statement-faithfulness audit and handoff plan

## Purpose

This document tracks places where a stable TeX label is mentioned in
`lean/GT.lean`, but the checked Lean type does not visibly expose every clause
of the corresponding statement in `test/GT/GT.tex`.

This is stricter than label coverage. A stronger theorem may count as faithful,
and a bundled `MulEquiv`, `OrderIso`, or typeclass may package several source
clauses. A merely related consequence does not count. For handoff, each closed
item should have a declaration whose type exposes the source obligation or a
short comment explaining exactly which field of a bundled object exposes it.

The separate all-environment audit currently finds 129 labels outside
 theorem-like environments that are not mentioned in the target. Those require
scope classification, but they are not mixed into the confirmed clause gaps
below.

## Difficulty scale

| Grade | Expected work for a smaller Lean model | Typical iterations |
|---|---|---:|
| S | Direct Mathlib wrapper or a short consequence | 1–3 REPL calls |
| M | Small adapter, coercion/API discovery, or several linked declarations | 3–8 REPL calls |
| L | New encoding or nontrivial proof design | 8–20+ REPL/build iterations |

Estimates assume the model reads `OVERVIEW.md` and `LEAN_REPL.md`, prototypes in
`lean_repl`, and then runs `cd lean && lake build GT`.

## Confirmed theorem-environment gaps

### F1 — `bd15`: divisibility conclusion of Lagrange

**Source:** `test/GT/GT.tex:1300–1310` states the cardinality/index identity and
then explicitly concludes that every subgroup order divides the group order.

**Current Lean:** `Subgroup.card_mul_index_eq` gives only the identity.

**Missing public obligation:** a finite-group-facing divisibility theorem, for
example

```lean
theorem Subgroup.card_dvd_card' [Finite G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G
```

**Likely API:** `Subgroup.card_subgroup_dvd_card` in
`Mathlib.GroupTheory.Coset.Card`/the current import closure.

**Difficulty:** **S**. Direct wrapper; 1 REPL call. Excellent small-model task.

---

### F2 — `bd27`: uniqueness of the quotient group structure

**Source:** `test/GT/GT.tex:1598–1603` says that there is a unique group
structure on the coset set for which the quotient map is a homomorphism.

**Current Lean:** `QuotientGroup.ker_mk'_eq` proves only that the normal subgroup
is the kernel. `QuotientGroup.existsUnique_lift` faithfully covers the separate
label `bd27m`, not the unique-group-law clause of `bd27`.

**Missing public obligation:** characterize multiplication and inversion on
cosets, or compare an arbitrary group structure on the quotient carrier for
which the projection is a homomorphism. Comparing raw `Group` structures is
awkward because the standard quotient type already has fixed operations.

**Recommended faithful interface:** avoid equality of typeclass structures if
possible. State that any candidate multiplication/inverse satisfying the
projection equations agrees pointwise with the standard quotient operations;
surjectivity of `QuotientGroup.mk'` should provide uniqueness. Document why
this is the Lean formulation of uniqueness of the group law.

**Difficulty:** **L**. The mathematics is easy, but the encoding is delicate.
Assign to a stronger model first; afterward a smaller model can fill pointwise
surjectivity proofs. Estimated 10–20 iterations.

---

### F3 — `it01`: explicit factorization equation

**Source:** `test/GT/GT.tex:1696–1711` exposes the complete factorization

```text
G → G/ker(f) ≃ range(f) ↪ G'.
```

**Current Lean:** `QuotientGroup.quotientKerMulEquivRange` provides the middle
`MulEquiv`. Kernel normality and the range subgroup are bundled by Mathlib, but
the target does not state that composing the quotient map, equivalence, and
range inclusion equals `f`.

**Missing public obligation:** an equality of `MonoidHom`s expressing the
commuting diagram. Surjectivity and injectivity need not be restated because
they are fields of the quotient map/equivalence/subtype inclusion, but the
comment should say so.

**Difficulty:** **S–M**. Usually `ext x; rfl` or `simp` after choosing the exact
coercions. Good small-model task; 2–5 REPL calls.

---

### F4 — `ga08`: number of conjugates of a subgroup

**Source:** `test/GT/GT.tex:4807–4815` includes both orbit–stabilizer and the
specialization that the number of conjugates of `H` is `(G : N_G(H))`.

**Current Lean:** `MulAction.orbit_cardinal_eq_quotient` and
`MulAction.orbit_card_eq_index` prove orbit–stabilizer but do not instantiate
the action on subgroups or identify the stabilizer with the normalizer.

**Missing public obligation:** a cardinal-valued theorem, preferably with a
`Nat.card` finite specialization, identifying the conjugation orbit of `H`
with the quotient by `Subgroup.normalizer H`.

**Likely route:** use the pointwise conjugation action on `Subgroup G`; prove
(or locate) `stabilizer G H = Subgroup.normalizer (H : Set G)`; then apply the
existing orbit theorem. The Sylow-specific analogue
`Sylow.stabilizer_eq_normalizer` is useful as an API example.

**Difficulty:** **M**. Main risk is selecting the intended `SMul` instance and
normalizer coercions. Suitable for a competent smaller model with the route
fixed; 4–8 iterations.

---

### F5 — `st8`: the stated Sylow corollary

**Source:** `test/GT/GT.tex:6199–6204` additionally says that no Sylow
`p`-subgroup other than `P` normalizes `P`.

**Current Lean:** `IsPGroup.le_sylow_of_le_normalizer` proves the main lemma but
not the explicit corollary.

**Missing public obligation:** for Sylow subgroups `P Q`, if `Q` normalizes
`P`, then `Q = P`, or equivalently `Q ≠ P → ¬ (Q : Subgroup G) ≤ normalizer P`.

**Likely proof:** apply `IsPGroup.le_sylow_of_le_normalizer` to `Q`, then use
maximality/cardinality or the Sylow API to turn `Q ≤ P` into equality.

**Difficulty:** **S**. Good small-model task; 1–3 iterations.

---

### F6 — `r16`: division-algebra conclusion of Schur's lemma

**Source:** `test/GT/GT.tex:8442–8445`, under the chapter's standing
finite-dimensional `F`-algebra/module conventions, says
`End_A(S)` is a division `F`-algebra.

**Current Lean:** `LinearMap.bijective_or_eq_zero_of_simple` states the key
zero-or-bijective lemma, but its type does not expose a division-ring structure
on `Module.End A S`.

**Missing public obligation:** provide the division-ring structure and retain
the existing `Algebra F (Module.End A S)` structure. A practical interface is

```lean
noncomputable def Module.End.divisionRingOfIsSimple ... :
    DivisionRing (Module.End A S)
```

or a theorem returning that structure nonemptily.

**Likely API:** `Module.End.instDivisionRing` exists in
`Mathlib.RingTheory.SimpleModule.Basic`, but requires
`DecidableEq (Module.End A S)`. Use `classical` locally. The algebra structure
already exists when the scalar-tower hypotheses are supplied.

**Difficulty:** **S–M**. Typeclass packaging is the only issue; 2–5 REPL calls.
Good small-model task if the required `classical` step is stated in the prompt.

---

### F7 — `r20`: direct sum of minimal left ideals

**Source:** `test/GT/GT.tex:8538–8550` has two clauses: minimal left ideals are
mutually isomorphic, and `A` is a direct sum of minimal left ideals.

**Current Lean:** `simpleRing_nonempty_linearEquiv_of_isSimpleModule` covers the
first clause (more generally for simple modules). The second clause is only
implicit in generic semisimplicity/decomposition results and is not exposed by
a declaration carrying `r20`.

**Missing public obligation:** specialize the semisimple decomposition of the
regular module to a family of simple submodules of `A`. Since submodules of the
left regular module are left ideals, the type should make the direct-sum family
visible. It is acceptable to use `Submodule A A` rather than introduce a new
left-ideal synonym.

**Likely API:** `IsSemisimpleModule.exists_linearEquiv_dfinsupp` or the existing
wrapper `IsSemisimpleModule.exists_linearEquiv_dfinsupp'`, after obtaining
`IsSemisimpleRing A` from simple + Artinian/finite-dimensional.

**Difficulty:** **M**. Mostly specialization and wording; 3–7 iterations.
Suitable for a smaller model after fixing the desired signature.

---

### F8 — `r22`: all modules are sums of one simple type

**Source:** `test/GT/GT.tex:8552–8560` says every `A`-module is a direct sum of
copies of a chosen simple module `S`.

**Current Lean:** `simpleRing_exists_linearEquiv_fun_of_isSimpleModule` proves
this only for the regular module `A` itself.

**Missing public obligation:** under the chapter's standing finite-dimensional
hypotheses, for an arbitrary module `M`, produce

```lean
∃ n : ℕ, Nonempty (M ≃ₗ[A] (Fin n → S)).
```

A more general intermediate result may use `ι →₀ S` for arbitrary modules.

**Likely route:** establish `IsSemisimpleRing A`, use
`AllSimpleModulesIsomorphic A` to construct `IsIsotypicOfType A M S`, then
apply `IsIsotypicOfType.linearEquiv_fun` (finite module) or
`linearEquiv_finsupp` (arbitrary module). The REPL has already confirmed that
the `linearEquiv_finsupp` route elaborates.

**Difficulty:** **M** for the arbitrary/direct-sum clause; 4–8 iterations.
Suitable for a smaller model with the route supplied.

---

### F9 — `r22`: equal `F`-dimension implies module isomorphism

**Source:** the second sentence of `r22` says two `A`-modules of equal
`F`-dimension are isomorphic.

**Current Lean:** no matching declaration.

**Missing public obligation:** for finite-dimensional `F`-modules `M` and `N`
with compatible `A`-actions,

```lean
Module.finrank F M = Module.finrank F N → Nonempty (M ≃ₗ[A] N).
```

**Likely proof:** use F8 to write `M ≃ (Fin m → S)` and
`N ≃ (Fin n → S)`. Restrict both equivalences to `F`; use
`Module.finrank_pi_fintype` to derive
`m * finrank F S = n * finrank F S`; cancel the positive finrank of the simple
nonzero module `S`; substitute `m = n`; compose the `A`-linear equivalences.
Install `Module.Finite F S` using `Module.Finite.trans F A S` (argument order
must be checked in the local Mathlib version).

**Difficulty:** **M–L**. The proof is elementary but has scalar-tower,
finite-module, and finrank coercion friction. Give to a medium model or split
into helper lemmas. Estimated 6–12 iterations.

## Lower-model handoff order

Recommended independent tasks, smallest first:

1. F1 (`bd15` divisibility).
2. F5 (`st8` Sylow corollary).
3. F6 (`r16` division-ring packaging).
4. F3 (`it01` commuting factorization).
5. F8 (`r22` arbitrary module decomposition).
6. F7 (`r20` regular-module decomposition into simple submodules).
7. F4 (`ga08` conjugation orbit/normalizer).
8. F9 (`r22` equal-dimension classification).
9. F2 (`bd27` uniqueness of quotient group law), after a stronger model fixes
   the statement design.

Each task should be handed off with only one requested declaration or one
helper plus final declaration. Do not ask a smaller model to repair all of
`r20`–`r22` in one prompt.

## Validation checklist per task

1. Read the exact source environment, including chapter-wide hypotheses.
2. Ensure the new declaration's type exposes the missing clause.
3. Prototype from the Mathlib-root `lean_repl`; carry `env` only within the
   prototype branch.
4. Insert the declaration near the existing label family in `lean/GT.lean`.
5. Run `cd lean && lake build GT`.
6. Run `python3 lean/tools/gt_coverage.py test/GT/GT.tex lean/GT.lean` from the
   repository root.
7. Update this file from “confirmed gap” to “closed” with the declaration name.

## Remaining audit work

The list above is an initial set of confirmed mismatches, not a proof that all
other theorem-like labels are faithful. A complete pass should build a clause
matrix for all 136 theorem-like environments with columns for:

- source hypotheses, including chapter-wide assumptions;
- existence/construction clauses;
- equations and commuting diagrams;
- uniqueness clauses;
- iff directions;
- explicitly stated corollaries;
- Lean declaration(s) exposing each clause;
- status: exact, stronger, bundled, partial, omitted, or dependency axiom.

That matrix is mostly reading and classification. Estimate **6–12 model-hours**
for a smaller model in batches of 10–15 labels, followed by a stronger-model
review. It should be completed before treating the 129 labels in non-theorem
environments as formalization tasks.
