# Audit report — FT chapter 1 delta audit (commit 8ba70b2)

Auditor: auditor agent (per AGENTS.md). Subject: `lean/Target.lean` at commit
`8ba70b2` (`5513a047c812c0636c9e3999b42037f8b60dc85cc9715958a8f96408aff37e7b`).
Source of truth: `test/FT/FT.tex` (Milne, *Fields and Galois Theory*, v5.00).

Note on HEAD drift: while the audit ran, HEAD advanced `8ba70b2 → f85bc25`,
but that commit touches only `.pi/subagents.json` (session metadata);
`lean/Target.lean` is byte-identical to `8ba70b2` (sha256 verified), so the
audit is valid for the intended state.

## Per-criteria verdicts

| Criterion | Verdict | Notes |
|---|---|---|
| Provenance | PASS | `# Provenance` section conformant with `PROVENANCE.md` (source/formalization blocks complete; `source-hooks = ["labels"]`). Source hash independently recomputed: `curl -L https://www.jmilne.org/math/CourseNotes/FT500.zip \| sha256sum` = `4912e7f765eb63f8f255277dbdeddb168c31119ac6607a2b8bf8238e3358f472`, matches the recorded hash. |
| Coverage | PASS (delta state) | `tools/ft_coverage.py` reports 144 source labels, 13 mentioned in target — matching the reported state. Chapter 1 ("Basic Definitions and Results") has 24 theorem-like labels; 13 formalized (ef1, ef4, ef6, ef6m, ef7, ef10, ef13+eq7, ef14, ef19, ef20, ef22, ef23); 11 pending (ef24, ef25, ef26, ef27, ef28, ef29, ef30, ef31, ac1, sf10, sf11, ac3) — consistent with the reported work-in-progress and the unintegrated worker (ac1/ac2/ac3/sf10/sf11). Non-theorem-like omitted items: see Finding F2. |
| Compilation | PASS | `lake build Target` → "Build completed successfully"; `lake env lean Target.lean` → exit 0, zero errors/warnings. No `sorry`/`admit`/`axiom` tokens in the target (rg verified). |
| Linters | PASS | All configured linters pass; no `@[nolint]` uses in the target; no linter-related `AUDIT-GAP` needed. (A `PANIC at Option.get!` backtrace appears in `lake build` stderr — this is the known toolchain/lake replay issue documented in `lakefile.toml`; it is not a Target defect.) |
| Axioms | PASS | No `axiom` declarations in the target. `#print axioms` run on all 26 declarations (25 theorems + `monomials` def; via shared REPL with `import Target`): every one depends only on `[propext, Classical.choice, Quot.sound]`. No undeclared/undocumented axioms. |
| Semantic (statement fidelity) | PASS | All 13 chapter-1 labels checked line-by-line against `FT.tex`; see detail below. No false statements, no missing hypotheses, no circularity; compound claims appropriately split. |
| Coding conventions | PASS | Names follow Mathlib conventions and are natural in context (e.g. `exists_factorization_of_map`, `mem_adjoin_iff_exists_finsupp`, `isAlgebraic_tower_trans`). Stable TeX labels kept in source comments per FORMALIZATION.md. |
| Documentation | PASS with 1 minor gap | All declarations carry textbook-level docstrings stating the statement and the proof idea (or declaring triviality); auxiliaries declare their nature. One minor scope-documentation gap flagged in place as `AUDIT-GAP` (Finding F2). |
| Obligation to external library | PASS | No `Improvements for Mathlib` section present; audited conclusion: none required. Every delegation targets an existing Mathlib declaration (signatures verified in REPL); the project-specific items (`monomials`, span-of-monomials bridge, Gauss factorization-existence wrappers) are source-facing wrappers, not upstream candidates. See note F4 on the source's UFD remark. |

## Semantic fidelity detail (label-by-label)

- `ef1` → `FT.isField_iff_forall_ideal_eq_bot_or_eq_top`: exact match (`IsField R ↔ ∀ I : Ideal R, I = ⊥ ∨ I = ⊤` over a nontrivial commutative ring).
- `ef4` → `FT.num_dvd_coeff_zero_and_den_dvd_coeff_natDegree` (+ `'` eval-form + bridge): c ∣ a₀, d ∣ aₘ via `r.num`/`r.den` (coprime by construction); delegation to Mathlib `num_dvd_of_is_root`/`den_dvd_of_is_root` with `Rat.associated_num_den` transfer verified correct.
- `ef6` → `FT.exists_factorization_of_map` (+ primitive auxiliary + `degree_pos_of_nonunit_dvd_of_isPrimitive`): "factors nontrivially in ℚ[X] ⇒ in ℤ[X]" encoded as positive-degree factors of `map (algebraMap ℤ ℚ) f`. Faithful; Gauss bridge via `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast` (signature verified).
- `ef6m` → `FT.monic_factor_eq_map`: monic factor over ℚ of a monic `f ∈ ℤ[X]` comes from `ℤ[X]`; via `IsIntegrallyClosed.eq_map_mul_C_of_dvd` (signature verified). Faithful.
- `ef7` → `FT.eisenstein_irreducible` (+ ℤ-step `eisenstein_irreducible_int` with explicit primitivity): hypotheses (i) p ∤ aₘ, (ii) p ∣ aᵢ for i < m, (iii) p² ∤ a₀; conclusion irreducibility over ℚ. Matches source; the ℤ-step mirrors the source's Gauss-reduction proof. The extra explicit `hp0` hypothesis is implied by `hcoeff` whenever m ≥ 1 (the only case where the source statement is non-vacuous) — no added restriction.
- `ef10` → `FT.finite_degree_iff`, `FT.finrank_tower_mul`, `FT.finrank_mul_of_finite`: finite-iff and `[L:F] = [L:E]·[E:F]` split into three faithful wrappers over `Module.Finite`/`Module.finrank_mul_finrank`.
- `ef13`/`eq7` → `FT.monomials`, `FT.span_closure_eq_span_monomials`, `FT.mem_adjoin_iff_mem_span_monomials`, `FT.mem_adjoin_iff_exists_finsupp`: the finite-sum form (eq7) is exposed as a `Finsupp` over `List S` (non-uniqueness of the representation, noted in the source, is preserved by the encoding). Faithful split of the compound claim.
- `ef14` → `FT.isField_of_isDomain_of_finiteDimensional`: exact match.
- `ef19` → three clause wrappers + `FT.finite_iff_algebraic_and_finiteType`. The normalization of "finitely generated (as a field)" to `Algebra.FiniteType` is faithful here: under the algebraicity that accompanies it in both directions the two readings coincide (F[t] = F(t) for algebraic t), and the ⇐ direction with `Algebra.FiniteType` is equivalent to the source's hypothesis "generated by a finite set of algebraic elements".
- `ef20` → split into (a) `FT.isField_of_subring_of_isAlgebraic` and (b) `FT.isAlgebraic_tower_trans`. Both faithful.
- `ef22` → `FT.algebraic_numbers_countable`: `{x : ℂ | IsAlgebraic ℚ x}.Countable` via `Algebraic.countable` (signature verified). Faithful.
- `ef23` → `FT.transcendental_of_transcendental_int` + `FT.liouville_transcendental`: Milne's α = ∑ 1/2^{n!}; the docstring's claim that the displayed `tsum` is *definitionally* Mathlib's `liouvilleNumber 2` was independently re-verified in the REPL (`rfl` succeeds with `open scoped Nat`), and `transcendental_liouvilleNumber : 2 ≤ m → Transcendental ℤ (liouvilleNumber m)` applies with m = 2. Faithful.

## Findings

| ID | Severity | Location | Finding |
|---|---|---|---|
| F1 | Informational | whole file | Delta state: 13 of 144 theorem-like source labels formalized (chapter 1: 13 of 24). Pending chapter-1 labels: ef24–ef31, ac1, sf10, sf11, ac3. Not a defect; recorded for the ledger. |
| F2 | Minor (documentation) | `lean/Target.lean`, scope-notes block (line 81) | The omitted chapter-1 expositional items `ef11`, `ef12`, `ef16`, `ef17`, `ef18` lack scope citations in the target's scope-notes block, unlike the other omitted items. Flagged in place as an `AUDIT-GAP` (documentation audit); remediation is a comment-level fix. |
| F3 | Minor (code quality) | `FT.injective_of_field` (private, line ~345) | Re-proves an existing Mathlib result: `RingHom.injective` already gives injectivity of a ring hom out of a field into a nontrivial ring (verified by elaborating `g.injective` against the target's import closure). Private auxiliary, correct, not source-facing — not a fidelity defect; recommend delegating in a future pass. |
| F4 | Informational | after source `ef7` (unlabeled prose) | The source states the "last three propositions hold mutatis mutandis with ℤ replaced by a UFD R". This unlabeled generalization is not covered by the label-based inventory and is not formalized. Since it is a source-stated generalization rather than a Mathlib-strengthening, it is not an obligation-section candidate per AUDIT.md; recommend the main agent either add a scope citation or target it in a later pass. |

No essential defects found: no false statements, no missing hypotheses, no
circular arguments, no unrecoverable semantics, no incomplete-proof tokens, no
undocumented axioms, no linter issues.

## Verification evidence

- Build: `lake build Target` → "Build completed successfully (2988 jobs)".
- Fresh compile: `lake env lean Target.lean` → exit 0, no diagnostics (run
  twice, second time after inserting the AUDIT-GAP comment).
- Axioms: `#print axioms` for all 26 declarations via shared REPL
  (`import Mathlib; import Target; import Extlib.GroupTheory.Mil21`); every
  result: `[propext, Classical.choice, Quot.sound]`.
- Coverage: `python3 tools/ft_coverage.py ../test/FT/FT.tex Target.lean` →
  `{"theorem_like_environments": 141, "source_labels": 144,
  "labels_mentioned_in_target": 13, ...}` with the unmentioned-label list
  dominated by later chapters (ag*/cg*/ft*/te*/...), matching the delta state.
- Provenance hash: recomputed sha256 of `FT500.zip` matches the header.
- Delegation signatures verified in REPL: `transcendental_liouvilleNumber`,
  `Algebraic.countable`, `num_dvd_of_is_root`, `den_dvd_of_is_root`,
  `Rat.associated_num_den`, `IsIntegrallyClosed.eq_map_mul_C_of_dvd`,
  `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`,
  `Module.finrank_mul_finrank`, `Algebra.IsAlgebraic.trans`; and
  `∑' n, 1 / 2 ^ n! = liouvilleNumber `2`` by `rfl`.

## Conclusion

**Signed off** for the delta under audit: the 13 formalized chapter-1 items
(ef1, ef4, ef6, ef6m, ef7, ef10, ef13/eq7, ef14, ef19, ef20, ef22, ef23) are
faithful, build clean, lint clean, and depend only on the standard Lean
axioms; provenance and coverage instrumentation are in order.

**Not signed off** as a complete formalization of chapter 1: 11 theorem-like
labels remain pending (F1). This is the expected state of a delta audit, not a
defect; the single `AUDIT-GAP` (F2) is documentation-level.

— auditor agent, single commit on current branch
