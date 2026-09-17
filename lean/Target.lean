import Extlib.GroupTheory.Mil21
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Localization.Rat
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Provenance

```toml
[source]
title    = "Fields and Galois Theory (v5.00)"
author   = ["Milne, James S."]
location = "https://www.jmilne.org/math/CourseNotes/FT500.zip"
hash     = "sha256:4912e7f765eb63f8f255277dbdeddb168c31119ac6607a2b8bf8238e3358f472"
year     = 2021
type     = "book"

[formalization]
formalizers = ["achatz64"]
scope       = """
  Exercises, solutions, and material of purely expositional nature (remarks,
  examples, asides, notes) are omitted.  The stable TeX labels are recorded in
  comments.  Declaration names follow Mathlib conventions and deliberately
  state the Mathlib formulation, which is occasionally more general than the
  formulation in the text.
  """
source-hooks = ["labels"]
```
-/

/-!
# Fields and Galois Theory (Milne FT v5.00)

Formalization of Milne's *Fields and Galois Theory* (v5.00).  Source-extraction
script: `tools/ft_inventory.py`; coverage audit: `tools/ft_coverage.py`.
-/

namespace FT

open scoped Polynomial
open scoped Pointwise

/-!
## Basic Definitions and Results

### Scope notes for omitted material (expositional by the provenance rule)

- `ef0` (definition of a field): mapped to the Mathlib `Field` class.
- `ef2` (examples of fields): `ℚ`, `ℝ`, `ℂ`, `ZMod p` for prime `p` are all
  `Field` instances in Mathlib.
- `ef3` (characteristic of a ring, prime field): Mathlib `RingChar`,
  `CharP`, `PrimeField`.
- `ef3a` (polynomial ring review): Mathlib `Polynomial`, `Polynomial.R `.
- `ef3b` (division algorithm): Mathlib `EuclideanDomain`,
  `Polynomial.modX_eq_sub_eval` / `Polynomial.div_by_monic` API.
- `ef3c` (factor theorem): Mathlib `Polynomial.eval_sub_factor` /
  `Polynomial.factor_theorem`-style lemmas (`Polynomial.eval` root and `X - C a`
  divisibility).
- `ef3d` (Euclid's algorithm for `F[X]`): Mathlib `EuclideanDomain.gcd`,
  `euclidAkgcd_eq_gcd`-style API for polynomial GCDs.
- `ef3e` (ideals of `F[X]` are principal): `PrincipalIdealRing` instance on
  `Polynomial` over a field (`EuclideanDomain.instPrincipal`).
- `ef3f` (field of fractions `F(X)`): Mathlib `FractionRing (F[X])` = `F(X)`.
- `ef5` (example: `X³ - 3X - 1` irreducible by root test): instance of the
  cubic-root criterion; omitted as an example.
- `ef6n` (aside: alternative proof of `ef6m` via algebraic integers):
  expositional aside; the integrally-closed-domain route is Mathlib's
  `IsIntegrallyClosed` API used by `Polynomial.GaussLemma.lean`.
- `ef8`, `ef8m` (remarks: factoring algorithm, content mod `p` observation):
  expositional; the mod-`p` content observation is subsumed by
  `eisenstein_irreducible_int` below.
- `ef9` (examples: `[ℂ:ℝ] = 2`, `[ℝ:ℚ] = ∞`): `Complex.finrank_real_complex`
  in Mathlib gives (a); (b) is a cardinality observation.
- `ef15` (example: `ℚ[π]`): instance of `mem_adjoin_iff_exists_finsupp` below.
-/

section Fields

/-- FT `ef1`. A nonzero commutative ring `R` is a field if and only if it has no
ideals other than `(0)` and `R`. -/
theorem isField_iff_forall_ideal_eq_bot_or_eq_top {R : Type*} [CommRing R] [Nontrivial R] :
    IsField R ↔ ∀ I : Ideal R, I = ⊥ ∨ I = ⊤ :=
  ⟨fun h I => (Ring.isField_iff_isSimpleOrder_ideal.mp h).eq_bot_or_eq_top I, fun H => by
    by_contra h
    obtain ⟨I, hI, hItop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp h
    rcases H I with hIBot | hITop
    · exact hI.ne' hIBot
    · exact hItop.ne hITop⟩

end Fields

section FactoringPolynomials

open Polynomial

/-- FT `ef4`. Rational root divisibility: if `r = c/d ∈ ℚ` (in lowest terms, here `r.num`
and `r.den`, which are automatically coprime) is a root of `f ∈ ℤ[X]`, then
`c ∣ a₀` and `d ∣ aₘ`, where `a₀ = f.coeff 0` and `aₘ = f.coeff f.natDegree` is the
leading coefficient.

Delegates to Mathlib's rational root theorem `num_dvd_of_is_root` / `den_dvd_of_is_root`
for the UFD `ℤ` inside its fraction field `ℚ`, transferring the divisibility statements
from `IsFractionRing.num ℤ r` / `IsFractionRing.den ℤ r` to `r.num` / `r.den` along the
unit-equivalence `Rat.associated_num_den`. -/
theorem num_dvd_coeff_zero_and_den_dvd_coeff_natDegree {f : ℤ[X]} {r : ℚ}
    (hr : Polynomial.aeval r f = 0) :
    (r.num : ℤ) ∣ f.coeff 0 ∧ (r.den : ℤ) ∣ f.coeff f.natDegree := by
  have h1 : IsFractionRing.num ℤ r ∣ f.coeff 0 := num_dvd_of_is_root hr
  have h2 : (IsFractionRing.den ℤ r : ℤ) ∣ f.leadingCoeff := den_dvd_of_is_root hr
  rw [show f.leadingCoeff = f.coeff f.natDegree from rfl] at h2
  have hassoc := Rat.associated_num_den r
  exact ⟨hassoc.1.dvd_iff_dvd_left.mp h1, hassoc.2.dvd_iff_dvd_left.mp h2⟩

/-- Bridge between the `aeval` reading and the `eval ∘ map (algebraMap ℤ ℚ)` reading of
"`r` is a root of `f : ℤ[X]`". -/
theorem aeval_eq_eval_map_algebraMap (f : ℤ[X]) (r : ℚ) :
    Polynomial.aeval r f = Polynomial.eval r (Polynomial.map (algebraMap ℤ ℚ) f) := by
  rw [Polynomial.aeval_def, Polynomial.eval_map]

/-- FT `ef4`, `eval`-form hypothesis: `r` is a root of `f` viewed in `ℚ[X]` via the
inclusion `ℤ → ℚ`. -/
theorem num_dvd_coeff_zero_and_den_dvd_coeff_natDegree' {f : ℤ[X]} {r : ℚ}
    (hr : Polynomial.eval r (Polynomial.map (algebraMap ℤ ℚ) f) = 0) :
    (r.num : ℤ) ∣ f.coeff 0 ∧ (r.den : ℤ) ∣ f.coeff f.natDegree := by
  rw [← aeval_eq_eval_map_algebraMap] at hr
  exact num_dvd_coeff_zero_and_den_dvd_coeff_natDegree hr

/-- FT `ef7` (integer version). Eisenstein's criterion in `ℤ[X]`: if the primitive polynomial
`f ∈ ℤ[X]` has all coefficients of degree `< f.natDegree` divisible by the prime `p`, its
leading coefficient not divisible by `p`, and its constant coefficient not divisible by `p ^ 2`,
then `f` is irreducible in `ℤ[X]`.  This is the `ℤ[X]`-step of the source proof of FT `ef7`,
which reduces irreducibility over `ℚ` to irreducibility over `ℤ` by Gauss's lemma. -/
theorem eisenstein_irreducible_int (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hp0 : (p : ℤ) ∣ f.coeff 0)
    (hp2 : ¬ ((p : ℤ) ^ 2 ∣ f.coeff 0))
    (hcoeff : ∀ i : ℕ, i < f.natDegree → (p : ℤ) ∣ f.coeff i)
    (hlead : ¬ (p : ℤ) ∣ f.coeff f.natDegree)
    (hprim : f.IsPrimitive) : Irreducible f := by
  have hpi : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 hpi
  have hf0 : f ≠ 0 := fun hf => hp2 (by simp [hf])
  have hfd0 : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h | h
    · exact absurd (by rw [h]; exact hp0) hlead
    · exact h
  refine Polynomial.irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hprim
  · rw [Ideal.mem_span_singleton]
    exact hlead
  · intro n hn
    rw [Ideal.mem_span_singleton]
    rw [Polynomial.degree_eq_natDegree hf0] at hn
    exact hcoeff n (by exact_mod_cast hn)
  · exact natDegree_pos_iff_degree_pos.mp hfd0
  · intro h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    exact hp2 h

/-- FT `ef7`. **Eisenstein's irreducibility criterion.**  Let `f = a_m X ^ m + ⋯ + a_0 ∈ ℤ[X]`
and let `p` be a prime such that (i) `p ∤ a_m`, (ii) `p ∣ a_i` for all `i < m`, and
(iii) `p ^ 2 ∤ a_0`.  Then `f` is irreducible in `ℚ[X]`.

The proof follows the source: by Gauss's lemma it suffices to prove irreducibility in `ℤ[X]`.
Factoring out the content reduces to the primitive part `f.primPart`, which again satisfies
Eisenstein's hypotheses (the content is not divisible by `p`, since it divides the leading
coefficient `a_m`), and for primitive polynomials we apply the reduction mod `p`. -/
theorem eisenstein_irreducible (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hp0 : (p : ℤ) ∣ f.coeff 0)
    (hp2 : ¬ ((p : ℤ) ^ 2 ∣ f.coeff 0))
    (hcoeff : ∀ i : ℕ, i < f.natDegree → (p : ℤ) ∣ f.coeff i)
    (hlead : ¬ (p : ℤ) ∣ f.coeff f.natDegree) :
    Irreducible (Polynomial.map (algebraMap ℤ ℚ) f) := by
  have hpz : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hf0 : f ≠ 0 := fun hf => hlead (by simp [hf])
  have hc0 : f.content ≠ 0 := fun h => hf0 (Polynomial.content_eq_zero_iff.mp h)
  -- `p` does not divide the content, since the content divides the leading coefficient
  have hpc : ¬ ((p : ℤ) ∣ f.content) := fun h =>
    hlead (h.trans (Polynomial.content_dvd_coeff f.natDegree))
  set g := f.primPart with hgd
  have hfC : f = C f.content * g := Polynomial.eq_C_content_mul_primPart f
  have hgn0 : g ≠ 0 := by
    intro h
    apply hf0
    rw [hfC, h]
    exact mul_zero _
  have hglc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgn0
  -- `g` has the same degree as `f`
  have hng : f.natDegree = g.natDegree :=
    hfC ▸ natDegree_C_mul_of_mul_ne_zero (a := f.content) (p := g)
      (mul_ne_zero hc0 hglc0)
  -- the coefficients of `g` are those of `f` divided by the content
  have hfg : ∀ i : ℕ, f.coeff i = f.content * g.coeff i := fun i => by
    conv_lhs => rw [hfC, coeff_C_mul]
  have hleadeq : f.coeff f.natDegree = f.content * g.leadingCoeff := by
    rw [hfg, hng]
    rfl
  -- `g` again satisfies Eisenstein's hypotheses
  have hirrg : Irreducible g := by
    refine eisenstein_irreducible_int g p hp ?_ ?_ ?_ ?_ (Polynomial.isPrimitive_primPart f)
    · have h' : (p : ℤ) ∣ f.content * g.coeff 0 := by rw [← hfg]; exact hp0
      rcases hpz.dvd_or_dvd h' with h | h
      · exact absurd h hpc
      · exact h
    · intro h
      refine hp2 ?_
      rw [hfg]
      exact dvd_mul_of_dvd_right h _
    · intro i hi
      have h' : (p : ℤ) ∣ f.content * g.coeff i := by
        rw [← hfg]
        exact hcoeff i (by rw [hng]; exact hi)
      rcases hpz.dvd_or_dvd h' with h | h
      · exact absurd h hpc
      · exact h
    · intro h
      refine hlead ?_
      rw [hleadeq]
      exact dvd_mul_of_dvd_right h _
  -- Gauss's lemma: `g` stays irreducible over `ℚ`
  have hgcast : Irreducible (Polynomial.map (Int.castRingHom ℚ) g) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (Polynomial.isPrimitive_primPart f)).mp hirrg
  -- `f` is a unit multiple (in `ℚ[X]`) of `g`
  have hmap : Polynomial.map (algebraMap ℤ ℚ) f
      = C ((f.content : ℚ)) * Polynomial.map (Int.castRingHom ℚ) g := by
    conv_lhs => rw [hfC, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hu : IsUnit (C ((f.content : ℚ))) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc0))
  have hassoc : Associated (Polynomial.map (Int.castRingHom ℚ) g)
      (C ((f.content : ℚ)) * Polynomial.map (Int.castRingHom ℚ) g) := by
    rw [mul_comm]
    exact (associated_mul_unit_left _ _ hu).symm
  rw [hmap]
  exact hassoc.irreducible hgcast

end FactoringPolynomials

section Extensions

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]

/-- A ring homomorphism out of a field into a nontrivial ring is injective. -/
private theorem injective_of_field {K S : Type*} [Field K] [Ring S] [Nontrivial S]
    (g : K →+* S) : Function.Injective g := by
  intro a b h
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h0 : g (a - b) = 0 := by rw [map_sub, h, sub_self]
  have h1 : (1 : S) = 0 := by
    rw [← map_one g, ← mul_inv_cancel₀ hne, map_mul, h0, zero_mul]
  exact one_ne_zero h1

/-- FT `ef10`, finiteness half: `L/F` has finite degree if and only if both `L/E` and
`E/F` have finite degree.

`(→)` an `F`-spanning set of `L` also `E`-spans it (`Module.Finite.of_restrictScalars_finite`),
and `E` embeds `F`-linearly into the finite `F`-space `L`
(`Module.Finite.of_injective` on `IsScalarTower.toAlgHom F E L`, injective because `E`
is a field); `(←)` is `Module.Finite.trans`. -/
theorem finite_degree_iff :
    Module.Finite F L ↔ Module.Finite E L ∧ Module.Finite F E := by
  constructor
  · intro h
    exact ⟨Module.Finite.of_restrictScalars_finite F E L,
      Module.Finite.of_injective (IsScalarTower.toAlgHom F E L).toLinearMap
        (injective_of_field _)⟩
  · rintro ⟨hEL, hFE⟩
    haveI := hEL
    haveI := hFE
    exact Module.Finite.trans (R := F) E L

/-- FT `ef10`, degree formula: when both `E/F` and `L/E` are finite,
`[L:F] = [L:E]·[E:F]` (as a product of natural numbers, via `Module.finrank`). -/
theorem finrank_tower_mul [Module.Finite F E] [Module.Finite E L] :
    Module.finrank F L = Module.finrank F E * Module.finrank E L :=
  (Module.finrank_mul_finrank F E L).symm

/-- FT `ef10`: if `[L:F] < ∞`, then `[L:E] < ∞` and `[E:F] < ∞`, and
`[L:F] = [L:E]·[E:F]`. -/
theorem finrank_mul_of_finite [Module.Finite F L] :
    Module.Finite E L ∧ Module.Finite F E ∧
      Module.finrank F L = Module.finrank F E * Module.finrank E L := by
  obtain ⟨hEL, hFE⟩ := finite_degree_iff (F := F) (E := E) (L := L) |>.mp ‹Module.Finite F L›
  haveI := hEL
  haveI := hFE
  exact ⟨hEL, hFE, finrank_tower_mul⟩

end Extensions

section SubringGeneratedBySubset

variable {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]

/-- Supporting definition for FT `ef13`: the monomials in elements of `S ⊆ E`: all
products `α₁ ⋯ αₙ` of a finite list of elements of `S` (the empty list gives `1`, and
repetitions of an `α ∈ S` give the powers `α^i`). These are the coefficient-free parts
of the sums `Σ a_{i₁…iₙ} α₁^{i₁}⋯αₙ^{iₙ}` of FT `ef13`. -/
def monomials (S : Set E) : Set E :=
  Set.range fun l : List S => (l.map ((↑) : S → E)).prod

/-- Supporting lemma for FT `ef13`: the `F`-span of the monomials in `S` is the `F`-span
of the submonoid generated by `S`, i.e. the underlying `F`-module of `F[S]` (by
`Algebra.adjoin_eq_span`). -/
theorem span_closure_eq_span_monomials (S : Set E) :
    Submodule.span F ↑(Submonoid.closure S) = Submodule.span F (monomials S) := by
  have hle : Submodule.span F (monomials S * monomials S) ≤ Submodule.span F (monomials S) := by
    rw [Submodule.span_le]
    intro m hm
    obtain ⟨u, ⟨l₁, rfl⟩, v, ⟨l₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hm
    exact Submodule.subset_span ⟨l₁ ++ l₂, by simp only [List.map_append, List.prod_append]⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem a ha => exact Submodule.subset_span ⟨[⟨a, ha⟩], by simp⟩
    | one => exact Submodule.subset_span ⟨[], rfl⟩
    | mul x y _ _ hx hy =>
        refine hle ?_
        rw [← Submodule.span_mul_span]
        exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.span_le]
    rintro y ⟨l, rfl⟩
    refine Submodule.subset_span (list_prod_mem (l := l.map ((↑) : S → E)) fun z hz => ?_)
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact Submonoid.subset_closure a.2

/-- FT `ef13`. The ring `F[S]` consists of the elements of `E` expressible as finite
`F`-linear sums of monomials `α₁^{i₁}⋯αₙ^{iₙ}` with `αⱼ ∈ S`: membership in
`Algebra.adjoin F S` is membership in the `F`-span of `FT.monomials S`, the set of all
products of finite lists of elements of `S` (repetitions give the powers `α^i`, and the
empty list gives the pure-constant summand `1`).

Proof: `Algebra.adjoin_eq_span` identifies `F[S]` with the `F`-span of
`Submonoid.closure S`, and `Submonoid.closure S` consists exactly of the finite products
of elements of `S` (induction on `Submonoid.closure_induction` one way,
`Submonoid.list_prod_mem` the other). -/
theorem mem_adjoin_iff_mem_span_monomials (S : Set E) (x : E) :
    x ∈ Algebra.adjoin F S ↔ x ∈ Submodule.span F (monomials S) := by
  have h1 : x ∈ Algebra.adjoin F S ↔ x ∈ Subalgebra.toSubmodule (Algebra.adjoin F S) := Iff.rfl
  rw [h1, Algebra.adjoin_eq_span F S, span_closure_eq_span_monomials]

/-- FT `ef13` (`eq7`), explicit finite-sums form: `x ∈ F[S]` iff `x = Σ_l a_l · monomial(l)`
for some finitely supported coefficient function `c : List S →₀ F` (each summand is a
monomial `α₁^{i₁}⋯αₙ^{iₙ}` with `αⱼ ∈ S` and coefficient `a_l ∈ F`). -/
theorem mem_adjoin_iff_exists_finsupp (S : Set E) (x : E) :
    x ∈ Algebra.adjoin F S ↔
      ∃ c : List S →₀ F, (c.sum fun l a => a • (l.map ((↑) : S → E)).prod) = x := by
  rw [mem_adjoin_iff_mem_span_monomials]
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- FT `ef14`. Let `R` be an integral domain containing a subfield `F` (as a subring).
If `R` is finite-dimensional as an `F`-vector space, then it is a field. -/
theorem isField_of_isDomain_of_finiteDimensional (F R : Type*) [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] [FiniteDimensional F R] : IsField R :=
  IsField.of_isDomain_of_finite F R

end SubringGeneratedBySubset

end FT
