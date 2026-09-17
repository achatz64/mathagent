import Extlib.GroupTheory.Mil21
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Localization.Rat
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.AlgebraicCard
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

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

AUDIT-GAP (full documentation audit, 2026-09-17, minor): the documentation
standard requires every theorem docstring to document the ideas entering the
proof, or to declare the proof trivial when only unpacking/repacking occurs.
The following docstrings state the theorem but do neither:

- trivial/delegation proofs (add "the proof is trivial" or name the delegated
  fact): `isField_iff_forall_ideal_eq_bot_or_eq_top`,
  `aeval_eq_eval_map_algebraMap`,
  `num_dvd_coeff_zero_and_den_dvd_coeff_natDegree'`, `monic_factor_eq_map`,
  `eisenstein_irreducible_int`, `finrank_tower_mul`, `finrank_mul_of_finite`,
  `mem_adjoin_iff_exists_finsupp`, `isField_of_isDomain_of_finiteDimensional`,
  `isAlgebraic_of_finite`, `finiteType_of_finite`,
  `finite_of_generated_by_finite_algebraic`,
  `finite_iff_algebraic_and_finiteType`, `isAlgebraic_tower_trans`,
  `isAlgClosure_of_isAlgClosed_of_isAlgebraic`,
  `isAlgClosed_of_isAlgebraic_of_splits`,
  `isAlgClosed_and_isAlgebraic_intermediateFieldIsAlgebraic`;
- proofs with a genuine idea that the docstring omits (add the textbook proof
  idea): `degree_pos_of_nonunit_dvd_of_isPrimitive` (non-unit divisor of a
  primitive polynomial has positive degree, else it is a constant dividing the
  content), `exists_factorization_of_map_of_isPrimitive` (irreducibility of
  the mapped primitive polynomial would contradict the hypothesis, so the
  integer factorization exists and its factors have positive degree by the
  auxiliary lemma), `exists_factorization_of_map` (factor out the content,
  apply the primitive-step auxiliary to the primitive part, absorb the content
  as a unit factor), `span_closure_eq_span_monomials` (products of monomials
  are monomials, so one span is closed under multiplication; conversely
  generators of the submonoid are monomials),
  `isField_of_subring_of_isAlgebraic` (R is closed under polynomial
  evaluation, and the inverse of a nonzero algebraic element is a polynomial
  in it), `isAlgClosed_iff_exists_root` (it suffices to test irreducible
  polynomials, which have positive degree),
  `isAlgClosed_iff_irreducible_degree_eq_one` (nonconstant polynomials have
  irreducible factors, of degree 1 by hypothesis, hence roots),
  `isAlgClosed_iff_algebraMap_surjective_of_finite` (test the quotient
  `k[X]/(q)` for an irreducible factor `q` of `p`; clause (4) forces a root
  back into `k`).

Excluded from this list: `mem_intermediateFieldIsAlgebraic`,
`coe_intermediateFieldIsAlgebraic`,
`isAlgClosure_iff_isAlgClosed_and_isAlgebraic` (already flagged by the
per-declaration AUDIT-GAP at `mem_intermediateFieldIsAlgebraic` below) and
the docstrings already carrying a proof-idea account (`num_dvd_coeff_zero_and_den_dvd_coeff_natDegree`,
`finite_degree_iff`, `mem_adjoin_iff_mem_span_monomials`,
`liouville_transcendental`, `isAlgClosure_intermediateFieldIsAlgebraic`,
`eisenstein_irreducible`, and the sf11/ac3 construction docstrings).
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
- `ef11`, `ef12` (examples: concrete extensions `ℝ[x]` for `x² + 1`, `ℚ[x]`
  for `x³ - 3x - 1`): instances of the quotient-ring construction
  (`AdjoinRoot`) and the degree computation; omitted as examples.
- `ef15`, `ef16` (examples: `ℚ[π]`, `ℚ(π)`): instances of
  `mem_adjoin_iff_exists_finsupp` below; `ℚ(π)` additionally illustrates the
  field of fractions of the adjoin.
- `ef17` (example: minimal polynomial of a root of `X³ - 3X - 1`): instance
  of the monic-irreducible-root characterization of minimal polynomials.
- `ef18` (remark: PARI/GP computations): computer-algebra illustration;
  omitted.
- Unlabeled prose following `ef7` in the source: the remark that the last
  three propositions hold "mutatis mutandis" with `ℤ` replaced by a UFD `R`
  carries no stable label and is omitted as a generalization beyond the
  stated scope; the general UFD route is available upstream through Mathlib's
  content/Gauss API (`Polynomial.GaussLemma.lean`, prime-ideal Eisenstein
  criterion `Polynomial.irreducible_of_eisenstein_criterion`).

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

/-- FT `ef6` (auxiliary).  A non-unit divisor of a primitive polynomial in `ℤ[X]`
has positive degree. -/
theorem degree_pos_of_nonunit_dvd_of_isPrimitive {P : ℤ[X]} (hP : P.IsPrimitive)
    {a : ℤ[X]} (ha0 : a ≠ 0) (ha : ¬IsUnit a) (hdvd : a ∣ P) : 0 < a.degree := by
  by_contra hneg
  rcases lt_or_eq_of_le ((Polynomial.zero_le_degree_iff).mpr ha0) with hcontra | hdeg
  · exact hneg hcontra
  have hC : a = C (a.coeff 0) := Polynomial.eq_C_of_degree_eq_zero hdeg.symm
  refine ha ?_
  rw [hC]
  exact Polynomial.isUnit_C.mpr
    ((Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hP) (a.coeff 0) (hC ▸ hdvd))

/-- FT `ef6` (auxiliary, primitive step).  If a primitive polynomial `P ∈ ℤ[X]` factors
nontrivially in `ℚ[X]`, then it factors nontrivially in `ℤ[X]`. -/
theorem exists_factorization_of_map_of_isPrimitive {P : ℤ[X]} (hP : P.IsPrimitive)
    {p q : ℚ[X]} (hp : 0 < p.degree) (hq : 0 < q.degree)
    (h : Polynomial.map (Int.castRingHom ℚ) P = p * q) :
    ∃ r s : ℤ[X], P = r * s ∧ 0 < r.degree ∧ 0 < s.degree := by
  have hnotmap : ¬Irreducible (Polynomial.map (Int.castRingHom ℚ) P) := fun Hirr =>
    (Hirr.isUnit_or_isUnit h).elim
      (fun hu => Polynomial.not_isUnit_of_degree_pos p hp hu)
      (fun hu => Polynomial.not_isUnit_of_degree_pos q hq hu)
  have hPnu : ¬IsUnit P := fun hu => by
    obtain ⟨u, huunit, hPu⟩ := Polynomial.isUnit_iff.mp hu
    have hu0 : (Int.castRingHom ℚ) u ≠ 0 := by
      rw [show (Int.castRingHom ℚ) u = ((u : ℤ) : ℚ) from rfl]
      exact_mod_cast huunit.ne_zero
    have h1 : (p * q).degree = 0 := by
      rw [← h, ← hPu, Polynomial.map_C, Polynomial.degree_C hu0]
    rw [Polynomial.degree_mul] at h1
    have hqz : q ≠ 0 := fun hqz => by simp [hqz] at hq
    have hlt : (0 : WithBot ℕ) < p.degree + q.degree :=
      lt_of_lt_of_le hp
        (le_add_of_nonneg_right ((Polynomial.zero_le_degree_iff).mpr hqz))
    rw [h1] at hlt
    exact lt_irrefl _ hlt
  rcases irreducible_or_factor hPnu with hPirr | ⟨a, b, ha, hb, hab⟩
  · exact absurd
      ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hP).mp hPirr) hnotmap
  · have ha0 : a ≠ 0 := fun hz => hP.ne_zero (by rw [hab, hz, zero_mul])
    have hb0 : b ≠ 0 := fun hz => hP.ne_zero (by rw [hab, hz, mul_zero])
    refine ⟨a, b, hab, ?_, ?_⟩
    · exact degree_pos_of_nonunit_dvd_of_isPrimitive hP ha0 ha (Dvd.intro b hab.symm)
    · exact degree_pos_of_nonunit_dvd_of_isPrimitive hP hb0 hb
        (Dvd.intro a (by rw [mul_comm]; exact hab.symm))

/-- FT `ef6`.  **Gauss's Lemma.**  Let `f ∈ ℤ[X]`.  If `f` factors nontrivially in `ℚ[X]`
(that is, `map (algebraMap ℤ ℚ) f = p * q` with both factors of positive degree), then
`f` factors nontrivially in `ℤ[X]`. -/
theorem exists_factorization_of_map {f : ℤ[X]} {p q : ℚ[X]} (hp : 0 < p.degree)
    (hq : 0 < q.degree) (h : Polynomial.map (algebraMap ℤ ℚ) f = p * q) :
    ∃ r s : ℤ[X], f = r * s ∧ 0 < r.degree ∧ 0 < s.degree := by
  have hf0 : f ≠ 0 := by
    intro hf
    rw [hf, Polynomial.map_zero] at h
    rcases mul_eq_zero.mp h.symm with hz | hz
    · simp [hz] at hp
    · simp [hz] at hq
  have hc0 : f.content ≠ 0 := fun hc => hf0 (Polynomial.content_eq_zero_iff.mp hc)
  have hmap : Polynomial.map (algebraMap ℤ ℚ) f
      = C ((f.content : ℚ)) * Polynomial.map (Int.castRingHom ℚ) f.primPart := by
    conv_lhs => rw [f.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hgpq : Polynomial.map (Int.castRingHom ℚ) f.primPart
      = C ((f.content : ℚ))⁻¹ * p * q := by
    have h1 : C ((f.content : ℚ)) * Polynomial.map (Int.castRingHom ℚ) f.primPart
        = p * q := by
      rw [← hmap]; exact h
    rw [mul_assoc, ← h1, ← mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ (show ((f.content : ℚ)) ≠ 0 by exact_mod_cast hc0), C_1, one_mul]
  have hp' : 0 < (C ((f.content : ℚ))⁻¹ * p).degree := by
    rw [Polynomial.degree_mul,
      Polynomial.degree_C (inv_ne_zero (show ((f.content : ℚ)) ≠ 0 by
        exact_mod_cast hc0)), zero_add]
    exact hp
  obtain ⟨a, b, hab, hadeg, hbdeg⟩ :=
    exists_factorization_of_map_of_isPrimitive (Polynomial.isPrimitive_primPart f)
      hp' hq hgpq
  have hfab : f = C f.content * a * b := by
    conv_lhs => rw [f.eq_C_content_mul_primPart]
    rw [hab, mul_assoc]
  refine ⟨C f.content * a, b, hfab, ?_, hbdeg⟩
  · rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
    exact hadeg

/-- FT `ef6m`.  If `f ∈ ℤ[X]` is monic, then every monic factor `g` of `f` in `ℚ[X]`
lies in `ℤ[X]`: `g = map (algebraMap ℤ ℚ) h` for a (necessarily monic) `h ∈ ℤ[X]`. -/
theorem monic_factor_eq_map {f : ℤ[X]} (hf : f.Monic) {g : ℚ[X]} (hg : g.Monic)
    (hdvd : g ∣ Polynomial.map (algebraMap ℤ ℚ) f) :
    ∃ h : ℤ[X], Polynomial.map (algebraMap ℤ ℚ) h = g := by
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hf hdvd
  refine ⟨h, ?_⟩
  rw [← hh, hg.leadingCoeff, C_1, mul_one]

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

/-- Auxiliary for FT `ef10` (finiteness half): a ring homomorphism out of a field into
a nontrivial ring is injective. Delegates to Mathlib's `RingHom.injective`. -/
private theorem injective_of_field {K S : Type*} [Field K] [Ring S] [Nontrivial S]
    (g : K →+* S) : Function.Injective g := g.injective

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

section AlgebraicElements

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- FT `ef19` (i): if `E/F` is finite, then every element of `E` is algebraic over `F`. -/
theorem isAlgebraic_of_finite [Module.Finite F E] (x : E) : IsAlgebraic F x :=
  IsAlgebraic.of_finite (R := F) x

/-- FT `ef19` (ii): if `E/F` is finite, then `E` is finitely generated (as a field) over `F`,
i.e. `Algebra.FiniteType F E` holds. -/
theorem finiteType_of_finite [Module.Finite F E] : Algebra.FiniteType F E :=
  inferInstance

/-- FT `ef19` (iii): if `E` is generated over `F` by a finite set of algebraic elements,
then `E/F` is finite. -/
theorem finite_of_generated_by_finite_algebraic {s : Set E} (hs : s.Finite)
    (halg : ∀ x ∈ s, IsAlgebraic F x) (hgen : Algebra.adjoin F s = ⊤) : Module.Finite F E := by
  have hf := Algebra.finite_adjoin_of_finite_of_isIntegral hs
    fun x hx => isAlgebraic_iff_isIntegral.mp (halg x hx)
  rw [hgen] at hf
  haveI := hf
  exact Module.Finite.equiv (Subalgebra.topEquiv).toLinearEquiv

/-- FT `ef19`. Let `E ⊃ F` be fields. `E/F` is finite if and only if `E` is algebraic over `F`
and finitely generated (as a field) over `F`. -/
theorem finite_iff_algebraic_and_finiteType :
    Module.Finite F E ↔ (Algebra.IsAlgebraic F E ∧ Algebra.FiniteType F E) := by
  constructor
  · intro hfin
    exact ⟨⟨fun x => isAlgebraic_of_finite x⟩, inferInstance⟩
  · rintro ⟨halg, hfin⟩
    obtain ⟨t, ht⟩ := hfin.out
    have hf := Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
      fun x _ => isAlgebraic_iff_isIntegral.mp (halg.isAlgebraic x)
    rw [ht] at hf
    haveI := hf
    exact Module.Finite.equiv (Subalgebra.topEquiv).toLinearEquiv

/-- FT `ef20` (a): if `E` is algebraic over `F`, then every subring `R` of `E` containing `F`
is a field. -/
theorem isField_of_subring_of_isAlgebraic [Algebra.IsAlgebraic F E] (R : Subring E)
    (hR : ∀ a : F, algebraMap F E a ∈ R) : IsField R := by
  have hmem : ∀ x : E, x ∈ R → ∀ q : Polynomial F,
      Polynomial.eval₂ (algebraMap F E) x q ∈ R := by
    intro x hx q
    induction q using Polynomial.induction_on' with
    | add p r hp hr =>
        rw [Polynomial.eval₂_add]; exact Subring.add_mem _ hp hr
    | monomial n a =>
        rw [Polynomial.eval₂_monomial]; exact Subring.mul_mem _ (hR a) (Subring.pow_mem _ hx n)
  refine ⟨⟨0, 1, by norm_num⟩, mul_comm, fun {x} hx => ?_⟩
  have hxE : (x : E) ≠ 0 := fun h => hx (Subtype.ext h)
  have hint : IsIntegral F (x : E) :=
    isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic (x : E))
  have hinv : (x : E)⁻¹ ∈ Algebra.adjoin F {(x : E)} := IsIntegral.inv_mem_adjoin hint
  obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval (R := F) (x := (x : E)) hinv
  refine ⟨⟨(x : E)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ hxE)⟩
  rw [← hq, Polynomial.aeval_def]
  exact hmem (x : E) x.2 q

/-- FT `ef20` (b): for fields `L ⊃ E ⊃ F`, if `L` is algebraic over `E` and `E` is algebraic
over `F`, then `L` is algebraic over `F`. -/
theorem isAlgebraic_tower_trans {L : Type*} [Field L] [Algebra E L] [Algebra F L]
    [IsScalarTower F E L] (hLE : Algebra.IsAlgebraic E L) (hEF : Algebra.IsAlgebraic F E) :
    Algebra.IsAlgebraic F L :=
  Algebra.IsAlgebraic.trans F E L

end AlgebraicElements

section TranscendentalNumbers

open scoped Nat

/-- FT `ef22`. The set of algebraic numbers is countable.

Delegates to Mathlib's `Algebraic.countable` for the countable domain `ℚ` acting on `ℂ`
(`ℚ[X]` is countable and each nonzero polynomial has finitely many roots). -/
theorem algebraic_numbers_countable : {x : ℂ | IsAlgebraic ℚ x}.Countable :=
  Algebraic.countable ℚ ℂ

/-- FT `ef23`, bridge lemma: a real number transcendental over `ℤ` is transcendental over
`ℚ`.  This is `IsFractionRing.isAlgebraic_iff` for the fraction field `ℚ` of `ℤ`: a
nonzero polynomial in `ℤ[X]` remains nonzero over the fraction field. -/
theorem transcendental_of_transcendental_int {x : ℝ} (h : Transcendental ℤ x) :
    Transcendental ℚ x :=
  fun hq => h ((IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℝ)).mpr hq)

/-- FT `ef23`. **Liouville's theorem**: the number `α = ∑ 1 / 2 ^ (n!)` is transcendental
over `ℚ`.

Milne's `α` is exactly Mathlib's Liouville constant `liouvilleNumber 2` (the defining
`tsum` matches definitionally, hence `rfl`), for which Mathlib proves
`Transcendental ℤ` via `transcendental_liouvilleNumber`; the bridge lemma
`FT.transcendental_of_transcendental_int` transfers this to `ℚ`. -/
theorem liouville_transcendental :
    Transcendental ℚ (∑' n : ℕ, (1 / (2 : ℝ) ^ ((n)! : ℕ))) :=
  transcendental_of_transcendental_int (transcendental_liouvilleNumber (m := 2) le_rfl)

end TranscendentalNumbers

/-!
### Algebraically closed fields

AUDIT-GAP (audit 3646858, provenance/scope audit, minor): the chapter-1 aside
`ac3a` (historical aside on Steinitz 1910) is omitted by the provenance scope
but has no scope citation in this file, unlike the other omitted expositional
items of the chapter (see the ef0-ef31 cluster of scope notes above).

Scope note: `sf10`'s source phrasing "hence an algebraic closure of `F`" is
exposed through `isAlgClosure_of_isAlgebraic_of_splits` alongside the bare
`isAlgClosed_of_isAlgebraic_of_splits`.
-/

section AlgebraicallyClosedFields

/-- FT `ac1`, clause (1). A field `Ω` is algebraically closed if and only if every
nonconstant polynomial in `Ω[X]` splits in `Ω[X]`.  This is Mathlib's definition
`IsAlgClosed Ω` (which asks that *every* polynomial split), restricted to nonconstant
polynomials: constant (and zero) polynomials split automatically. -/
theorem isAlgClosed_iff_splits_nonconstant (k : Type*) [Field k] :
    IsAlgClosed k ↔ ∀ p : k[X], p.degree ≠ 0 → p.Splits := by
  constructor
  · exact fun _ p hp => IsAlgClosed.splits p
  · intro h
    refine ⟨fun p => ?_⟩
    by_cases hp : p.degree ≠ 0
    · exact h p hp
    · exact Polynomial.Splits.of_degree_le_zero
        (le_of_not_gt fun h0 => hp (ne_of_gt h0))

/-- FT `ac1`, clause (2). A field `Ω` is algebraically closed if and only if every
nonconstant polynomial in `Ω[X]` has a root in `Ω`.  Mathlib packages both directions as
`IsAlgClosed.exists_root` and `IsAlgClosed.of_exists_root`. -/
theorem isAlgClosed_iff_exists_root (k : Type*) [Field k] :
    IsAlgClosed k ↔ ∀ p : k[X], p.degree ≠ 0 → ∃ x, p.eval x = 0 := by
  constructor
  · exact fun h p hp => h.exists_root p hp
  · intro h
    exact IsAlgClosed.of_exists_root k fun p _ hp =>
      h p (Polynomial.degree_pos_of_irreducible hp).ne'

/-- FT `ac1`, clause (3). A field `Ω` is algebraically closed if and only if the
irreducible polynomials in `Ω[X]` are exactly those of degree `1`. -/
theorem isAlgClosed_iff_irreducible_degree_eq_one (k : Type*) [Field k] :
    IsAlgClosed k ↔ ∀ p : k[X], (Irreducible p ↔ p.degree = 1) := by
  constructor
  · intro h p
    exact ⟨fun hirr => h.degree_eq_one_of_irreducible k hirr,
      fun hd1 => Polynomial.irreducible_of_degree_eq_one hd1⟩
  · intro h
    refine (isAlgClosed_iff_exists_root k).mpr fun p hp => ?_
    rcases eq_or_ne p 0 with hp0 | hp0
    · exact ⟨0, by rw [hp0]; simp⟩
    -- every nonconstant `p` has an irreducible factor `q`; by (3), `deg q = 1`, so `q`,
    -- hence `p`, has a root in `k`
    obtain ⟨q, hqirr, hpq⟩ := WfDvdMonoid.exists_irreducible_factor
      (fun hu => hp (Polynomial.degree_eq_zero_of_isUnit hu)) hp0
    have hq1 : q.degree = 1 := (h q).1 hqirr
    obtain ⟨x, hx⟩ := (Polynomial.Splits.of_degree_eq_one hq1).exists_eval_eq_zero
      (by simp [hq1])
    obtain ⟨r, rfl⟩ := hpq
    exact ⟨x, by rw [Polynomial.eval_mul, hx, zero_mul]⟩

/-- FT `ac1`, clause (4), forward direction (at full universe generality): if `Ω` is
algebraically closed, then every field of finite degree over `Ω` equals `Ω` (encoded
as: the algebra map `Ω → K` is surjective, i.e. `K` is generated by `Ω`). -/
theorem algebraMap_surjective_of_isAlgClosed {k K : Type*} [Field k] [IsAlgClosed k]
    [Field K] [Algebra k K] [Module.Finite k K] : Function.Surjective (algebraMap k K) := by
  haveI : Algebra.IsIntegral k K := Algebra.IsIntegral.of_finite k K
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2

/-- FT `ac1`, clause (4). A field `Ω` is algebraically closed if and only if every
field of finite degree over `Ω` equals `Ω` (encoded as: for every field extension `K`
of `Ω` with `[K : Ω] < ∞`, the algebra map `Ω → K` is surjective, i.e. `K` is generated
by `Ω`).  The equivalence quantifies over extensions `K` in the universe of `Ω`, which
matches the source where all fields live in one universe; the forward direction is
available at full generality as `FT.algebraMap_surjective_of_isAlgClosed`. -/
theorem isAlgClosed_iff_algebraMap_surjective_of_finite.{u} (k : Type u) [Field k] :
    IsAlgClosed k ↔ ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K],
      Function.Surjective (algebraMap k K) := by
  constructor
  · intro _ K _ _ _
    exact algebraMap_surjective_of_isAlgClosed (k := k) (K := K)
  · intro h
    refine (isAlgClosed_iff_exists_root k).mpr fun p hp => ?_
    rcases eq_or_ne p 0 with hp0 | hp0
    · exact ⟨0, by rw [hp0]; simp⟩
    -- an irreducible factor `q` of `p`; the quotient `k[X]/(q)` is a finite field
    -- extension of `k` in which `q` has a root; clause (4) pulls that root back to `k`
    obtain ⟨q, hqirr, hpq⟩ := WfDvdMonoid.exists_irreducible_factor
      (fun hu => hp (Polynomial.degree_eq_zero_of_isUnit hu)) hp0
    have hqd : q.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hqirr).ne'
    haveI : Fact (Irreducible q) := ⟨hqirr⟩
    haveI : Module.Finite k (AdjoinRoot q) := (AdjoinRoot.powerBasis hqirr.ne_zero).finite
    obtain ⟨a, ha⟩ := h (AdjoinRoot q) (AdjoinRoot.root q)
    have hae : Polynomial.aeval (algebraMap k (AdjoinRoot q) a) q = 0 := by
      rw [ha, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hqa : q.eval a = 0 := by
      refine (AdjoinRoot.of.injective_of_degree_ne_zero hqd) ?_
      rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        hae, map_zero]
    obtain ⟨r, rfl⟩ := hpq
    exact ⟨a, by rw [Polynomial.eval_mul, hqa, zero_mul]⟩

/-- FT `ac2`. (a) "Algebraically closed" is Mathlib's `IsAlgClosed`, characterized by the
four equivalent conditions of FT `ac1` above.  (b) A field `Ω` is an algebraic closure of
a subfield `F` if and only if it is algebraically closed and algebraic over `F`: this is
Mathlib's `IsAlgClosure F Ω` (whose `IsTorsionFree F Ω` side condition is automatic for a
field base). -/
theorem isAlgClosure_iff_isAlgClosed_and_isAlgebraic (F : Type*) [Field F] (Ω : Type*)
    [Field Ω] [Algebra F Ω] : IsAlgClosure F Ω ↔ IsAlgClosed Ω ∧ Algebra.IsAlgebraic F Ω :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- FT `ac2` (b), assembly direction: an algebraically closed field that is algebraic
over the subfield `F` is an algebraic closure of `F`. -/
theorem isAlgClosure_of_isAlgClosed_of_isAlgebraic {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] (h1 : IsAlgClosed Ω) (h2 : Algebra.IsAlgebraic F Ω) : IsAlgClosure F Ω :=
  ⟨h1, h2⟩

/-- FT `sf10`. If `Ω` is algebraic over `F` and every polynomial `f ∈ F[X]` splits in
`Ω[X]`, then `Ω` is an algebraic closure of `F`. -/
theorem isAlgClosure_of_isAlgebraic_of_splits {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [Algebra.IsAlgebraic F Ω] (h : ∀ f : F[X], (f.map (algebraMap F Ω)).Splits) :
    IsAlgClosure F Ω := by
  haveI : Algebra.IsIntegral F Ω :=
    ⟨fun x => isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic x)⟩
  exact IsAlgClosure.of_splits (R := F) (K := Ω) fun p _ _ => h p

/-- FT `sf10`. If `Ω` is algebraic over `F` and every polynomial `f ∈ F[X]` splits in
`Ω[X]`, then `Ω` is algebraically closed (hence an algebraic closure of `F`). -/
theorem isAlgClosed_of_isAlgebraic_of_splits {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [Algebra.IsAlgebraic F Ω] (h : ∀ f : F[X], (f.map (algebraMap F Ω)).Splits) :
    IsAlgClosed Ω :=
  (isAlgClosure_of_isAlgebraic_of_splits h).isAlgClosed

/-- FT `sf11`. Let `Ω ⊃ F` be fields; the set `{α ∈ Ω | α algebraic over F}` is a field:
it is the underlying set of the intermediate field `FT.intermediateFieldIsAlgebraic F Ω`
(Mathlib's `Subalgebra.algebraicClosure F Ω`, the subalgebra of elements of `Ω` algebraic
over `F`, turned into an intermediate field). -/
noncomputable def intermediateFieldIsAlgebraic (F : Type*) [Field F] (Ω : Type*) [Field Ω]
    [Algebra F Ω] : IntermediateField F Ω :=
  Subalgebra.IsAlgebraic.toIntermediateField (S := Subalgebra.algebraicClosure F Ω)
    (fun _ hx => hx)

/-- FT `sf11`. Membership in `FT.intermediateFieldIsAlgebraic F Ω` is exactly being
algebraic over `F`.

AUDIT-GAP (audit 3646858, documentation audit, minor): the proof is `Iff.rfl`.
Per the documentation standard this docstring should declare the proof trivial,
as should the docstrings of `isAlgClosure_iff_isAlgClosed_and_isAlgebraic` and
`coe_intermediateFieldIsAlgebraic` (unpacking/repacking proofs). -/
theorem mem_intermediateFieldIsAlgebraic {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {x : Ω} : x ∈ intermediateFieldIsAlgebraic F Ω ↔ IsAlgebraic F x := by
  unfold intermediateFieldIsAlgebraic
  exact Iff.rfl

/-- FT `sf11`, set-level form: the set `{α ∈ Ω | α algebraic over F}` is the underlying
set of the intermediate field `FT.intermediateFieldIsAlgebraic F Ω`, hence is a field. -/
theorem coe_intermediateFieldIsAlgebraic {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] :
    SetLike.coe (intermediateFieldIsAlgebraic F Ω) = {α : Ω | IsAlgebraic F α} := by
  ext a
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  exact mem_intermediateFieldIsAlgebraic

/-- FT `ac3`. Let `Ω` be an algebraically closed field and `F` a subfield. The algebraic
closure `E` of `F` in `Ω` — realized as the intermediate field
`FT.intermediateFieldIsAlgebraic F Ω` of elements of `Ω` algebraic over `F` (FT `sf11`) —
is an algebraic closure of `F`, i.e. `E` is algebraically closed (FT `sf10` route: every
monic irreducible polynomial over `F` splits in `Ω`, and its roots are algebraic over
`F`, hence lie in `E`) and algebraic over `F`. -/
theorem isAlgClosure_intermediateFieldIsAlgebraic (F : Type*) [Field F] (Ω : Type*)
    [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    IsAlgClosure F (intermediateFieldIsAlgebraic F Ω) := by
  have hE : ∀ x : intermediateFieldIsAlgebraic F Ω, IsAlgebraic F (x : Ω) := fun x =>
    (Subalgebra.mem_algebraicClosure F Ω).mp x.property
  haveI : Algebra.IsIntegral F (intermediateFieldIsAlgebraic F Ω) :=
    ⟨fun x => (IntermediateField.coe_isIntegral_iff (R := F)).mp
      (isAlgebraic_iff_isIntegral.mp (hE x))⟩
  refine IsAlgClosure.of_splits (R := F) (K := intermediateFieldIsAlgebraic F Ω) fun p _ hp => ?_
  refine Polynomial.Splits.of_splits_map_of_injective
    (i := algebraMap (intermediateFieldIsAlgebraic F Ω) Ω) ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext hxy
  · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact IsAlgClosed.splits _
  · intro β hβ
    have hcomp : (Polynomial.map (algebraMap F (intermediateFieldIsAlgebraic F Ω)) p).map
        (algebraMap (intermediateFieldIsAlgebraic F Ω) Ω) =
        Polynomial.map (algebraMap F Ω) p := by
      rw [Polynomial.map_map, IsScalarTower.algebraMap_eq F
        (intermediateFieldIsAlgebraic F Ω) Ω]
    have hroot : Polynomial.eval β (Polynomial.map (algebraMap F Ω) p) = 0 := by
      rw [← hcomp]
      exact (Polynomial.mem_roots'.mp hβ).2
    refine ⟨⟨β, ?_⟩, rfl⟩
    exact ⟨p, hp.ne_zero, by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot⟩

/-- FT `ac3`, unpacked form: the algebraic closure `E` of `F` in the algebraically closed
field `Ω` is algebraically closed and algebraic over `F`. -/
theorem isAlgClosed_and_isAlgebraic_intermediateFieldIsAlgebraic (F : Type*) [Field F]
    (Ω : Type*) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    IsAlgClosed (intermediateFieldIsAlgebraic F Ω) ∧
      Algebra.IsAlgebraic F (intermediateFieldIsAlgebraic F Ω) :=
  (isAlgClosure_iff_isAlgClosed_and_isAlgebraic F _).mp
    (isAlgClosure_intermediateFieldIsAlgebraic F Ω)

end AlgebraicallyClosedFields

end FT
