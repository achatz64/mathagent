import Extlib.GroupTheory.Mil21
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Localization.Rat
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.AlgebraicCard
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

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

AUDIT-GAP (full audit of commit 22eea5c, coverage audit, expected for
work-in-progress): the target covers chapter 1 only.  Of the 24 chapter-1
theorem-like labels, 16 are mentioned; `ef24`-`ef31` (straight-edge-and-compass
section) are pending.  Chapters 2-7 (splitting fields, fundamental theorem of
Galois theory, ...; the `ft`/`sf`/`te`/`ag`/`cg`/`ig`/`ca` label clusters) are
entirely absent from the target although in scope per the provenance `scope`
field (which omits only exercises, solutions, and expositional material).  To
be recorded in the final ledger as pending or as AUDIT-DEFERRED.
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
- `ac3a` (aside: historical remark on Steinitz 1910): historical aside;
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
ideals other than `(0)` and `R`.  Key idea: a field has no ideals other than
`(0)` and `R` because every nonzero ideal contains a unit, and conversely a
nonzero commutative ring whose only ideals are `(0)` and `R` makes every
nonzero element a unit.  The proof is a trivial unpacking of Mathlib's
`Ring.isField_iff_isSimpleOrder_ideal` (forward) and of the contrapositive
characterization of non-fields by a proper intermediate ideal (backward). -/
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
"`r` is a root of `f : ℤ[X]`".  The proof is trivial: it unfolds
`Polynomial.aeval_def` and `Polynomial.eval_map`. -/
theorem aeval_eq_eval_map_algebraMap (f : ℤ[X]) (r : ℚ) :
    Polynomial.aeval r f = Polynomial.eval r (Polynomial.map (algebraMap ℤ ℚ) f) := by
  rw [Polynomial.aeval_def, Polynomial.eval_map]

/-- FT `ef4`, `eval`-form hypothesis: `r` is a root of `f` viewed in `ℚ[X]` via the
inclusion `ℤ → ℚ`.  The proof is trivial: it rewrites the hypothesis to the
`aeval` form with the bridge lemma `FT.aeval_eq_eval_map_algebraMap` and applies
the `aeval`-form theorem. -/
theorem num_dvd_coeff_zero_and_den_dvd_coeff_natDegree' {f : ℤ[X]} {r : ℚ}
    (hr : Polynomial.eval r (Polynomial.map (algebraMap ℤ ℚ) f) = 0) :
    (r.num : ℤ) ∣ f.coeff 0 ∧ (r.den : ℤ) ∣ f.coeff f.natDegree := by
  rw [← aeval_eq_eval_map_algebraMap] at hr
  exact num_dvd_coeff_zero_and_den_dvd_coeff_natDegree hr

/-- FT `ef6` (auxiliary).  A non-unit divisor of a primitive polynomial in `ℤ[X]`
has positive degree.

Proof idea: a degree-zero divisor is a constant `C c`; a constant dividing `P`
divides every coefficient of `P`, hence the content of the primitive `P` —
which forces `c` to be a unit, contradiction.  (Mathlib's
`Polynomial.isPrimitive_iff_isUnit_of_C_dvd` packages the last step.) -/
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
nontrivially in `ℚ[X]`, then it factors nontrivially in `ℤ[X]`.

Proof idea: the mapped `P` is not irreducible (both factors have positive
degree, hence are non-units), and `P` is not a unit (degree drops under the
map would force `p * q` to have degree zero); by Gauss's bridge
(`Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`) `P` itself
factors in `ℤ[X]`, and the auxiliary lemma
`FT.degree_pos_of_nonunit_dvd_of_isPrimitive` upgrades "non-unit factor" to
"positive degree". -/
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
`f` factors nontrivially in `ℤ[X]`.

Proof idea: factor out the content, `f = C f.content * f.primPart`; after
absorbing the content as the unit `C f.content⁻¹` in `ℚ[X]`, the given
factorization transfers to the primitive part, to which the primitive-step
auxiliary applies; multiplying the content factor back into one factor
preserves positive degrees. -/
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
lies in `ℤ[X]`: `g = map (algebraMap ℤ ℚ) h` for a (necessarily monic) `h ∈ ℤ[X]`.
This is a delegation wrapper: Mathlib's `IsIntegrallyClosed.eq_map_mul_C_of_dvd`
states the factorization with an explicit scalar `C g.leadingCoeff`; the proof
trivially simplifies that scalar away using the monicity of `g`. -/
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
which reduces irreducibility over `ℚ` to irreducibility over `ℤ` by Gauss's lemma.

Proof idea: apply Mathlib's general prime-ideal Eisenstein criterion
(`Polynomial.irreducible_of_eisenstein_criterion`) to the prime ideal `pℤ` —
its four hypotheses translate the divisibility conditions (i)-(iii) of the
source; the remaining bookkeeping (f nonzero, positive degree) is trivial.
The `f.IsPrimitive` hypothesis is genuinely necessary: irreducibility in
`ℤ[X]` fails for non-primitive input (e.g. `2X² + 6X + 6` at `p = 3`). -/
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
`[L:F] = [L:E]·[E:F]` (as a product of natural numbers, via `Module.finrank`).
The proof is trivial: it is Mathlib's `Module.finrank_mul_finrank`, stated
symmetrically. -/
theorem finrank_tower_mul [Module.Finite F E] [Module.Finite E L] :
    Module.finrank F L = Module.finrank F E * Module.finrank E L :=
  (Module.finrank_mul_finrank F E L).symm

/-- FT `ef10`: if `[L:F] < ∞`, then `[L:E] < ∞` and `[E:F] < ∞`, and
`[L:F] = [L:E]·[E:F]`.  The proof is trivial: it combines the two directions
of `FT.finite_degree_iff` with the degree formula `FT.finrank_tower_mul`. -/
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
`Algebra.adjoin_eq_span`).

Proof idea: products of monomials are monomials (concatenating the witness
lists), so the span of the monomials is closed under multiplication and
contains the submonoid; conversely every generator of the submonoid — i.e.
every element of `S` — is a monomial, so the two spans coincide by induction
on `Submonoid.closure_induction`. -/
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
monomial `α₁^{i₁}⋯αₙ^{iₙ}` with `αⱼ ∈ S` and coefficient `a_l ∈ F`).  The proof
is trivial: it rewrites the left side with
`FT.mem_adjoin_iff_mem_span_monomials` and applies Mathlib's
`Finsupp.mem_span_range_iff_exists_finsupp`. -/
theorem mem_adjoin_iff_exists_finsupp (S : Set E) (x : E) :
    x ∈ Algebra.adjoin F S ↔
      ∃ c : List S →₀ F, (c.sum fun l a => a • (l.map ((↑) : S → E)).prod) = x := by
  rw [mem_adjoin_iff_mem_span_monomials]
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- FT `ef14`. Let `R` be an integral domain containing a subfield `F` (as a subring).
If `R` is finite-dimensional as an `F`-vector space, then it is a field.  This is a pure
delegation to Mathlib's `IsField.of_isDomain_of_finite`; the proof is trivial. -/
theorem isField_of_isDomain_of_finiteDimensional (F R : Type*) [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] [FiniteDimensional F R] : IsField R :=
  IsField.of_isDomain_of_finite F R

end SubringGeneratedBySubset

section AlgebraicElements

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- FT `ef19` (i): if `E/F` is finite, then every element of `E` is algebraic over `F`.
This is a pure delegation to Mathlib's `IsAlgebraic.of_finite`; the proof is trivial. -/
theorem isAlgebraic_of_finite [Module.Finite F E] (x : E) : IsAlgebraic F x :=
  IsAlgebraic.of_finite (R := F) x

/-- FT `ef19` (ii): if `E/F` is finite, then `E` is finitely generated (as a field) over `F`,
i.e. `Algebra.FiniteType F E` holds.  The proof is trivial: Mathlib's instance
`Module.Finite → Algebra.FiniteType` applies directly. -/
theorem finiteType_of_finite [Module.Finite F E] : Algebra.FiniteType F E :=
  inferInstance

/-- FT `ef19` (iii): if `E` is generated over `F` by a finite set of algebraic elements,
then `E/F` is finite.  The proof is a trivial repackaging: Mathlib's
`Algebra.finite_adjoin_of_finite_of_isIntegral` gives finiteness of the adjoin of the
finite generating set, and the hypothesis `Algebra.adjoin F s = ⊤` transfers it to `E`
along the `Subalgebra.topEquiv` linear equivalence. -/
theorem finite_of_generated_by_finite_algebraic {s : Set E} (hs : s.Finite)
    (halg : ∀ x ∈ s, IsAlgebraic F x) (hgen : Algebra.adjoin F s = ⊤) : Module.Finite F E := by
  have hf := Algebra.finite_adjoin_of_finite_of_isIntegral hs
    fun x hx => isAlgebraic_iff_isIntegral.mp (halg x hx)
  rw [hgen] at hf
  haveI := hf
  exact Module.Finite.equiv (Subalgebra.topEquiv).toLinearEquiv

/-- FT `ef19`. Let `E ⊃ F` be fields. `E/F` is finite if and only if `E` is algebraic over `F`
and finitely generated (as a field) over `F`.  The proof is a trivial assembly of the
three clause theorems `FT.isAlgebraic_of_finite`, `FT.finiteType_of_finite`, and
`FT.finite_of_generated_by_finite_algebraic`. -/
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
is a field.

Proof idea: `R` is closed under polynomial evaluation at its elements with
coefficients in `F` (induction on polynomials); for nonzero `x ∈ R`,
integrality of `x` over `F` puts `x⁻¹ ∈ F[x]` in the adjoin
(`IsIntegral.inv_mem_adjoin`), and `F[x]`-membership is witnessed by a
polynomial, whose evaluation lies in `R` — so `x⁻¹ ∈ R`. -/
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
over `F`, then `L` is algebraic over `F`.  This is a pure delegation to Mathlib's
`Algebra.IsAlgebraic.trans`; the proof is trivial. -/
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
`IsAlgClosed.exists_root` and `IsAlgClosed.of_exists_root`.

Proof idea (⇐): it suffices to test irreducible polynomials, since every
nonconstant polynomial has an irreducible factor; irreducibles have positive
degree, so Mathlib's `IsAlgClosed.of_exists_root` applies. -/
theorem isAlgClosed_iff_exists_root (k : Type*) [Field k] :
    IsAlgClosed k ↔ ∀ p : k[X], p.degree ≠ 0 → ∃ x, p.eval x = 0 := by
  constructor
  · exact fun h p hp => h.exists_root p hp
  · intro h
    exact IsAlgClosed.of_exists_root k fun p _ hp =>
      h p (Polynomial.degree_pos_of_irreducible hp).ne'

/-- FT `ac1`, clause (3). A field `Ω` is algebraically closed if and only if the
irreducible polynomials in `Ω[X]` are exactly those of degree `1`.

Proof idea (⇐): a nonconstant polynomial has an irreducible factor; by the
hypothesis that factor has degree `1`, hence a root in `Ω`, which is then a
root of the original polynomial. -/
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
available at full generality as `FT.algebraMap_surjective_of_isAlgClosed`.

Proof idea (⇐): test an irreducible factor `q` of a nonconstant `p`; the
quotient `k[X]/(q)` is a finite extension of `k` in which `q` has a root
(the class of `X`); clause (4) forces that root to come from `k`, and
pulling back along the quotient map embeds it as a root of `q`, hence of `p`,
in `k`. -/
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
field base).  The proof is trivial: it unpacks the `IsAlgClosure` structure fields. -/
theorem isAlgClosure_iff_isAlgClosed_and_isAlgebraic (F : Type*) [Field F] (Ω : Type*)
    [Field Ω] [Algebra F Ω] : IsAlgClosure F Ω ↔ IsAlgClosed Ω ∧ Algebra.IsAlgebraic F Ω :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- FT `ac2` (b), assembly direction: an algebraically closed field that is algebraic
over the subfield `F` is an algebraic closure of `F`.  The proof is trivial: it
assembles the `IsAlgClosure` structure from the two components. -/
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
`Ω[X]`, then `Ω` is algebraically closed (hence an algebraic closure of `F`).
The proof is trivial: it extracts the `IsAlgClosed` component of
`FT.isAlgClosure_of_isAlgebraic_of_splits`. -/
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
algebraic over `F`.  The proof is trivial: the definition unfolds to Mathlib's
subalgebra-of-algebraic-elements membership, which is definitionally the same
predicate. -/
theorem mem_intermediateFieldIsAlgebraic {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {x : Ω} : x ∈ intermediateFieldIsAlgebraic F Ω ↔ IsAlgebraic F x := by
  unfold intermediateFieldIsAlgebraic
  exact Iff.rfl

/-- FT `sf11`, set-level form: the set `{α ∈ Ω | α algebraic over F}` is the underlying
set of the intermediate field `FT.intermediateFieldIsAlgebraic F Ω`, hence is a field.
The proof is trivial: it is the extensionality unpacking of the membership
characterization `FT.mem_intermediateFieldIsAlgebraic`. -/
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
field `Ω` is algebraically closed and algebraic over `F`.  The proof is trivial: it
unpacks `FT.isAlgClosure_intermediateFieldIsAlgebraic` with the `ac2`
characterization. -/
theorem isAlgClosed_and_isAlgebraic_intermediateFieldIsAlgebraic (F : Type*) [Field F]
    (Ω : Type*) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    IsAlgClosed (intermediateFieldIsAlgebraic F Ω) ∧
      Algebra.IsAlgebraic F (intermediateFieldIsAlgebraic F Ω) :=
  (isAlgClosure_iff_isAlgClosed_and_isAlgebraic F _).mp
    (isAlgClosure_intermediateFieldIsAlgebraic F Ω)

end AlgebraicallyClosedFields

/-!
### Constructions with straight-edge and compass
-/

section ConstructionsStraightEdgeCompass

open Polynomial
open scoped IntermediateField

/-- Helper for FT `ef24`: on the real line, `x² + y² = 0` forces `x = y = 0`. -/
theorem ef24_sq_add_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have h1 : 0 ≤ y ^ 2 := sq_nonneg y
  have hx : x ^ 2 ≤ 0 := by linarith
  have hy : y ^ 2 ≤ 0 := by linarith [sq_nonneg x]
  exact ⟨sq_eq_zero_iff.mp (le_antisymm hx (sq_nonneg x)), sq_eq_zero_iff.mp (le_antisymm hy (sq_nonneg y))⟩

/-- Helper for FT `ef24`: `2` and `4` belong to every subfield of `ℝ`. -/
theorem ef24_two_mem {F : Subfield ℝ} : (2 : ℝ) ∈ F := by
  have h : (2 : ℝ) = 1 + 1 := by norm_num
  rw [h]; exact Subfield.add_mem F (Subfield.one_mem F) (Subfield.one_mem F)

/-- Helper for FT `ef24`: `4` belongs to every subfield of `ℝ`. -/
theorem ef24_four_mem {F : Subfield ℝ} : (4 : ℝ) ∈ F := by
  have h : (4 : ℝ) = 2 + 2 := by norm_num
  rw [h]; exact Subfield.add_mem F ef24_two_mem ef24_two_mem

/-- Helper for FT `ef24`: two nonproportional nonzero pairs with vanishing determinant of
`[[a, b], [a', b']]` cannot exist: if `a b' = a' b` and `(a, b) ≠ 0 ≠ (a', b')`, then `(a', b')`
is a nonzero multiple of `(a, b)`. -/
theorem ef24_exists_prop_coeff {a a' b b' : ℝ} (ha : a ≠ 0 ∨ b ≠ 0) (ha' : a' ≠ 0 ∨ b' ≠ 0) (hD : a * b' = a' * b) : ∃ k : ℝ, a' = k * a ∧ b' = k * b ∧ k ≠ 0 := by
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := ha.elim (absurd ha0) id
    have ha'0 : a' = 0 := by rw [ha0, zero_mul] at hD; exact (mul_eq_zero.mp hD.symm).resolve_right hb0
    have hb'0 : b' ≠ 0 := ha'.elim (absurd ha'0) id
    refine ⟨b' / b, ?_, ?_, div_ne_zero hb'0 hb0⟩
    · rw [ha'0, ha0, mul_zero]
    · field_simp
  · have ha'0 : a' ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hD
      exact ha'.elim (absurd h0) fun h => absurd ((mul_eq_zero.mp hD).resolve_left ha0) h
    refine ⟨a' / a, ?_, ?_, div_ne_zero ha'0 ha0⟩
    · field_simp
    · field_simp; linarith

/-- Helper for FT `ef24`: parametrization of the line `a x + b y + c = 0` by the foot
`(-(a c)/(a² + b²), -(b c)/(a² + b²))` and direction `(-b, a)`. -/
theorem ef24_line_param {a b c x y t : ℝ} (hline : a * x + b * y + c = 0) (hne : a ^ 2 + b ^ 2 ≠ 0) (ht : (a ^ 2 + b ^ 2) * t = a * y - b * x) : x = -(a * c) / (a ^ 2 + b ^ 2) + t * (-b) ∧ y = -(b * c) / (a ^ 2 + b ^ 2) + t * a := by
  constructor
  · field_simp; linear_combination (a * hline + b * ht)
  · field_simp; linear_combination (b * hline - a * ht)

/-- Helper for FT `ef24`: converse parametrization — a point of the standard parametric form lies
on the line. -/
theorem ef24_line_param_mem {a b c t x y : ℝ} (hne : a ^ 2 + b ^ 2 ≠ 0) (hx : x = -(a * c) / (a ^ 2 + b ^ 2) + t * (-b)) (hy : y = -(b * c) / (a ^ 2 + b ^ 2) + t * a) : a * x + b * y + c = 0 := by
  subst hx; subst hy; field_simp; ring

/-- Helper for FT `ef24`: substituting the parametric point `(p1 + t d1, p2 + t d2)` into the circle
equation yields a quadratic in `t` with coefficients expressed by `A, B, Cq`. -/
theorem ef24_circle_quad_iff {t p1 p2 d1 d2 cx cy r A B Cq : ℝ} (hA : A = d1 ^ 2 + d2 ^ 2) (hB : B = 2 * ((p1 - cx) * d1 + (p2 - cy) * d2)) (hC : Cq = (p1 - cx) ^ 2 + (p2 - cy) ^ 2 - r * r) : ((p1 + t * d1 - cx) ^ 2 + (p2 + t * d2 - cy) ^ 2 = r * r) ↔ A * t ^ 2 + B * t + Cq = 0 := by
  subst hA; subst hB; subst hC
  constructor <;> intro h <;> linear_combination h

/-- Helper for FT `ef24`: if `t` is a root of the quadratic, then `(2 A t + B)²` equals the
discriminant `B² - 4 A Cq`; in particular the discriminant is nonnegative. -/
theorem ef24_quad_disc {t A B Cq Δ : ℝ} (h : A * t ^ 2 + B * t + Cq = 0) (hΔ : Δ = B ^ 2 - 4 * A * Cq) : (2 * A * t + B) ^ 2 = Δ := by
  subst hΔ; linear_combination (4 * A * h)

/-- Helper for FT `ef24`: if `s² = B² - 4 A Cq`, the quadratic `A t² + B t + Cq` has the root
`t = (s - B) / (2 A)`, for which moreover `2 A t + B = s`. -/
theorem ef24_quad_root_exists {A B Cq s : ℝ} (hA : A ≠ 0) (h : s * s = B ^ 2 - 4 * A * Cq) : ∃ t : ℝ, A * t ^ 2 + B * t + Cq = 0 ∧ 2 * A * t + B = s := by
  refine ⟨(s - B) / (2 * A), ?_, ?_⟩
  · field_simp; linear_combination h
  · field_simp; ring

/-- An `F`-line (FT, *Constructions with straight-edge and compass*): the line in `ℝ × ℝ` given by
`a x + b y + c = 0` with `a, b, c ∈ F` and `(a, b) ≠ 0`. -/
structure FLine (F : Subfield ℝ) where
  /-- x-coefficient -/
  a : ℝ
  /-- y-coefficient -/
  b : ℝ
  /-- constant term -/
  c : ℝ
  ha : a ∈ F
  hb : b ∈ F
  hc : c ∈ F
  ab_ne : a ≠ 0 ∨ b ≠ 0

/-- Membership of a point in the `F`-line `a x + b y + c = 0`. -/
def MemFLine {F : Subfield ℝ} (L : FLine F) (p : ℝ × ℝ) : Prop := L.a * p.1 + L.b * p.2 + L.c = 0

/-- An `F`-circle (FT): centre `(cx, cy)` with `cx, cy ∈ F` and radius `r ∈ F`, `r ≥ 0`. -/
structure FCircle (F : Subfield ℝ) where
  /-- x-coordinate of the centre -/
  cx : ℝ
  /-- y-coordinate of the centre -/
  cy : ℝ
  /-- radius -/
  r : ℝ
  hcx : cx ∈ F
  hcy : cy ∈ F
  hr : r ∈ F
  hr_nonneg : 0 ≤ r

/-- Membership of a point in the `F`-circle `(x - cx)² + (y - cy)² = r²`. -/
def MemFCircle {F : Subfield ℝ} (C : FCircle F) (p : ℝ × ℝ) : Prop := (p.1 - C.cx) ^ 2 + (p.2 - C.cy) ^ 2 = C.r * C.r

/-- `p` lies in the `F[√e]`-plane: both coordinates are of the form `u + v √e` with `u, v ∈ F`,
where `√e` is the real square root `Real.sqrt e` (so `F[√e]` is realized inside `ℝ`). -/
def InQuadPlane (F : Subfield ℝ) (e : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ u v w z : ℝ, u ∈ F ∧ v ∈ F ∧ w ∈ F ∧ z ∈ F ∧ p.1 = u + v * Real.sqrt e ∧ p.2 = w + z * Real.sqrt e

/-- FT `ef24`, clause (1).  Let `L ≠ L′` be `F`-lines.  Then `L ∩ L′ = ∅` or consists of a single
`F`-point.

Encoding: an `F`-line is the solution set in `ℝ × ℝ` of `a x + b y + c = 0` with `a, b, c ∈ F` and
`(a, b) ≠ 0` (`FLine`, `MemFLine`).  Since such coefficient triples are not unique, the hypothesis
`L ≠ L′` is encoded as distinctness of the two solution sets (the geometric meaning of distinct
lines).  The intersection is empty, or it is the singleton `{p}` of the Cramer point
`p = ((b c′ - b′ c)/(a b′ - a′ b), (a′ c - a c′)/(a b′ - a′ b))`, whose coordinates lie in `F`.
Proof idea: if `a b′ - a′ b = 0` and the lines share a point, the two equations are proportional,
so the lines are equal — contradiction; otherwise Cramer's rule gives the unique solution. -/
theorem ef24_1 {F : Subfield ℝ} (L L' : FLine F) (hne : {p : ℝ × ℝ | MemFLine L p} ≠ {p : ℝ × ℝ | MemFLine L' p}) : {p : ℝ × ℝ | MemFLine L p ∧ MemFLine L' p} = ∅ ∨ ∃ p : ℝ × ℝ, p.1 ∈ F ∧ p.2 ∈ F ∧ {q : ℝ × ℝ | MemFLine L q ∧ MemFLine L' q} = {p} := by
  by_cases hD : L.a * L'.b - L'.a * L.b = 0
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [MemFLine] at h1 h2
    obtain ⟨k, hk1, hk2, hk0⟩ := ef24_exists_prop_coeff L.ab_ne L'.ab_ne (by linarith)
    have hkc : L'.c = k * L.c := by rw [hk1, hk2] at h2; linear_combination (h2 - k * h1)
    refine hne (Set.ext fun q => ?_)
    constructor
    · intro hq
      simp only [Set.mem_setOf_eq, MemFLine] at hq ⊢
      rw [hk1, hk2, hkc]
      linear_combination (k * hq)
    · intro hq
      simp only [Set.mem_setOf_eq, MemFLine] at hq ⊢
      rw [hk1, hk2, hkc] at hq
      have hkey : k * (L.a * q.1 + L.b * q.2 + L.c) = 0 := by linear_combination hq
      exact (mul_eq_zero.mp hkey).resolve_left hk0
  · right
    have hD0 : L.a * L'.b - L'.a * L.b ≠ 0 := hD
    have hDmem : L.a * L'.b - L'.a * L.b ∈ F := Subfield.sub_mem F (Subfield.mul_mem F L.ha L'.hb) (Subfield.mul_mem F L'.ha L.hb)
    set p1 : ℝ := (L.b * L'.c - L'.b * L.c) / (L.a * L'.b - L'.a * L.b) with hp1def
    set p2 : ℝ := (L'.a * L.c - L.a * L'.c) / (L.a * L'.b - L'.a * L.b) with hp2def
    have hclear1 : L.a * (L.b * L'.c - L'.b * L.c) + L.b * (L'.a * L.c - L.a * L'.c) + L.c * (L.a * L'.b - L'.a * L.b) = 0 := by ring
    have hclear2 : L'.a * (L.b * L'.c - L'.b * L.c) + L'.b * (L'.a * L.c - L.a * L'.c) + L'.c * (L.a * L'.b - L'.a * L.b) = 0 := by ring
    have hmem1 : p1 ∈ F := by rw [hp1def]; exact Subfield.div_mem F (Subfield.sub_mem F (Subfield.mul_mem F L.hb L'.hc) (Subfield.mul_mem F L'.hb L.hc)) hDmem
    have hmem2 : p2 ∈ F := by rw [hp2def]; exact Subfield.div_mem F (Subfield.sub_mem F (Subfield.mul_mem F L'.ha L.hc) (Subfield.mul_mem F L.ha L'.hc)) hDmem
    have hDp1 : (L.a * L'.b - L'.a * L.b) * p1 = L.b * L'.c - L'.b * L.c := by rw [hp1def, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ hD0
    have hDp2 : (L.a * L'.b - L'.a * L.b) * p2 = L'.a * L.c - L.a * L'.c := by rw [hp2def, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ hD0
    have hon1 : MemFLine L ⟨p1, p2⟩ := by
      show L.a * p1 + L.b * p2 + L.c = 0
      have hz : (L.a * L'.b - L'.a * L.b) * (L.a * p1 + L.b * p2 + L.c) = 0 := by
        linear_combination (L.a * hDp1 + L.b * hDp2 + hclear1)
      exact (mul_eq_zero.mp hz).resolve_left hD0
    have hon2 : MemFLine L' ⟨p1, p2⟩ := by
      show L'.a * p1 + L'.b * p2 + L'.c = 0
      have hz : (L.a * L'.b - L'.a * L.b) * (L'.a * p1 + L'.b * p2 + L'.c) = 0 := by
        linear_combination (L'.a * hDp1 + L'.b * hDp2 + hclear2)
      exact (mul_eq_zero.mp hz).resolve_left hD0
    refine ⟨⟨p1, p2⟩, hmem1, hmem2, ?_⟩
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq1, hq2⟩
      simp only [MemFLine] at hq1 hq2
      have hc1 : (L.a * L'.b - L'.a * L.b) * q.1 = L.b * L'.c - L'.b * L.c := by linear_combination (L'.b * hq1 - L.b * hq2)
      have hc2 : (L.a * L'.b - L'.a * L.b) * q.2 = L'.a * L.c - L.a * L'.c := by linear_combination (L.a * hq2 - L'.a * hq1)
      refine Prod.ext ?_ ?_
      · rw [eq_div_iff hD0]; linear_combination hc1
      · rw [eq_div_iff hD0]; linear_combination hc2
    · rintro h
      rw [h]; exact ⟨hon1, hon2⟩

/-- FT `ef24`, clause (2).  Let `L` be an `F`-line and `C` an `F`-circle.  Then `L ∩ C = ∅` or
consists of one or two points in the `F[√e]`-plane for some `e ∈ F` with `e > 0`.

Encoding: an `F`-circle is given by centre `(cx, cy)` with `cx, cy ∈ F` and radius `r ∈ F`, `r ≥ 0`
(`FCircle`, `MemFCircle`); a point lies in the `F[√e]`-plane (`InQuadPlane`) when both coordinates
have the form `u + v √e` with `u, v ∈ F`, where `√e` is the real square root `Real.sqrt e` (so
`F[√e]` is realized as the subfield of `ℝ` generated by `F` and `√e`).  "One or two points" is
encoded as equality with `insert p {q}` (which also covers the single-point case `p = q`).

Proof idea: parametrize the line as `p₀ + t d` with `p₀ = (-a c/(a² + b²), -b c/(a² + b²))` and
`d = (-b, a)`; substitution into the circle equation gives a genuine quadratic
`(a² + b²) t² + B t + C = 0` over `F`.  If the intersection is nonempty its discriminant
`Δ = B² - 4 (a² + b²) C` is a square `(2 (a² + b²) t₀ + B)²` of a real number, hence `Δ ≥ 0`, and
each intersection point corresponds to a root `t = (-B ± √Δ)/(2 (a² + b²))`, giving coordinates
`u + v √Δ` with `u, v ∈ F`.  In the tangential case `Δ = 0` the coordinates already lie in `F ⊆
F[√1]`, so `e = 1` is produced. -/
theorem ef24_2 {F : Subfield ℝ} (L : FLine F) (C : FCircle F) : {p : ℝ × ℝ | MemFLine L p ∧ MemFCircle C p} = ∅ ∨ ∃ e : ℝ, e ∈ F ∧ 0 < e ∧ ∃ p q : ℝ × ℝ, InQuadPlane F e p ∧ InQuadPlane F e q ∧ {r : ℝ × ℝ | MemFLine L r ∧ MemFCircle C r} = insert p {q} := by
  by_cases hex : ∃ p : ℝ × ℝ, MemFLine L p ∧ MemFCircle C p
  · right
    obtain ⟨p0, hp0l, hp0c⟩ := hex
    simp only [MemFLine] at hp0l
    have hA0 : L.a ^ 2 + L.b ^ 2 ≠ 0 := by
      intro h
      rcases L.ab_ne with h' | h'
      · exact h' (ef24_sq_add_sq_eq_zero h).1
      · exact h' (ef24_sq_add_sq_eq_zero h).2
    have hAmem : L.a ^ 2 + L.b ^ 2 ∈ F := by rw [pow_two, pow_two]; exact Subfield.add_mem F (Subfield.mul_mem F L.ha L.ha) (Subfield.mul_mem F L.hb L.hb)
    have hp01mem : -(L.a * L.c) / (L.a ^ 2 + L.b ^ 2) ∈ F := Subfield.div_mem F (Subfield.neg_mem F (Subfield.mul_mem F L.ha L.hc)) hAmem
    have hp02mem : -(L.b * L.c) / (L.a ^ 2 + L.b ^ 2) ∈ F := Subfield.div_mem F (Subfield.neg_mem F (Subfield.mul_mem F L.hb L.hc)) hAmem
    have hBmem : -L.b ∈ F := Subfield.neg_mem F L.hb
    set p01 : ℝ := -(L.a * L.c) / (L.a ^ 2 + L.b ^ 2) with hp01def
    set p02 : ℝ := -(L.b * L.c) / (L.a ^ 2 + L.b ^ 2) with hp02def
    set t0 : ℝ := (L.a * p0.2 - L.b * p0.1) / (L.a ^ 2 + L.b ^ 2) with ht0def
    have ht0 : (L.a ^ 2 + L.b ^ 2) * t0 = L.a * p0.2 - L.b * p0.1 := by rw [ht0def, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ hA0
    obtain ⟨hpar1, hpar2⟩ := ef24_line_param hp0l hA0 ht0
    rw [← hp01def] at hpar1
    rw [← hp02def] at hpar2
    set Bq : ℝ := 2 * ((p01 - C.cx) * (-L.b) + (p02 - C.cy) * L.a) with hBqdef
    set Cq : ℝ := (p01 - C.cx) ^ 2 + (p02 - C.cy) ^ 2 - C.r * C.r with hCqdef
    have hcirc0 : MemFCircle C ⟨p01 + t0 * (-L.b), p02 + t0 * L.a⟩ := by rw [← hpar1, ← hpar2]; exact hp0c
    have hAeq : L.a ^ 2 + L.b ^ 2 = (-L.b) ^ 2 + L.a ^ 2 := by ring
    have hroot0 : (L.a ^ 2 + L.b ^ 2) * t0 ^ 2 + Bq * t0 + Cq = 0 := (ef24_circle_quad_iff hAeq hBqdef hCqdef).mp hcirc0
    set Δ : ℝ := Bq ^ 2 - 4 * (L.a ^ 2 + L.b ^ 2) * Cq with hΔdef
    have hw1m : (p01 - C.cx) * (-L.b) ∈ F := Subfield.mul_mem F (Subfield.sub_mem F hp01mem C.hcx) hBmem
    have hw2m : (p02 - C.cy) * L.a ∈ F := Subfield.mul_mem F (Subfield.sub_mem F hp02mem C.hcy) L.ha
    have hBqmem : Bq ∈ F := by rw [hBqdef]; exact Subfield.mul_mem F ef24_two_mem (Subfield.add_mem F hw1m hw2m)
    have hu1m : (p01 - C.cx) ^ 2 ∈ F := by rw [pow_two]; exact Subfield.mul_mem F (Subfield.sub_mem F hp01mem C.hcx) (Subfield.sub_mem F hp01mem C.hcx)
    have hu2m : (p02 - C.cy) ^ 2 ∈ F := by rw [pow_two]; exact Subfield.mul_mem F (Subfield.sub_mem F hp02mem C.hcy) (Subfield.sub_mem F hp02mem C.hcy)
    have hCqmem : Cq ∈ F := by rw [hCqdef]; exact Subfield.sub_mem F (Subfield.add_mem F hu1m hu2m) (Subfield.mul_mem F C.hr C.hr)
    have hBq2m : Bq ^ 2 ∈ F := by rw [pow_two]; exact Subfield.mul_mem F hBqmem hBqmem
    have hΔmem : Δ ∈ F := by rw [hΔdef]; exact Subfield.sub_mem F hBq2m (Subfield.mul_mem F (Subfield.mul_mem F ef24_four_mem hAmem) hCqmem)
    have hΔsq : (2 * (L.a ^ 2 + L.b ^ 2) * t0 + Bq) ^ 2 = Δ := ef24_quad_disc hroot0 hΔdef
    have hΔle : 0 ≤ Δ := by rw [← hΔsq]; exact sq_nonneg _
    have hsΔ : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔle
    have hsΔ2 : (Real.sqrt Δ) ^ 2 = Δ := by rw [pow_two]; exact hsΔ
    have hroot' : Real.sqrt Δ * Real.sqrt Δ = Bq ^ 2 - 4 * (L.a ^ 2 + L.b ^ 2) * Cq := by rw [hsΔ, hΔdef]
    obtain ⟨tpos, hqpos, h2pos⟩ := ef24_quad_root_exists hA0 hroot'
    obtain ⟨tneg, hqneg, h2neg⟩ := ef24_quad_root_exists hA0 (by rw [neg_mul_neg]; exact hroot')
    have hAt : 2 * (L.a ^ 2 + L.b ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hA0
    have hPposin : MemFLine L ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ ∧ MemFCircle C ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ := by
      constructor
      · exact ef24_line_param_mem hA0 (by rw [← hp01def]) (by rw [← hp02def])
      · exact (ef24_circle_quad_iff hAeq hBqdef hCqdef).mpr hqpos
    have hPnegin : MemFLine L ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ ∧ MemFCircle C ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ := by
      constructor
      · exact ef24_line_param_mem hA0 (by rw [← hp01def]) (by rw [← hp02def])
      · exact (ef24_circle_quad_iff hAeq hBqdef hCqdef).mpr hqneg
    have hchar : ∀ q : ℝ × ℝ, MemFLine L q ∧ MemFCircle C q → q = ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ ∨ q = ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [MemFLine] at hq1
      set tq : ℝ := (L.a * q.2 - L.b * q.1) / (L.a ^ 2 + L.b ^ 2) with htqdef
      have htq : (L.a ^ 2 + L.b ^ 2) * tq = L.a * q.2 - L.b * q.1 := by rw [htqdef, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ hA0
      obtain ⟨hpar1, hpar2⟩ := ef24_line_param hq1 hA0 htq
      rw [← hp01def] at hpar1
      rw [← hp02def] at hpar2
      have hcircq : MemFCircle C ⟨p01 + tq * (-L.b), p02 + tq * L.a⟩ := by rw [← hpar1, ← hpar2]; exact hq2
      have hrootq : (L.a ^ 2 + L.b ^ 2) * tq ^ 2 + Bq * tq + Cq = 0 := (ef24_circle_quad_iff hAeq hBqdef hCqdef).mp hcircq
      have hΔq : (2 * (L.a ^ 2 + L.b ^ 2) * tq + Bq) ^ 2 = Δ := ef24_quad_disc hrootq hΔdef
      have hprod : (2 * (L.a ^ 2 + L.b ^ 2) * tq + Bq) * (2 * (L.a ^ 2 + L.b ^ 2) * tq + Bq) = Real.sqrt Δ * Real.sqrt Δ := by rw [← pow_two, ← pow_two]; rw [hΔq, hsΔ2]
      rcases mul_self_eq_mul_self_iff.mp hprod with h | h
      · left
        have hteq : tq = tpos := mul_left_cancel₀ hAt (by linarith [h, h2pos])
        refine Prod.ext ?_ ?_
        · rw [hpar1, hteq]
        · rw [hpar2, hteq]
      · right
        have hteq : tq = tneg := mul_left_cancel₀ hAt (by linarith [h, h2neg])
        refine Prod.ext ?_ ?_
        · rw [hpar1, hteq]
        · rw [hpar2, hteq]
    have hset : {r : ℝ × ℝ | MemFLine L r ∧ MemFCircle C r} = insert ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ {⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hr
        exact hchar r hr
      · rintro (h | h)
        · rw [h]; exact hPposin
        · rw [h]; exact hPnegin
    by_cases hΔz : Δ = 0
    · have hs0 : Real.sqrt Δ = 0 := by rw [hΔz]; exact Real.sqrt_zero
      rw [hs0] at h2pos h2neg
      have h5p : 2 * (L.a ^ 2 + L.b ^ 2) * tpos = -Bq := by linarith
      have h5n : 2 * (L.a ^ 2 + L.b ^ 2) * tneg = -Bq := by linarith
      have htposp : tpos = -Bq / (2 * (L.a ^ 2 + L.b ^ 2)) := by rw [← h5p]; exact (mul_div_cancel_left₀ _ hAt).symm
      have htnegp : tneg = -Bq / (2 * (L.a ^ 2 + L.b ^ 2)) := by rw [← h5n]; exact (mul_div_cancel_left₀ _ hAt).symm
      have htposmem : tpos ∈ F := by rw [htposp]; exact Subfield.div_mem F (Subfield.neg_mem F hBqmem) (Subfield.mul_mem F ef24_two_mem hAmem)
      have htnegmem : tneg ∈ F := by rw [htnegp]; exact Subfield.div_mem F (Subfield.neg_mem F hBqmem) (Subfield.mul_mem F ef24_two_mem hAmem)
      have hc1F : p01 + tpos * (-L.b) ∈ F := Subfield.add_mem F hp01mem (Subfield.mul_mem F htposmem hBmem)
      have hc2F : p02 + tpos * L.a ∈ F := Subfield.add_mem F hp02mem (Subfield.mul_mem F htposmem L.ha)
      have hc1F' : p01 + tneg * (-L.b) ∈ F := Subfield.add_mem F hp01mem (Subfield.mul_mem F htnegmem hBmem)
      have hc2F' : p02 + tneg * L.a ∈ F := Subfield.add_mem F hp02mem (Subfield.mul_mem F htnegmem L.ha)
      have hiP1 : InQuadPlane F 1 ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ := ⟨p01 + tpos * (-L.b), 0, p02 + tpos * L.a, 0, hc1F, Subfield.zero_mem F, hc2F, Subfield.zero_mem F, by show p01 + tpos * (-L.b) = p01 + tpos * (-L.b) + 0 * Real.sqrt 1; ring, by show p02 + tpos * L.a = p02 + tpos * L.a + 0 * Real.sqrt 1; ring⟩
      have hiP2 : InQuadPlane F 1 ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ := ⟨p01 + tneg * (-L.b), 0, p02 + tneg * L.a, 0, hc1F', Subfield.zero_mem F, hc2F', Subfield.zero_mem F, by show p01 + tneg * (-L.b) = p01 + tneg * (-L.b) + 0 * Real.sqrt 1; ring, by show p02 + tneg * L.a = p02 + tneg * L.a + 0 * Real.sqrt 1; ring⟩
      exact ⟨1, Subfield.one_mem F, zero_lt_one, ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩, ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩, hiP1, hiP2, hset⟩
    · have g1 : p01 + tpos * (-L.b) = p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) + (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) * Real.sqrt Δ := by
        field_simp
        linear_combination ((-L.b) * h2pos)
      have g2 : p02 + tpos * L.a = p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)) + L.a / (2 * (L.a ^ 2 + L.b ^ 2)) * Real.sqrt Δ := by
        field_simp
        linear_combination (L.a * h2pos)
      have g3 : p01 + tneg * (-L.b) = p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) + L.b / (2 * (L.a ^ 2 + L.b ^ 2)) * Real.sqrt Δ := by
        field_simp
        linear_combination ((-L.b) * h2neg)
      have g4 : p02 + tneg * L.a = p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)) + (-L.a) / (2 * (L.a ^ 2 + L.b ^ 2)) * Real.sqrt Δ := by
        field_simp
        linear_combination (L.a * h2neg)
      have hu1mem : p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.sub_mem F hp01mem (Subfield.div_mem F (Subfield.mul_mem F hBqmem hBmem) (Subfield.mul_mem F ef24_two_mem hAmem))
      have hv1mem : (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F hBmem (Subfield.mul_mem F ef24_two_mem hAmem)
      have hu2mem : p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.sub_mem F hp02mem (Subfield.div_mem F (Subfield.mul_mem F hBqmem L.ha) (Subfield.mul_mem F ef24_two_mem hAmem))
      have hv2mem : L.a / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F L.ha (Subfield.mul_mem F ef24_two_mem hAmem)
      have hv2mem' : (-L.a) / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F (Subfield.neg_mem F L.ha) (Subfield.mul_mem F ef24_two_mem hAmem)
      have hv1mem' : L.b / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F L.hb (Subfield.mul_mem F ef24_two_mem hAmem)
      exact ⟨Δ, hΔmem, lt_of_le_of_ne hΔle (Ne.symm hΔz), ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩, ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩, ⟨p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)), (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)), p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)), L.a / (2 * (L.a ^ 2 + L.b ^ 2)), hu1mem, hv1mem, hu2mem, hv2mem, g1, g2⟩, ⟨p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)), L.b / (2 * (L.a ^ 2 + L.b ^ 2)), p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)), (-L.a) / (2 * (L.a ^ 2 + L.b ^ 2)), hu1mem, hv1mem', hu2mem, hv2mem', g3, g4⟩, hset⟩
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    exact hex ⟨p, hp⟩

/-- FT `ef24`, clause (3).  Let `C ≠ C′` be `F`-circles.  Then `C ∩ C′ = ∅` or consists of one or
two points in the `F[√e]`-plane for some `e ∈ F` with `e > 0`.

Encoding: `C ≠ C′` is encoded as distinctness of the defining data (`C.cx ≠ C'.cx ∨ C.cy ≠ C'.cy ∨
C.r ≠ C'.r`), which is equivalent to distinctness of the structures since the data determine the
circle.  "One or two points in the `F[√e]`-plane" is as in `ef24_2` (`InQuadPlane`, `insert p {q}`).

Proof idea: subtracting the two circle equations gives the radical axis, an `F`-line
`2 (cx - cx′) x + 2 (cy - cy′) y + (cx′² + cy′² - cx² - cy² - r′² + r²) = 0` with a genuinely
nonzero coefficient pair when the centres differ.  A common point of the two circles is exactly a
common point of this `F`-line and `C`, so clause (2) applies.  If the centres coincide, then `C ≠ C′`
forces `r ≠ r′`, and a point on both circles would give `r² = r′²`, hence `r = r′` — so the
intersection is empty. -/
theorem ef24_3 {F : Subfield ℝ} (C C' : FCircle F) (hC : C.cx ≠ C'.cx ∨ C.cy ≠ C'.cy ∨ C.r ≠ C'.r) : {p : ℝ × ℝ | MemFCircle C p ∧ MemFCircle C' p} = ∅ ∨ ∃ e : ℝ, e ∈ F ∧ 0 < e ∧ ∃ p q : ℝ × ℝ, InQuadPlane F e p ∧ InQuadPlane F e q ∧ {r : ℝ × ℝ | MemFCircle C r ∧ MemFCircle C' r} = insert p {q} := by
  by_cases hctr : C.cx = C'.cx ∧ C.cy = C'.cy
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [MemFCircle] at h1 h2
    rcases hC with h | h | h
    · exact absurd hctr.1 h
    · exact absurd hctr.2 h
    · rw [← hctr.1, ← hctr.2] at h2
      have hrr : C.r * C.r = C'.r * C'.r := by linarith
      rcases mul_self_eq_mul_self_iff.mp hrr with h0 | h0
      · exact h h0
      · exact h (by linarith [h0, C.hr_nonneg, C'.hr_nonneg])
  · have hctr' : C.cx ≠ C'.cx ∨ C.cy ≠ C'.cy := by
      by_cases h1 : C.cx = C'.cx
      · right; intro h2; exact hctr ⟨h1, h2⟩
      · left; exact h1
    set a3 : ℝ := 2 * (C.cx - C'.cx) with ha3def
    set b3 : ℝ := 2 * (C.cy - C'.cy) with hb3def
    set c3 : ℝ := C'.cx ^ 2 + C'.cy ^ 2 - C.cx ^ 2 - C.cy ^ 2 - C'.r * C'.r + C.r * C.r with hc3def
    have ha3mem : a3 ∈ F := by rw [ha3def]; exact Subfield.mul_mem F ef24_two_mem (Subfield.sub_mem F C.hcx C'.hcx)
    have hb3mem : b3 ∈ F := by rw [hb3def]; exact Subfield.mul_mem F ef24_two_mem (Subfield.sub_mem F C.hcy C'.hcy)
    have hc3mem : c3 ∈ F := by
      rw [hc3def, pow_two, pow_two, pow_two, pow_two]
      exact Subfield.add_mem F (Subfield.sub_mem F (Subfield.sub_mem F (Subfield.sub_mem F (Subfield.add_mem F (Subfield.mul_mem F C'.hcx C'.hcx) (Subfield.mul_mem F C'.hcy C'.hcy)) (Subfield.mul_mem F C.hcx C.hcx)) (Subfield.mul_mem F C.hcy C.hcy)) (Subfield.mul_mem F C'.hr C'.hr)) (Subfield.mul_mem F C.hr C.hr)
    have hline : a3 ≠ 0 ∨ b3 ≠ 0 := by
      rcases hctr' with h | h
      · left
        intro h0
        rw [ha3def] at h0
        exact h (by linarith)
      · right
        intro h0
        rw [hb3def] at h0
        exact h (by linarith)
    have hiff : ∀ p : ℝ × ℝ, (MemFCircle C p ∧ MemFCircle C' p) ↔ (a3 * p.1 + b3 * p.2 + c3 = 0 ∧ MemFCircle C p) := by
      intro p
      constructor
      · rintro ⟨h1, h2⟩
        simp only [MemFCircle] at h1 h2
        refine ⟨?_, h1⟩
        have e1 : (p.1 - C'.cx) ^ 2 - (p.1 - C.cx) ^ 2 = 2 * (C.cx - C'.cx) * p.1 + (C'.cx ^ 2 - C.cx ^ 2) := by ring
        have e2 : (p.2 - C'.cy) ^ 2 - (p.2 - C.cy) ^ 2 = 2 * (C.cy - C'.cy) * p.2 + (C'.cy ^ 2 - C.cy ^ 2) := by ring
        linarith
      · rintro ⟨h3, h1⟩
        simp only [MemFCircle] at h1 ⊢
        refine ⟨h1, ?_⟩
        have e1 : (p.1 - C'.cx) ^ 2 - (p.1 - C.cx) ^ 2 = 2 * (C.cx - C'.cx) * p.1 + (C'.cx ^ 2 - C.cx ^ 2) := by ring
        have e2 : (p.2 - C'.cy) ^ 2 - (p.2 - C.cy) ^ 2 = 2 * (C.cy - C'.cy) * p.2 + (C'.cy ^ 2 - C.cy ^ 2) := by ring
        linarith
    have hseteq' : {p : ℝ × ℝ | MemFLine ⟨a3, b3, c3, ha3mem, hb3mem, hc3mem, hline⟩ p ∧ MemFCircle C p} = {p : ℝ × ℝ | MemFCircle C p ∧ MemFCircle C' p} := by
      ext p
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨h5, h6⟩
        exact (hiff p).mpr ⟨h5, h6⟩
      · intro h
        obtain ⟨h5, h6⟩ := (hiff p).mp h
        exact ⟨h5, h6⟩
    have hfin := ef24_2 ⟨a3, b3, c3, ha3mem, hb3mem, hc3mem, hline⟩ C
    rw [hseteq'] at hfin
    exact hfin

/-- FT `ef31` (auxiliary plumbing).  Substituting `X - C t` into the substituted polynomial
`(p.comp (X + C t))` recovers `p`: this is the trivial inverse property of the change of
variables `X ↦ X + t`, and is the only fact needed to transfer units and irreducibility of
`R[X]` across the substitution `f(X) ↦ f(X + 1)` used in the proof of FT `ef31`.  Proof is a
standard `Polynomial.comp_assoc` computation; mathematically trivial. -/
private theorem comp_X_add_C_comp_X_sub_C {R : Type*} [CommRing R] (t : R) (p : R[X]) :
    (p.comp (X + C t)).comp (X - C t) = p := by
  have h : (X + C t).comp (X - C t) = X := by simp
  rw [Polynomial.comp_assoc, h, Polynomial.comp_X]

/-- FT `ef31` (auxiliary plumbing).  A polynomial `p ∈ R[X]` is a unit iff its substitution
image `p(X + t)` is a unit; this makes `f(X) ↦ f(X + 1)` a unit-respecting multiplicative
automorphism of `R[X]`.  Proof: one direction maps the unit through the ring homomorphism
`Polynomial.compRingHom`; the other composes back with `X - C t` (previous lemma) and again
maps a unit through a ring homomorphism. -/
private theorem isUnit_comp_X_add_C_iff {R : Type*} [CommRing R] (t : R) {p : R[X]} :
    IsUnit (p.comp (X + C t)) ↔ IsUnit p :=
  ⟨fun hu => by
      rw [← comp_X_add_C_comp_X_sub_C t p]
      exact (Polynomial.compRingHom (X - C t)).isUnit_map hu,
   fun hu => (Polynomial.compRingHom (X + C t)).isUnit_map hu⟩

/-- FT `ef31` (auxiliary plumbing).  Mirror of `comp_X_add_C_comp_X_sub_C` for the
substitution `X ↦ X - t`: `(p(X - t))(X + t) = p(X)`.  Proof is the same trivial
`Polynomial.comp_assoc` computation. -/
private theorem comp_X_sub_C_comp_X_add_C {R : Type*} [CommRing R] (t : R) (p : R[X]) :
    (p.comp (X - C t)).comp (X + C t) = p := by
  have h : (X - C t).comp (X + C t) = X := by simp
  rw [Polynomial.comp_assoc, h, Polynomial.comp_X]

/-- FT `ef31` (auxiliary plumbing).  A polynomial `p ∈ R[X]` is a unit iff its substitution
image `p(X - t)` is a unit.  Proof identical to `isUnit_comp_X_add_C_iff`. -/
private theorem isUnit_comp_X_sub_C_iff {R : Type*} [CommRing R] (t : R) {p : R[X]} :
    IsUnit (p.comp (X - C t)) ↔ IsUnit p :=
  ⟨fun hu => by
      rw [← comp_X_sub_C_comp_X_add_C t p]
      exact (Polynomial.compRingHom (X + C t)).isUnit_map hu,
   fun hu => (Polynomial.compRingHom (X - C t)).isUnit_map hu⟩

/-- FT `ef31` (auxiliary plumbing).  The substitution `f(X) ↦ f(X + t)` is a multiplicative
automorphism of `R[X]`, hence preserves irreducibility.  This is the standard step in the
Eisenstein proof of the irreducibility of `X ^ (p - 1) + ⋯ + 1`: Eisenstein's criterion
applies to `f(X + 1)`, and irreducibility is transported back to `f`.  Proof: expand both
sides with `irreducible_iff` and transfer units and factorizations through the substitution,
using the two unit-transfer lemmas above. -/
private theorem irreducible_comp_X_add_C_iff {R : Type*} [CommRing R] (t : R) {p : R[X]} :
    Irreducible (p.comp (X + C t)) ↔ Irreducible p := by
  rw [irreducible_iff, irreducible_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hu => h1 (isUnit_comp_X_add_C_iff t |>.2 hu), fun x y hxy => ?_⟩
    have hp : p.comp (X + C t) = x.comp (X + C t) * y.comp (X + C t) := by
      rw [hxy, Polynomial.mul_comp]
    rcases h2 hp with h' | h'
    · exact Or.inl (isUnit_comp_X_add_C_iff t |>.1 h')
    · exact Or.inr (isUnit_comp_X_add_C_iff t |>.1 h')
  · rintro ⟨h1, h2⟩
    refine ⟨fun hu => h1 (isUnit_comp_X_add_C_iff t |>.1 hu), fun x y hxy => ?_⟩
    have hp : p = x.comp (X - C t) * y.comp (X - C t) := by
      rw [← comp_X_add_C_comp_X_sub_C t p, hxy, Polynomial.mul_comp]
    rcases h2 hp with h' | h'
    · exact Or.inl (isUnit_comp_X_sub_C_iff t |>.1 h')
    · exact Or.inr (isUnit_comp_X_sub_C_iff t |>.1 h')

/-- FT `ef31` (auxiliary lemma: the Eisenstein step).  With `f(X) = X ^ (p - 1) + ⋯ + 1 =
∑ i ∈ range p, X ^ i` (so `(X - 1) * f = X ^ p - 1`, i.e. `f` is Milne's `(X ^ p - 1)/(X - 1)`,
and `f = Φ_p`, the `p`-th cyclotomic polynomial, for prime `p`), the substituted polynomial
`f(X + 1) = ((X + 1) ^ p - 1) / X` is Eisenstein at the prime `p`: its non-leading
coefficients are the binomial coefficients `C(p, i + 1)`, all divisible by `p` (FT `ef3`),
while `p ^ 2 ∤ C(p, 2)` — exactly the computation in Milne's proof.  Delegation: the
coefficient computation is delegated to Mathlib's
`Polynomial.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` (at `n = 0`, using
`Φ_p = ∑ i ∈ range p, X ^ i` from `Polynomial.cyclotomic_prime`); its proof performs precisely
this binomial-coefficient argument. -/
theorem geom_sum_prime_comp_X_add_one_isEisensteinAt {p : ℕ} (hp : p.Prime) :
    ((∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).comp (X + C 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ)}) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← cyclotomic_prime ℤ p]
  have hcyc : cyclotomic (p ^ (0 + 1)) ℤ = cyclotomic p ℤ := by simp
  rw [← hcyc]
  exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p 0

/-- FT `ef31` (auxiliary lemma).  For a prime `p`, the polynomial `X ^ (p - 1) + ⋯ + 1` is
irreducible in `ℤ[X]`.  Proof follows the source: by the Eisenstein criterion in prime-ideal
form (`Polynomial.IsEisensteinAt.irreducible` at the prime ideal `pℤ`; the composition with
the monic `X + C 1` is monic, hence primitive, and has degree `φ(p) = p - 1 > 0`),
`f(X + 1)` is irreducible; the substitution `X ↦ X + 1` is a multiplicative automorphism
(`irreducible_comp_X_add_C_iff`), so `f` itself is irreducible. -/
theorem geom_sum_prime_irreducible_int {p : ℕ} (hp : p.Prime) :
    Irreducible (∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : Irreducible ((∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).comp (X + C 1)) := by
    have hmonic : ((∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).comp (X + C 1)).Monic := by
      rw [← cyclotomic_prime ℤ p]
      exact (cyclotomic.monic p ℤ).comp_X_add_C 1
    have hprime : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
    have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 hprime
    refine Polynomial.IsEisensteinAt.irreducible
      (geom_sum_prime_comp_X_add_one_isEisensteinAt hp) hP hmonic.isPrimitive ?_
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one,
      ← cyclotomic_prime ℤ p, natDegree_cyclotomic, Nat.totient_prime hp]
    exact Nat.sub_pos_of_lt hp.two_le
  exact (irreducible_comp_X_add_C_iff (1 : ℤ)).mp hc

/-- FT `ef31` (part (i), key lemma).  If `p` is prime, then `X ^ (p - 1) + ⋯ + 1` is
irreducible.  In the source this is `Φ_p = (X ^ p - 1) / (X - 1)` over `ℚ`; here the
polynomial is represented as the geometric sum `∑ i ∈ Finset.range p, X ^ i` (Mathlib's
`Polynomial.cyclotomic_prime` identifies it with `cyclotomic p`, so this is irreducibility of
the `p`-th cyclotomic polynomial over `ℚ`).  Proof: Gauss's lemma
(`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`, the same reduction the
source makes via FT `ef6`) transports irreducibility from `ℤ[X]`
(`geom_sum_prime_irreducible_int`, i.e. Eisenstein on `Φ_p(X + 1)` per the source proof) to
`ℚ[X]`. -/
theorem geom_sum_prime_irreducible {p : ℕ} (hp : p.Prime) :
    Irreducible (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ i) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hprim : (∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).IsPrimitive := by
    rw [← cyclotomic_prime ℤ p]
    exact (cyclotomic.monic p ℤ).isPrimitive
  have hmap : (∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).map (algebraMap ℤ ℚ)
      = ∑ i ∈ Finset.range p, (X : ℚ[X]) ^ i := by
    simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]
  rw [← hmap]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map hprim).mp
    (geom_sum_prime_irreducible_int hp)

/-- FT `ef31` (part (ii), degree conclusion).  If `p` is prime, then `ℚ[e ^ (2πi / p)]` has
degree `p - 1` over `ℚ`.  Proof: `ζ = e ^ (2πi / p)` is a primitive `p`-th root of unity
(`Complex.isPrimitiveRoot_exp`), so `Φ_p = cyclotomic p ℚ` is its minimal polynomial over
`ℚ` (`Polynomial.cyclotomic_eq_minpoly_rat`), whose degree is `φ(p) = p - 1`
(`Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`); the degree of a simple adjoin equals
the degree of the minimal polynomial (`IntermediateField.adjoin.finrank`).  Combined with
part (i), this is the source's "hence": the minimal polynomial of `ζ` is the irreducible
degree `p - 1` polynomial `X ^ (p - 1) + ⋯ + 1`. -/
theorem finrank_adjoin_exp_two_pi_i_over_prime {p : ℕ} (hp : p.Prime) :
    Module.finrank ℚ (ℚ⟮Complex.exp (2 * Real.pi * Complex.I / p)⟯) = p - 1 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.pos.ne'
  have hint : IsIntegral ℚ (Complex.exp (2 * Real.pi * Complex.I / p)) := by
    refine ⟨cyclotomic p ℚ, cyclotomic.monic p ℚ, ?_⟩
    rw [eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def]
    exact IsPrimitiveRoot.isRoot_cyclotomic hp.pos hζ
  rw [IntermediateField.adjoin.finrank hint, ← cyclotomic_eq_minpoly_rat hζ hp.pos,
    natDegree_cyclotomic, Nat.totient_prime hp]

end ConstructionsStraightEdgeCompass

end FT
