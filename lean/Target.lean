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
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

# Inventory
INVENTORY-SCRIPT tools/ft_inventory.py
COVERAGE-SCRIPT tools/ft_coverage.py

Script notes: `tools/ft_inventory.py` extracts referenceable source environments
(exercises, solutions, and the review/examination chapters excluded by
default); `tools/ft_coverage.py` audits the stable TeX labels mentioned by this
target against the extracted inventory.

AUDIT-GAP (coverage audit, expected for work-in-progress; updated after the
audit of commit a86787d, which found the previous note stale): the target covers
chapters 1 and 2 completely - all 24 (ch1) and all 9 (ch2: `sf1`, `sf2`, `sf4`,
`sf7`, `sf8`, `ft1`, `ft3`, `ft3a`, `ft5`; the definition-like labels `ft4`,
`ft4m` and the examples/asides are additionally formalized) theorem-like labels
are formalized and mentioned, and `tools/ft_coverage.py` reports 0 unmentioned
chapter-1/2 labels.  Chapters 3-7 (fundamental theorem of Galois theory, computing
Galois groups, applications, algebraic closures, infinite Galois extensions,
etale algebras, transcendental extensions; the `ft`/`te`/`ag`/`cg`/`ig`/
`ca` label clusters) are pending although in scope per the provenance
`scope` field (which omits only exercises, solutions, and expositional
material).  To be recorded in the final ledger as pending or as
AUDIT-DEFERRED.
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

/-- Technical lemma.  On the real line, `x² + y² = 0` forces `x = y = 0`.  The proof is
trivial (`sq_nonneg` on both summands). -/
theorem eq_zero_of_sq_add_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have h1 : 0 ≤ y ^ 2 := sq_nonneg y
  have hx : x ^ 2 ≤ 0 := by linarith
  have hy : y ^ 2 ≤ 0 := by linarith [sq_nonneg x]
  exact ⟨sq_eq_zero_iff.mp (le_antisymm hx (sq_nonneg x)), sq_eq_zero_iff.mp (le_antisymm hy (sq_nonneg y))⟩

/-- Technical lemma.  `2` belongs to every subfield of `ℝ`.  The proof is trivial
(`2 = 1 + 1`). -/
theorem two_mem_subfield {F : Subfield ℝ} : (2 : ℝ) ∈ F := by
  have h : (2 : ℝ) = 1 + 1 := by norm_num
  rw [h]; exact Subfield.add_mem F (Subfield.one_mem F) (Subfield.one_mem F)

/-- Technical lemma.  `4` belongs to every subfield of `ℝ`.  The proof is trivial
(`4 = 2 + 2`). -/
theorem four_mem_subfield {F : Subfield ℝ} : (4 : ℝ) ∈ F := by
  have h : (4 : ℝ) = 2 + 2 := by norm_num
  rw [h]; exact Subfield.add_mem F two_mem_subfield two_mem_subfield

/-- Technical lemma.  Two nonproportional nonzero pairs with vanishing determinant of
`[[a, b], [a', b']]` cannot exist: if `a b' = a' b` and `(a, b) ≠ 0 ≠ (a', b')`, then `(a', b')`
is a nonzero multiple of `(a, b)`.  Proof idea: case on which coordinate of `(a, b)` is
nonzero and solve for the scale factor. -/
theorem exists_prop_coeff_of_det_eq_zero {a a' b b' : ℝ} (ha : a ≠ 0 ∨ b ≠ 0) (ha' : a' ≠ 0 ∨ b' ≠ 0) (hD : a * b' = a' * b) : ∃ k : ℝ, a' = k * a ∧ b' = k * b ∧ k ≠ 0 := by
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

/-- Technical lemma.  Parametrization of the line `a x + b y + c = 0` by the foot
`(-(a c)/(a² + b²), -(b c)/(a² + b²))` and direction `(-b, a)`.  Proof idea: the foot lies
on the line and `(-b, a)` spans its direction kernel; both identities are
`linear_combination`-arithmetic. -/
theorem line_param_of_mem_line {a b c x y t : ℝ} (hline : a * x + b * y + c = 0) (hne : a ^ 2 + b ^ 2 ≠ 0) (ht : (a ^ 2 + b ^ 2) * t = a * y - b * x) : x = -(a * c) / (a ^ 2 + b ^ 2) + t * (-b) ∧ y = -(b * c) / (a ^ 2 + b ^ 2) + t * a := by
  constructor
  · field_simp; linear_combination (a * hline + b * ht)
  · field_simp; linear_combination (b * hline - a * ht)

/-- Technical lemma.  Converse parametrization — a point of the standard parametric form lies
on the line.  The proof is trivial (substitution and `ring`). -/
theorem mem_line_of_line_param {a b c t x y : ℝ} (hne : a ^ 2 + b ^ 2 ≠ 0) (hx : x = -(a * c) / (a ^ 2 + b ^ 2) + t * (-b)) (hy : y = -(b * c) / (a ^ 2 + b ^ 2) + t * a) : a * x + b * y + c = 0 := by
  subst hx; subst hy; field_simp; ring

/-- Technical lemma.  Substituting the parametric point `(p1 + t d1, p2 + t d2)` into the circle
equation yields a quadratic in `t` with coefficients expressed by `A, B, Cq`.  The proof is
trivial expansion (`linear_combination`). -/
theorem mem_circle_iff_quadratic {t p1 p2 d1 d2 cx cy r A B Cq : ℝ} (hA : A = d1 ^ 2 + d2 ^ 2) (hB : B = 2 * ((p1 - cx) * d1 + (p2 - cy) * d2)) (hC : Cq = (p1 - cx) ^ 2 + (p2 - cy) ^ 2 - r * r) : ((p1 + t * d1 - cx) ^ 2 + (p2 + t * d2 - cy) ^ 2 = r * r) ↔ A * t ^ 2 + B * t + Cq = 0 := by
  subst hA; subst hB; subst hC
  constructor <;> intro h <;> linear_combination h

/-- Technical lemma.  If `t` is a root of the quadratic, then `(2 A t + B)²` equals the
discriminant `B² - 4 A Cq`; in particular the discriminant is nonnegative.  The proof is
trivial (`linear_combination`). -/
theorem sq_eq_disc_of_quadratic_root {t A B Cq Δ : ℝ} (h : A * t ^ 2 + B * t + Cq = 0) (hΔ : Δ = B ^ 2 - 4 * A * Cq) : (2 * A * t + B) ^ 2 = Δ := by
  subst hΔ; linear_combination (4 * A * h)

/-- Technical lemma.  If `s² = B² - 4 A Cq`, the quadratic `A t² + B t + Cq` has the root
`t = (s - B) / (2 A)`, for which moreover `2 A t + B = s`.  The proof is the quadratic-root
computation (`field_simp` and `linear_combination`). -/
theorem exists_quadratic_root_of_sq_eq_disc {A B Cq s : ℝ} (hA : A ≠ 0) (h : s * s = B ^ 2 - 4 * A * Cq) : ∃ t : ℝ, A * t ^ 2 + B * t + Cq = 0 ∧ 2 * A * t + B = s := by
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
theorem FLine.inter_eq_empty_or_singleton {F : Subfield ℝ} (L L' : FLine F) (hne : {p : ℝ × ℝ | MemFLine L p} ≠ {p : ℝ × ℝ | MemFLine L' p}) : {p : ℝ × ℝ | MemFLine L p ∧ MemFLine L' p} = ∅ ∨ ∃ p : ℝ × ℝ, p.1 ∈ F ∧ p.2 ∈ F ∧ {q : ℝ × ℝ | MemFLine L q ∧ MemFLine L' q} = {p} := by
  by_cases hD : L.a * L'.b - L'.a * L.b = 0
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [MemFLine] at h1 h2
    obtain ⟨k, hk1, hk2, hk0⟩ := exists_prop_coeff_of_det_eq_zero L.ab_ne L'.ab_ne (by linarith)
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
theorem FLine.inter_circle_eq_empty_or_insert {F : Subfield ℝ} (L : FLine F) (C : FCircle F) : {p : ℝ × ℝ | MemFLine L p ∧ MemFCircle C p} = ∅ ∨ ∃ e : ℝ, e ∈ F ∧ 0 < e ∧ ∃ p q : ℝ × ℝ, InQuadPlane F e p ∧ InQuadPlane F e q ∧ {r : ℝ × ℝ | MemFLine L r ∧ MemFCircle C r} = insert p {q} := by
  by_cases hex : ∃ p : ℝ × ℝ, MemFLine L p ∧ MemFCircle C p
  · right
    obtain ⟨p0, hp0l, hp0c⟩ := hex
    simp only [MemFLine] at hp0l
    have hA0 : L.a ^ 2 + L.b ^ 2 ≠ 0 := by
      intro h
      rcases L.ab_ne with h' | h'
      · exact h' (eq_zero_of_sq_add_sq_eq_zero h).1
      · exact h' (eq_zero_of_sq_add_sq_eq_zero h).2
    have hAmem : L.a ^ 2 + L.b ^ 2 ∈ F := by rw [pow_two, pow_two]; exact Subfield.add_mem F (Subfield.mul_mem F L.ha L.ha) (Subfield.mul_mem F L.hb L.hb)
    have hp01mem : -(L.a * L.c) / (L.a ^ 2 + L.b ^ 2) ∈ F := Subfield.div_mem F (Subfield.neg_mem F (Subfield.mul_mem F L.ha L.hc)) hAmem
    have hp02mem : -(L.b * L.c) / (L.a ^ 2 + L.b ^ 2) ∈ F := Subfield.div_mem F (Subfield.neg_mem F (Subfield.mul_mem F L.hb L.hc)) hAmem
    have hBmem : -L.b ∈ F := Subfield.neg_mem F L.hb
    set p01 : ℝ := -(L.a * L.c) / (L.a ^ 2 + L.b ^ 2) with hp01def
    set p02 : ℝ := -(L.b * L.c) / (L.a ^ 2 + L.b ^ 2) with hp02def
    set t0 : ℝ := (L.a * p0.2 - L.b * p0.1) / (L.a ^ 2 + L.b ^ 2) with ht0def
    have ht0 : (L.a ^ 2 + L.b ^ 2) * t0 = L.a * p0.2 - L.b * p0.1 := by rw [ht0def, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ hA0
    obtain ⟨hpar1, hpar2⟩ := line_param_of_mem_line hp0l hA0 ht0
    rw [← hp01def] at hpar1
    rw [← hp02def] at hpar2
    set Bq : ℝ := 2 * ((p01 - C.cx) * (-L.b) + (p02 - C.cy) * L.a) with hBqdef
    set Cq : ℝ := (p01 - C.cx) ^ 2 + (p02 - C.cy) ^ 2 - C.r * C.r with hCqdef
    have hcirc0 : MemFCircle C ⟨p01 + t0 * (-L.b), p02 + t0 * L.a⟩ := by rw [← hpar1, ← hpar2]; exact hp0c
    have hAeq : L.a ^ 2 + L.b ^ 2 = (-L.b) ^ 2 + L.a ^ 2 := by ring
    have hroot0 : (L.a ^ 2 + L.b ^ 2) * t0 ^ 2 + Bq * t0 + Cq = 0 := (mem_circle_iff_quadratic hAeq hBqdef hCqdef).mp hcirc0
    set Δ : ℝ := Bq ^ 2 - 4 * (L.a ^ 2 + L.b ^ 2) * Cq with hΔdef
    have hw1m : (p01 - C.cx) * (-L.b) ∈ F := Subfield.mul_mem F (Subfield.sub_mem F hp01mem C.hcx) hBmem
    have hw2m : (p02 - C.cy) * L.a ∈ F := Subfield.mul_mem F (Subfield.sub_mem F hp02mem C.hcy) L.ha
    have hBqmem : Bq ∈ F := by rw [hBqdef]; exact Subfield.mul_mem F two_mem_subfield (Subfield.add_mem F hw1m hw2m)
    have hu1m : (p01 - C.cx) ^ 2 ∈ F := by rw [pow_two]; exact Subfield.mul_mem F (Subfield.sub_mem F hp01mem C.hcx) (Subfield.sub_mem F hp01mem C.hcx)
    have hu2m : (p02 - C.cy) ^ 2 ∈ F := by rw [pow_two]; exact Subfield.mul_mem F (Subfield.sub_mem F hp02mem C.hcy) (Subfield.sub_mem F hp02mem C.hcy)
    have hCqmem : Cq ∈ F := by rw [hCqdef]; exact Subfield.sub_mem F (Subfield.add_mem F hu1m hu2m) (Subfield.mul_mem F C.hr C.hr)
    have hBq2m : Bq ^ 2 ∈ F := by rw [pow_two]; exact Subfield.mul_mem F hBqmem hBqmem
    have hΔmem : Δ ∈ F := by rw [hΔdef]; exact Subfield.sub_mem F hBq2m (Subfield.mul_mem F (Subfield.mul_mem F four_mem_subfield hAmem) hCqmem)
    have hΔsq : (2 * (L.a ^ 2 + L.b ^ 2) * t0 + Bq) ^ 2 = Δ := sq_eq_disc_of_quadratic_root hroot0 hΔdef
    have hΔle : 0 ≤ Δ := by rw [← hΔsq]; exact sq_nonneg _
    have hsΔ : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔle
    have hsΔ2 : (Real.sqrt Δ) ^ 2 = Δ := by rw [pow_two]; exact hsΔ
    have hroot' : Real.sqrt Δ * Real.sqrt Δ = Bq ^ 2 - 4 * (L.a ^ 2 + L.b ^ 2) * Cq := by rw [hsΔ, hΔdef]
    obtain ⟨tpos, hqpos, h2pos⟩ := exists_quadratic_root_of_sq_eq_disc hA0 hroot'
    obtain ⟨tneg, hqneg, h2neg⟩ := exists_quadratic_root_of_sq_eq_disc hA0 (by rw [neg_mul_neg]; exact hroot')
    have hAt : 2 * (L.a ^ 2 + L.b ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hA0
    have hPposin : MemFLine L ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ ∧ MemFCircle C ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ := by
      constructor
      · exact mem_line_of_line_param hA0 (by rw [← hp01def]) (by rw [← hp02def])
      · exact (mem_circle_iff_quadratic hAeq hBqdef hCqdef).mpr hqpos
    have hPnegin : MemFLine L ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ ∧ MemFCircle C ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ := by
      constructor
      · exact mem_line_of_line_param hA0 (by rw [← hp01def]) (by rw [← hp02def])
      · exact (mem_circle_iff_quadratic hAeq hBqdef hCqdef).mpr hqneg
    have hchar : ∀ q : ℝ × ℝ, MemFLine L q ∧ MemFCircle C q → q = ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩ ∨ q = ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩ := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [MemFLine] at hq1
      set tq : ℝ := (L.a * q.2 - L.b * q.1) / (L.a ^ 2 + L.b ^ 2) with htqdef
      have htq : (L.a ^ 2 + L.b ^ 2) * tq = L.a * q.2 - L.b * q.1 := by rw [htqdef, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ hA0
      obtain ⟨hpar1, hpar2⟩ := line_param_of_mem_line hq1 hA0 htq
      rw [← hp01def] at hpar1
      rw [← hp02def] at hpar2
      have hcircq : MemFCircle C ⟨p01 + tq * (-L.b), p02 + tq * L.a⟩ := by rw [← hpar1, ← hpar2]; exact hq2
      have hrootq : (L.a ^ 2 + L.b ^ 2) * tq ^ 2 + Bq * tq + Cq = 0 := (mem_circle_iff_quadratic hAeq hBqdef hCqdef).mp hcircq
      have hΔq : (2 * (L.a ^ 2 + L.b ^ 2) * tq + Bq) ^ 2 = Δ := sq_eq_disc_of_quadratic_root hrootq hΔdef
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
      have htposmem : tpos ∈ F := by rw [htposp]; exact Subfield.div_mem F (Subfield.neg_mem F hBqmem) (Subfield.mul_mem F two_mem_subfield hAmem)
      have htnegmem : tneg ∈ F := by rw [htnegp]; exact Subfield.div_mem F (Subfield.neg_mem F hBqmem) (Subfield.mul_mem F two_mem_subfield hAmem)
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
      have hu1mem : p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.sub_mem F hp01mem (Subfield.div_mem F (Subfield.mul_mem F hBqmem hBmem) (Subfield.mul_mem F two_mem_subfield hAmem))
      have hv1mem : (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F hBmem (Subfield.mul_mem F two_mem_subfield hAmem)
      have hu2mem : p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.sub_mem F hp02mem (Subfield.div_mem F (Subfield.mul_mem F hBqmem L.ha) (Subfield.mul_mem F two_mem_subfield hAmem))
      have hv2mem : L.a / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F L.ha (Subfield.mul_mem F two_mem_subfield hAmem)
      have hv2mem' : (-L.a) / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F (Subfield.neg_mem F L.ha) (Subfield.mul_mem F two_mem_subfield hAmem)
      have hv1mem' : L.b / (2 * (L.a ^ 2 + L.b ^ 2)) ∈ F := Subfield.div_mem F L.hb (Subfield.mul_mem F two_mem_subfield hAmem)
      exact ⟨Δ, hΔmem, lt_of_le_of_ne hΔle (Ne.symm hΔz), ⟨p01 + tpos * (-L.b), p02 + tpos * L.a⟩, ⟨p01 + tneg * (-L.b), p02 + tneg * L.a⟩, ⟨p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)), (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)), p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)), L.a / (2 * (L.a ^ 2 + L.b ^ 2)), hu1mem, hv1mem, hu2mem, hv2mem, g1, g2⟩, ⟨p01 - Bq * (-L.b) / (2 * (L.a ^ 2 + L.b ^ 2)), L.b / (2 * (L.a ^ 2 + L.b ^ 2)), p02 - Bq * L.a / (2 * (L.a ^ 2 + L.b ^ 2)), (-L.a) / (2 * (L.a ^ 2 + L.b ^ 2)), hu1mem, hv1mem', hu2mem, hv2mem', g3, g4⟩, hset⟩
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    exact hex ⟨p, hp⟩

/-- FT `ef24`, clause (3).  Let `C ≠ C′` be `F`-circles.  Then `C ∩ C′ = ∅` or consists of one or
two points in the `F[√e]`-plane for some `e ∈ F` with `e > 0`.

Encoding: `C ≠ C′` is encoded as distinctness of the defining data (`C.cx ≠ C'.cx ∨ C.cy ≠ C'.cy ∨
C.r ≠ C'.r`), which is equivalent to distinctness of the structures since the data determine the
circle.  "One or two points in the `F[√e]`-plane" is as in `FLine.inter_circle_eq_empty_or_insert` (`InQuadPlane`, `insert p {q}`).

Proof idea: subtracting the two circle equations gives the radical axis, an `F`-line
`2 (cx - cx′) x + 2 (cy - cy′) y + (cx′² + cy′² - cx² - cy² - r′² + r²) = 0` with a genuinely
nonzero coefficient pair when the centres differ.  A common point of the two circles is exactly a
common point of this `F`-line and `C`, so clause (2) applies.  If the centres coincide, then `C ≠ C′`
forces `r ≠ r′`, and a point on both circles would give `r² = r′²`, hence `r = r′` — so the
intersection is empty. -/
theorem FCircle.inter_circle_eq_empty_or_insert {F : Subfield ℝ} (C C' : FCircle F) (hC : C.cx ≠ C'.cx ∨ C.cy ≠ C'.cy ∨ C.r ≠ C'.r) : {p : ℝ × ℝ | MemFCircle C p ∧ MemFCircle C' p} = ∅ ∨ ∃ e : ℝ, e ∈ F ∧ 0 < e ∧ ∃ p q : ℝ × ℝ, InQuadPlane F e p ∧ InQuadPlane F e q ∧ {r : ℝ × ℝ | MemFCircle C r ∧ MemFCircle C' r} = insert p {q} := by
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
    have ha3mem : a3 ∈ F := by rw [ha3def]; exact Subfield.mul_mem F two_mem_subfield (Subfield.sub_mem F C.hcx C'.hcx)
    have hb3mem : b3 ∈ F := by rw [hb3def]; exact Subfield.mul_mem F two_mem_subfield (Subfield.sub_mem F C.hcy C'.hcy)
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
    have hfin := FLine.inter_circle_eq_empty_or_insert ⟨a3, b3, c3, ha3mem, hb3mem, hc3mem, hline⟩ C
    rw [hseteq'] at hfin
    exact hfin

/-!
**Encoding note (FT `ef25`–`ef30`).**  FT defines constructible numbers geometrically
(coordinates of points obtained by ruler-and-compass constructions, cf. `ef24`).  We
formalise constructibility as an inductive predicate `Constructible : ℝ → Prop` generated
by the rationals, the field operations, and square roots of positive elements.  With this
encoding, FT `ef25` becomes the closure properties of the predicate (its intro rules),
FT `ef26` (i) says the predicate is the carrier of a subfield of ℝ, and FT `ef26` (ii) is
the quadratic-tower characterisation; the geometric input of FT's `ef24` (constructed
points lie in `F[√e]`) is the separate item `ef24` above and is not needed here.
-/

/-- **FT `ef25`, encoding.**  A real number is *constructible* iff it is generated from the
rationals by addition, negation, multiplication, inversion, and square roots of positive
elements — equivalently (FT `ef26` (ii)) iff it lies in a quadratic tower
`ℚ[√a₁, …, √a_r]` over ℚ inside ℝ.  The intro rules mirror the straight-edge-and-compass
operations: rational points, sums, differences, products, quotients, and lengths of
diagonals (square roots). -/
inductive Constructible : ℝ → Prop
  | ofRat (q : ℚ) : Constructible (q : ℝ)
  | ofAdd {x y : ℝ} : Constructible x → Constructible y → Constructible (x + y)
  | ofNeg {x : ℝ} : Constructible x → Constructible (-x)
  | ofMul {x y : ℝ} : Constructible x → Constructible y → Constructible (x * y)
  | ofInv {x : ℝ} : Constructible x → Constructible (x⁻¹)
  | ofSqrt {x : ℝ} : 0 < x → Constructible x → Constructible (√x)

/-- Rational numbers are constructible.  The proof is trivial (constructor `ofRat`). -/
theorem constructible_of_ratCast (q : ℚ) : Constructible (q : ℝ) := Constructible.ofRat q

/-- `0` is constructible. -/
theorem constructible_zero : Constructible (0 : ℝ) := by
  rw [← Rat.cast_zero (α := ℝ)]
  exact Constructible.ofRat 0

/-- `1` is constructible. -/
theorem constructible_one : Constructible (1 : ℝ) := by
  rw [← Rat.cast_one (α := ℝ)]
  exact Constructible.ofRat 1

/-- **FT `ef25` (a), part 1.**  Constructible numbers are closed under addition.
The source proves this geometrically (perpendiculars/parallels, similar triangles); here it
is the defining closure of the constructibility predicate. -/
theorem constructible_add {c d : ℝ} (hc : Constructible c) (hd : Constructible d) :
    Constructible (c + d) := Constructible.ofAdd hc hd

/-- **FT `ef25` (a), part 2.**  Constructible numbers are closed under negation. -/
theorem constructible_neg {c : ℝ} (hc : Constructible c) : Constructible (-c) :=
  Constructible.ofNeg hc

/-- **FT `ef25` (a), part 3.**  Constructible numbers are closed under multiplication. -/
theorem constructible_mul {c d : ℝ} (hc : Constructible c) (hd : Constructible d) :
    Constructible (c * d) := Constructible.ofMul hc hd

/-- **FT `ef25` (a), part 4.**  Constructible numbers are closed under inversion
(no `c ≠ 0` hypothesis is needed since `0⁻¹ = 0` is constructible). -/
theorem constructible_inv {c : ℝ} (hc : Constructible c) : Constructible (c⁻¹) :=
  Constructible.ofInv hc

/-- **FT `ef25` (a), part 4'.**  Constructible numbers are closed under division
(`d ≠ 0` in FT's statement is automatic: `c / 0 = 0`). -/
theorem constructible_div {c d : ℝ} (hc : Constructible c) (hd : Constructible d) :
    Constructible (c / d) := by
  rw [div_eq_mul_inv]
  exact Constructible.ofMul hc (Constructible.ofInv hd)

/-- **FT `ef25` (b).**  If `c > 0` is constructible then so is `√c` (the positive square
root in ℝ, cf. FT's construction with the circle of radius `(c+1)/2`). -/
theorem constructible_sqrt {c : ℝ} (hc : 0 < c) (h : Constructible c) : Constructible (√c) :=
  Constructible.ofSqrt hc h

/-- **FT `ef26` (i).**  The set of constructible numbers is a field: it is the carrier of
this subfield of ℝ, by definition closed under `0, 1, +, -, *, ⁻¹` (this restates
`ef25` (a) together with the constructibility of `0` and `1`). -/
def ConstructibleField : Subfield ℝ where
  carrier := {x | Constructible x}
  zero_mem' := constructible_zero
  one_mem' := constructible_one
  add_mem' hx hy := Constructible.ofAdd hx hy
  neg_mem' hx := Constructible.ofNeg hx
  mul_mem' hx hy := Constructible.ofMul hx hy
  inv_mem' _x hx := Constructible.ofInv hx

/-- Membership in `ConstructibleField` is exactly constructibility. -/
theorem mem_ConstructibleField_iff (x : ℝ) : x ∈ ConstructibleField ↔ Constructible x :=
  Iff.rfl
/-! ### The geometric bridge (FT `ef24`–`ef26` → `Constructible`)

The source defines *constructible* geometrically (successive intersections of
lines through two already constructed points and circles with constructed
centre and constructed radius, starting from the unit length); `ef25`/`ef26`
are then proved geometrically via `ef24`.  The formalization encodes
constructibility as the inductive predicate `Constructible` above; the
following definitions and theorems provide the link: `GeoConstructiblePoint`
encodes FT's construction process, and the bridge theorem proves that every
constructed length of FT's geometric development satisfies `Constructible`, so the
impossibility results transfer to genuine straight-edge-and-compass
constructibility. -/

/-- The straight line through two points `p₁, p₂ ∈ ℝ × ℝ`, as a membership predicate: `q` lies on
it iff `(y₁ - y₂) x + (x₂ - x₁) y + (x₁ y₂ - x₂ y₁) = 0` (determinant form of the line equation).
For `p₁ ≠ p₂` this is the unique straight line through `p₁` and `p₂`. -/
def MemGeoLine (p₁ p₂ q : ℝ × ℝ) : Prop :=
  (p₁.2 - p₂.2) * q.1 + (p₂.1 - p₁.1) * q.2 + (p₁.1 * p₂.2 - p₂.1 * p₁.2) = 0

/-- The circle with centre `c ∈ ℝ × ℝ` and radius the constructed length `|a - b|` (the distance
between two constructed points `a`, `b`; FT: "radius a constructed length"), as a membership
predicate: `q` lies on it iff its squared distance to `c` equals `|a - b|²`. -/
def MemGeoCircle (c a b q : ℝ × ℝ) : Prop :=
  (q.1 - c.1) ^ 2 + (q.2 - c.2) ^ 2 = (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- FT, *Constructions with straight-edge and compass* (geometric encoding).
`GeoConstructiblePoint p` says that the point `p ∈ ℝ × ℝ` is obtainable from the two base points
`(0, 0)` and `(1, 0)` by the straight-edge-and-compass operations of FT:
* drawing the straight line through two already constructed points (`MemGeoLine`);
* drawing the circle with an already constructed centre `c` and radius a constructed length, i.e.
  the distance `|a - b|` between two already constructed points `a`, `b` (`MemGeoCircle`;
  a circle through a constructed point `o` is the special case `a = c`, `b = o`);
* forming the intersection points of two distinct constructed lines, of a constructed line with a
  constructed circle, and of two distinct constructed circles.

Distinctness of two lines (resp. two circles) is encoded, as in the `ef24` intersection theorems,
by distinctness of their point sets.  This is the minimal closure of the base points under the
three intersection operations, i.e. exactly the points "already constructed" in FT's sense. -/
inductive GeoConstructiblePoint : ℝ × ℝ → Prop
  | base1 : GeoConstructiblePoint (0, 0)
  | base2 : GeoConstructiblePoint (1, 0)
  | lineIntersect {p₁ p₂ q₁ q₂ r : ℝ × ℝ} :
      GeoConstructiblePoint p₁ → GeoConstructiblePoint p₂ → p₁ ≠ p₂ →
      GeoConstructiblePoint q₁ → GeoConstructiblePoint q₂ → q₁ ≠ q₂ →
      {s : ℝ × ℝ | MemGeoLine p₁ p₂ s} ≠ {s : ℝ × ℝ | MemGeoLine q₁ q₂ s} →
      MemGeoLine p₁ p₂ r → MemGeoLine q₁ q₂ r → GeoConstructiblePoint r
  | circleLineIntersect {p₁ p₂ c a b r : ℝ × ℝ} :
      GeoConstructiblePoint p₁ → GeoConstructiblePoint p₂ → p₁ ≠ p₂ →
      GeoConstructiblePoint c → GeoConstructiblePoint a → GeoConstructiblePoint b →
      MemGeoLine p₁ p₂ r → MemGeoCircle c a b r → GeoConstructiblePoint r
  | circleCircleIntersect {c₁ a₁ b₁ c₂ a₂ b₂ r : ℝ × ℝ} :
      GeoConstructiblePoint c₁ → GeoConstructiblePoint a₁ → GeoConstructiblePoint b₁ →
      GeoConstructiblePoint c₂ → GeoConstructiblePoint a₂ → GeoConstructiblePoint b₂ →
      {s : ℝ × ℝ | MemGeoCircle c₁ a₁ b₁ s} ≠ {s : ℝ × ℝ | MemGeoCircle c₂ a₂ b₂ s} →
      MemGeoCircle c₁ a₁ b₁ r → MemGeoCircle c₂ a₂ b₂ r → GeoConstructiblePoint r

/-- A real number (length) is *geometrically constructible* (FT) when it occurs as the
x-coordinate of a constructed point on the x-axis. -/
def GeoConstructible (x : ℝ) : Prop := GeoConstructiblePoint (x, 0)

/-- Constructible numbers are closed under subtraction. -/
theorem constructible_sub {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
    Constructible (x - y) := constructible_add hx (constructible_neg hy)

/-- The `F`-line through two points with constructible coordinates, when the points are distinct:
its membership predicate is (definitionally) `MemGeoLine`. -/
theorem exists_fline_geoLine {p₁ p₂ : ℝ × ℝ} (hne : p₁ ≠ p₂)
    (h : Constructible p₁.1 ∧ Constructible p₁.2 ∧ Constructible p₂.1 ∧ Constructible p₂.2) :
    ∃ L : FLine ConstructibleField, ∀ s, (MemFLine L s ↔ MemGeoLine p₁ p₂ s) := by
  have habne : p₁.2 - p₂.2 ≠ 0 ∨ p₂.1 - p₁.1 ≠ 0 := by
    rcases ne_or_eq p₁.2 p₂.2 with h1 | h1
    · exact Or.inl fun hc => h1 (sub_eq_zero.mp hc)
    · rcases ne_or_eq p₂.1 p₁.1 with h2 | h2
      · exact Or.inr fun hc => h2 (sub_eq_zero.mp hc)
      · exact absurd (Prod.ext_iff.mpr ⟨h2.symm, h1⟩) hne
  refine ⟨⟨p₁.2 - p₂.2, p₂.1 - p₁.1, p₁.1 * p₂.2 - p₂.1 * p₁.2,
    (mem_ConstructibleField_iff _).mpr (constructible_add h.2.1 (constructible_neg h.2.2.2)),
    (mem_ConstructibleField_iff _).mpr (constructible_add h.2.2.1 (constructible_neg h.1)),
    (mem_ConstructibleField_iff _).mpr (constructible_add (constructible_mul h.1 h.2.2.2)
      (constructible_neg (constructible_mul h.2.2.1 h.2.1))), habne⟩, fun s => Iff.rfl⟩

/-- The `F`-circle with centre `c` and radius the constructed length `|a - b|`, for points
`c, a, b` with constructible coordinates: its membership predicate is `MemGeoCircle` (the
`F`-radius is `√(|a - b|²)`, which is again constructible). -/
theorem exists_fcircle_geoCircle {c a b : ℝ × ℝ}
    (h : Constructible c.1 ∧ Constructible c.2 ∧ Constructible a.1 ∧ Constructible a.2 ∧
      Constructible b.1 ∧ Constructible b.2) :
    ∃ C : FCircle ConstructibleField, ∀ s, (MemFCircle C s ↔ MemGeoCircle c a b s) := by
  have hsub1 : Constructible (a.1 - b.1) := constructible_sub h.2.2.1 h.2.2.2.2.1
  have hsub2 : Constructible (a.2 - b.2) := constructible_sub h.2.2.2.1 h.2.2.2.2.2
  have hsq : Constructible ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    rw [pow_two, pow_two]
    exact constructible_add (constructible_mul hsub1 hsub1) (constructible_mul hsub2 hsub2)
  have hnonneg : 0 ≤ (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hrmem : Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) ∈ ConstructibleField := by
    by_cases hz : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 = 0
    · rw [hz, Real.sqrt_zero]; exact (mem_ConstructibleField_iff _).mpr constructible_zero
    · exact (mem_ConstructibleField_iff _).mpr
        (constructible_sqrt (lt_of_le_of_ne hnonneg (Ne.symm hz)) hsq)
  refine ⟨⟨c.1, c.2, Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2),
    (mem_ConstructibleField_iff _).mpr h.1, (mem_ConstructibleField_iff _).mpr h.2.1, hrmem,
    Real.sqrt_nonneg _⟩, ?_⟩
  intro s
  simp only [MemFCircle, MemGeoCircle]
  rw [Real.mul_self_sqrt hnonneg]

/-- Both coordinates of a point in the `F[√e]`-plane of `F = ConstructibleField` are
constructible: they are of the form `u + v √e` with `u, v ∈ F`, and `√e` is constructible. -/
theorem constructible_coords_of_inQuadPlane {e : ℝ} (hepos : 0 < e) (he : Constructible e)
    {p : ℝ × ℝ} (h : InQuadPlane ConstructibleField e p) :
    Constructible p.1 ∧ Constructible p.2 := by
  obtain ⟨u, v, w, z, hu, hv, hw, hz, hx, hy⟩ := h
  have hsqrt : Constructible (Real.sqrt e) := constructible_sqrt hepos he
  refine ⟨?_, ?_⟩
  · rw [hx]
    exact constructible_add ((mem_ConstructibleField_iff _).mp hu)
      (constructible_mul ((mem_ConstructibleField_iff _).mp hv) hsqrt)
  · rw [hy]
    exact constructible_add ((mem_ConstructibleField_iff _).mp hw)
      (constructible_mul ((mem_ConstructibleField_iff _).mp hz) hsqrt)

/-- **The geometric bridge** (FT `ef24`–`ef26`).  Every coordinate of a straight-edge-and-compass
constructed point is a constructible number.

Proof idea: induction on the derivation of `GeoConstructiblePoint`.  The base points `(0, 0)`,
`(1, 0)` have constructible coordinates.  If two distinct lines are drawn through points whose
coordinates are constructible, their coefficient triples `y₁ - y₂, x₂ - x₁, x₁ y₂ - x₂ y₁` are
constructible, so they are `F`-lines of `F = ConstructibleField`; by `ef24` (1) their intersection
point, if nonempty, has coordinates in `F`, hence constructible.  For line ∩ circle and
circle ∩ circle, the `F`-circle with centre `c` through `o` has `F`-radius
`√((o₁ - c₁)² + (o₂ - c₂)²)`, again constructible; by `ef24` (2), (3) the intersection points lie
in the `F[√e]`-plane for some constructible `e > 0`, and coordinates `u + v √e` with `u, v ∈ F`
are constructible. -/
theorem constructible_coords_of_geoPoint {p : ℝ × ℝ} (h : GeoConstructiblePoint p) :
    Constructible p.1 ∧ Constructible p.2 := by
  induction h with
  | base1 => exact ⟨constructible_zero, constructible_zero⟩
  | base2 => exact ⟨constructible_one, constructible_zero⟩
  | @lineIntersect p₁ p₂ q₁ q₂ r hp1 hp2 hne1 hq₁ hq₂ hne2 hset hr1 hr2 ih1 ih2 ih3 ih4 =>
    obtain ⟨L₁, hL₁⟩ := exists_fline_geoLine hne1 ⟨ih1.1, ih1.2, ih2.1, ih2.2⟩
    obtain ⟨L₂, hL₂⟩ := exists_fline_geoLine hne2 ⟨ih3.1, ih3.2, ih4.1, ih4.2⟩
    have e1 : {s : ℝ × ℝ | MemFLine L₁ s} = {s : ℝ × ℝ | MemGeoLine p₁ p₂ s} :=
      Set.ext fun s => hL₁ s
    have e2 : {s : ℝ × ℝ | MemFLine L₂ s} = {s : ℝ × ℝ | MemGeoLine q₁ q₂ s} :=
      Set.ext fun s => hL₂ s
    have hsetF : {s : ℝ × ℝ | MemFLine L₁ s} ≠ {s : ℝ × ℝ | MemFLine L₂ s} := by
      rw [e1, e2]; exact hset
    rcases FLine.inter_eq_empty_or_singleton L₁ L₂ hsetF with hempty | ⟨P, hP1, hP2, hsingle⟩
    · exfalso
      have hrin : r ∈ {s : ℝ × ℝ | MemFLine L₁ s ∧ MemFLine L₂ s} :=
        ⟨(hL₁ r).mpr hr1, (hL₂ r).mpr hr2⟩
      rw [hempty] at hrin
      simp at hrin
    · have hrin : r ∈ {s : ℝ × ℝ | MemFLine L₁ s ∧ MemFLine L₂ s} :=
        ⟨(hL₁ r).mpr hr1, (hL₂ r).mpr hr2⟩
      rw [hsingle] at hrin
      rw [Set.mem_singleton_iff.mp hrin]
      exact ⟨(mem_ConstructibleField_iff _).mp hP1, (mem_ConstructibleField_iff _).mp hP2⟩
  | @circleLineIntersect p₁ p₂ c a b r hp1 hp2 hne1 hc ha hb hr1 hr2 ih1 ih2 ih3 ih4 ih5 =>
    obtain ⟨L, hL⟩ := exists_fline_geoLine hne1 ⟨ih1.1, ih1.2, ih2.1, ih2.2⟩
    obtain ⟨C, hC⟩ := exists_fcircle_geoCircle
      ⟨ih3.1, ih3.2, ih4.1, ih4.2, ih5.1, ih5.2⟩
    rcases FLine.inter_circle_eq_empty_or_insert L C with hempty | ⟨e, he, hepos, P, Q, hPq, hQq, hsingle⟩
    · exfalso
      have hrin : r ∈ {s : ℝ × ℝ | MemFLine L s ∧ MemFCircle C s} :=
        ⟨(hL r).mpr hr1, (hC r).mpr hr2⟩
      rw [hempty] at hrin
      simp at hrin
    · have hrin : r ∈ {s : ℝ × ℝ | MemFLine L s ∧ MemFCircle C s} :=
        ⟨(hL r).mpr hr1, (hC r).mpr hr2⟩
      rw [hsingle] at hrin
      have hquad : InQuadPlane ConstructibleField e r := by
        rcases Set.mem_insert_iff.mp hrin with hre | hre
        · rw [hre]; exact hPq
        · rw [Set.mem_singleton_iff.mp hre]; exact hQq
      exact constructible_coords_of_inQuadPlane hepos ((mem_ConstructibleField_iff _).mp he) hquad
  | @circleCircleIntersect c₁ a₁ b₁ c₂ a₂ b₂ r hp1 hp2 hp3 hp4 hp5 hp6 hset hr1 hr2 ih1 ih2 ih3 ih4 ih5 ih6 =>
    obtain ⟨C, hC⟩ := exists_fcircle_geoCircle
      ⟨ih1.1, ih1.2, ih2.1, ih2.2, ih3.1, ih3.2⟩
    obtain ⟨C', hC'⟩ := exists_fcircle_geoCircle
      ⟨ih4.1, ih4.2, ih5.1, ih5.2, ih6.1, ih6.2⟩
    have e1 : {s : ℝ × ℝ | MemFCircle C s} = {s : ℝ × ℝ | MemGeoCircle c₁ a₁ b₁ s} :=
      Set.ext fun s => hC s
    have e2 : {s : ℝ × ℝ | MemFCircle C' s} = {s : ℝ × ℝ | MemGeoCircle c₂ a₂ b₂ s} :=
      Set.ext fun s => hC' s
    have hCne : C.cx ≠ C'.cx ∨ C.cy ≠ C'.cy ∨ C.r ≠ C'.r := by
      by_contra hcon
      push Not at hcon
      refine hset ?_
      rw [← e1, ← e2]
      exact Set.ext fun s => by
        simp only [MemFCircle, hcon.1, hcon.2.1, hcon.2.2]
    rcases FCircle.inter_circle_eq_empty_or_insert C C' hCne with hempty | ⟨e, he, hepos, P, Q, hPq, hQq, hsingle⟩
    · exfalso
      have hrin : r ∈ {s : ℝ × ℝ | MemFCircle C s ∧ MemFCircle C' s} :=
        ⟨(hC r).mpr hr1, (hC' r).mpr hr2⟩
      rw [hempty] at hrin
      simp at hrin
    · have hrin : r ∈ {s : ℝ × ℝ | MemFCircle C s ∧ MemFCircle C' s} :=
        ⟨(hC r).mpr hr1, (hC' r).mpr hr2⟩
      rw [hsingle] at hrin
      have hquad : InQuadPlane ConstructibleField e r := by
        rcases Set.mem_insert_iff.mp hrin with hre | hre
        · rw [hre]; exact hPq
        · rw [Set.mem_singleton_iff.mp hre]; exact hQq
      exact constructible_coords_of_inQuadPlane hepos ((mem_ConstructibleField_iff _).mp he) hquad
/-- **The geometric bridge for lengths** (FT).  Every straight-edge-and-compass constructible
length is a constructible number (`Constructible`). -/
theorem constructible_of_geo {x : ℝ} (h : GeoConstructible x) : Constructible x :=
  (constructible_coords_of_geoPoint h).1


/-! ### The reverse geometric bridge (`Constructible` → `GeoConstructible`)

The source proves `ef25`/`ef26` geometrically, i.e. for straight-edge-and-compass
constructibility, while the formalization so far only had the forward bridge
`constructible_of_geo`.  The following block closes the gap: from the algebraic
predicate `Constructible` it reconstructs the geometric derivation, using only
explicit straight-edge-and-compass constructions with concrete coordinates
(whose line/circle memberships are elementary ring identities).  -/

/-- Technical lemma.  Two points with different first coordinates are different points.  The
proof is trivial (transport of the equality through `Prod.fst`). -/
theorem pair_fst_ne {a b c d : ℝ} (h : a ≠ c) : (a, b) ≠ (c, d) := fun he => h (congrArg Prod.fst he)

/-- Technical lemma.  Two points with different second coordinates are different points.  The
proof is trivial (transport of the equality through `Prod.snd`). -/
theorem pair_snd_ne {a b c d : ℝ} (h : b ≠ d) : (a, b) ≠ (c, d) := fun he => h (congrArg Prod.snd he)

/-- Technical lemma.  Two line predicates that differ at a point `w` have different solution
sets: the sets are equal only if both predicates agree everywhere, and membership transports
along set equality.  The proof is trivial (contraposition on `w`). -/
theorem lineSet_ne {p₁ p₂ q₁ q₂ w : ℝ × ℝ}
    (h₁ : MemGeoLine p₁ p₂ w) (h₂ : ¬ MemGeoLine q₁ q₂ w) :
    {s : ℝ × ℝ | MemGeoLine p₁ p₂ s} ≠ {s : ℝ × ℝ | MemGeoLine q₁ q₂ s} := by
  intro hset
  apply h₂
  have hw : w ∈ {s : ℝ × ℝ | MemGeoLine q₁ q₂ s} :=
    hset ▸ (h₁ : w ∈ {s : ℝ × ℝ | MemGeoLine p₁ p₂ s})
  exact hw

/-- Technical lemma.  Two circle predicates that differ at a point `w` have different solution
sets.  The proof is trivial (contraposition on `w`). -/

theorem circleSet_ne {c₁ a₁ b₁ c₂ a₂ b₂ w : ℝ × ℝ}
    (h₁ : MemGeoCircle c₁ a₁ b₁ w) (h₂ : ¬ MemGeoCircle c₂ a₂ b₂ w) :
    {s : ℝ × ℝ | MemGeoCircle c₁ a₁ b₁ s} ≠ {s : ℝ × ℝ | MemGeoCircle c₂ a₂ b₂ s} := by
  intro hset
  apply h₂
  have hw : w ∈ {s : ℝ × ℝ | MemGeoCircle c₂ a₂ b₂ s} :=
    hset ▸ (h₁ : w ∈ {s : ℝ × ℝ | MemGeoCircle c₁ a₁ b₁ s})
  exact hw

/-- Technical lemma.  Membership in the x-axis (the line through `(0, 0)` and `(1, 0)`) is
exactly having zero second coordinate.  The proof is trivial (linear arithmetic on the line
equation `0·x + 1·y + 0 = 0`... i.e. `y = 0`). -/
theorem memGeoLine_axis {q : ℝ × ℝ} : MemGeoLine (0, 0) (1, 0) q ↔ q.2 = 0 := by
  constructor
  · intro h; simp only [MemGeoLine] at h; linarith [h]
  · intro h; simp only [MemGeoLine]; linarith [h]

/-- Technical lemma.  Membership in the vertical line through `(x, 2)` and `(x, -2)` is exactly
having first coordinate `x`.  The proof is trivial (linear arithmetic). -/
theorem memGeoLine_vert {x : ℝ} {q : ℝ × ℝ} : MemGeoLine (x, 2) (x, -2) q ↔ q.1 = x := by
  constructor
  · intro h; simp only [MemGeoLine] at h; linarith [h]
  · intro h; simp only [MemGeoLine]; linarith [h]

/-- Technical lemma.  Membership in the horizontal line at height `y` (through `(0, y)` and
`(1, y)`) is exactly having second coordinate `y`.  The proof is trivial (linear arithmetic). -/
theorem memGeoLine_horiz {y : ℝ} {q : ℝ × ℝ} : MemGeoLine (0, y) (1, y) q ↔ q.2 = y := by
  constructor
  · intro h; simp only [MemGeoLine] at h; linarith [h]
  · intro h; simp only [MemGeoLine]; linarith [h]

/-- `0` is geometrically constructible: it is the base point `(0, 0)`.  Trivial (constructor). -/
theorem geo_zero : GeoConstructible 0 := GeoConstructiblePoint.base1

/-- `1` is geometrically constructible: it is the base point `(1, 0)` — the unit length.  Trivial
(constructor). -/
theorem geo_one : GeoConstructible 1 := GeoConstructiblePoint.base2

/-- The origin is a constructed point.  Trivial (constructor). -/
theorem geoPoint_zero : GeoConstructiblePoint (0 : ℝ × ℝ) := GeoConstructiblePoint.base1

/-- The point `(2, 0)`: the circle with centre `(1, 0)` through `(0, 0)` meets the x-axis again at
`(2, 0)`. -/
theorem geo_two : GeoConstructible 2 :=
  @GeoConstructiblePoint.circleLineIntersect (0, 0) (1, 0) (1, 0) (0, 0) (1, 0) (2, 0)
    GeoConstructiblePoint.base1 GeoConstructiblePoint.base2 (pair_fst_ne (by norm_num))
    GeoConstructiblePoint.base2 GeoConstructiblePoint.base1 GeoConstructiblePoint.base2
    (by simp only [MemGeoLine]; ring) (by simp only [MemGeoCircle]; ring)

/-- **Length addition** (Euclid-style two-point radius).  From constructed points `(c, 0)`, `(d, 0)`
on the x-axis, the circle centred `(c, 0)` with radius `|d|` (the distance between the constructed
points `(0, 0)` and `(d, 0)`) meets the x-axis at `(c + d, 0)`. -/
theorem geoPoint_add {c d : ℝ} (hc : GeoConstructiblePoint (c, 0))
    (hd : GeoConstructiblePoint (d, 0)) : GeoConstructiblePoint (c + d, 0) :=
  @GeoConstructiblePoint.circleLineIntersect (0, 0) (1, 0) (c, 0) (0, 0) (d, 0) (c + d, 0)
    GeoConstructiblePoint.base1 GeoConstructiblePoint.base2 (pair_fst_ne (by norm_num))
    hc GeoConstructiblePoint.base1 hd
    (by simp only [MemGeoLine]; ring) (by simp only [MemGeoCircle]; ring)

/-- **Length subtraction.**  Same circle as in `geoPoint_add`; the second intersection with the
x-axis is `(c - d, 0)`. -/
theorem geoPoint_sub {c d : ℝ} (hc : GeoConstructiblePoint (c, 0))
    (hd : GeoConstructiblePoint (d, 0)) : GeoConstructiblePoint (c - d, 0) :=
  @GeoConstructiblePoint.circleLineIntersect (0, 0) (1, 0) (c, 0) (0, 0) (d, 0) (c - d, 0)
    GeoConstructiblePoint.base1 GeoConstructiblePoint.base2 (pair_fst_ne (by norm_num))
    hc GeoConstructiblePoint.base1 hd
    (by simp only [MemGeoLine]; ring) (by simp only [MemGeoCircle]; ring)

/-- **Point reflection through the origin.**  The circle centred `(0, 0)` with radius `|c|` (the
distance between the constructed points `(c, 0)` and `(0, 0)`) meets the x-axis at `(-c, 0)`. -/
theorem geoPoint_neg {c : ℝ} (hc : GeoConstructiblePoint (c, 0)) : GeoConstructiblePoint (-c, 0) :=
  @GeoConstructiblePoint.circleLineIntersect (0, 0) (1, 0) (0, 0) (c, 0) (0, 0) (-c, 0)
    GeoConstructiblePoint.base1 GeoConstructiblePoint.base2 (pair_fst_ne (by norm_num))
    GeoConstructiblePoint.base1 hc GeoConstructiblePoint.base1
    (by simp only [MemGeoLine]; ring) (by simp only [MemGeoCircle]; ring)

/-- Technical lemma.  Constructibility of a point transfers along equality of points.  The proof
is trivial (rewrite). -/
theorem geoPoint_congr {p q : ℝ × ℝ} (h : GeoConstructiblePoint p) (he : p = q) :
    GeoConstructiblePoint q := he ▸ h

/-- Technical lemma.  A constructed point `(a, 0)` on the x-axis yields the constructed point
`(b, 0)` when `a = b`.  The proof is trivial (rewrite of the equality in the hypothesis). -/
theorem geoPoint_x_congr {a b : ℝ} (he : a = b) (h : GeoConstructiblePoint (a, 0)) :
    GeoConstructiblePoint (b, 0) := by
  rw [he] at h; exact h

/-- **Halving** (perpendicular bisector).  The two circles of radius `|c|` centred at `(0, 0)` and
`(c, 0)` meet at `(c/2, ±√3 c/2)`; the line through these two points is the perpendicular bisector
`x = c/2` of the segment from `(0, 0)` to `(c, 0)`, and it meets the x-axis at `(c/2, 0)`. -/
theorem geoPoint_half {c : ℝ} (hc : GeoConstructiblePoint (c, 0)) (hc0 : c ≠ 0) :
    GeoConstructiblePoint (c / 2, 0) := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3sq : (Real.sqrt 3 * c / 2) ^ 2 = 3 * c ^ 2 / 4 := by rw [div_pow, mul_pow, h3]; ring
  have h3ne : Real.sqrt 3 ≠ 0 := by
    intro h0
    have h := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
    rw [h0] at h
    norm_num at h
  have hs0 : Real.sqrt 3 * c / 2 ≠ 0 := by
    intro h0
    have hz : Real.sqrt 3 * c = 0 := by linarith [h0]
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact h3ne h1
    · exact hc0 h1
  have m1 : MemGeoCircle (0, 0) (0, 0) (c, 0) (c / 2, Real.sqrt 3 * c / 2) := by
    simp only [MemGeoCircle, sub_zero]; rw [h3sq]; ring
  have m2 : MemGeoCircle (c, 0) (0, 0) (c, 0) (c / 2, Real.sqrt 3 * c / 2) := by
    simp only [MemGeoCircle, sub_zero]; rw [h3sq]; ring
  have w1 : MemGeoCircle (0, 0) (0, 0) (c, 0) (c, 0) := by
    simp only [MemGeoCircle, sub_zero]; ring
  have hnot2 : ¬ MemGeoCircle (c, 0) (0, 0) (c, 0) (c, 0) := by
    intro hmem
    simp only [MemGeoCircle, sub_zero] at hmem
    have h5 : (0 - c) ^ 2 = c ^ 2 := by ring
    have e : (c - c) ^ 2 = 0 := by ring
    rw [e, h5] at hmem
    have hz : c ^ 2 = 0 := by linarith [hmem]
    exact hc0 (sq_eq_zero_iff.mp hz)
  have hA : GeoConstructiblePoint (c / 2, Real.sqrt 3 * c / 2) :=
    @GeoConstructiblePoint.circleCircleIntersect (0, 0) (0, 0) (c, 0) (c, 0) (0, 0) (c, 0)
      (c / 2, Real.sqrt 3 * c / 2)
      GeoConstructiblePoint.base1 GeoConstructiblePoint.base1 hc hc GeoConstructiblePoint.base1 hc
      (circleSet_ne w1 hnot2) m1 m2
  have m1' : MemGeoCircle (0, 0) (0, 0) (c, 0) (c / 2, -(Real.sqrt 3 * c / 2)) := by
    simp only [MemGeoCircle, sub_zero]
    rw [show (-(Real.sqrt 3 * c / 2)) ^ 2 = (Real.sqrt 3 * c / 2) ^ 2 by ring, h3sq]; ring
  have m2' : MemGeoCircle (c, 0) (0, 0) (c, 0) (c / 2, -(Real.sqrt 3 * c / 2)) := by
    simp only [MemGeoCircle, sub_zero]
    rw [show (-(Real.sqrt 3 * c / 2)) ^ 2 = (Real.sqrt 3 * c / 2) ^ 2 by ring, h3sq]; ring
  have hB : GeoConstructiblePoint (c / 2, -(Real.sqrt 3 * c / 2)) :=
    @GeoConstructiblePoint.circleCircleIntersect (0, 0) (0, 0) (c, 0) (c, 0) (0, 0) (c, 0)
      (c / 2, -(Real.sqrt 3 * c / 2))
      GeoConstructiblePoint.base1 GeoConstructiblePoint.base1 hc hc GeoConstructiblePoint.base1 hc
      (circleSet_ne w1 hnot2) m1' m2'
  have hne' : Real.sqrt 3 * c / 2 ≠ -(Real.sqrt 3 * c / 2) := by
    intro h
    have hz : Real.sqrt 3 * c = 0 := by linarith [h]
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact h3ne h0
    · exact hc0 h0
  have x0' : MemGeoLine (c / 2, Real.sqrt 3 * c / 2) (c / 2, -(Real.sqrt 3 * c / 2))
      (c / 2, Real.sqrt 3 * c / 2) := by simp only [MemGeoLine]; ring
  have hnot'' : ¬ MemGeoLine (0, 0) (1, 0) (c / 2, Real.sqrt 3 * c / 2) :=
    fun hm => hs0 ((memGeoLine_axis).mp hm)
  have lv : MemGeoLine (c / 2, Real.sqrt 3 * c / 2) (c / 2, -(Real.sqrt 3 * c / 2)) (c / 2, 0) := by
    simp only [MemGeoLine]; ring
  have lx : MemGeoLine (0, 0) (1, 0) (c / 2, 0) := (memGeoLine_axis).mpr rfl
  exact @GeoConstructiblePoint.lineIntersect (c / 2, Real.sqrt 3 * c / 2)
    (c / 2, -(Real.sqrt 3 * c / 2)) (0, 0) (1, 0) (c / 2, 0)
    hA hB (pair_snd_ne hne') GeoConstructiblePoint.base1 GeoConstructiblePoint.base2
    (pair_fst_ne (by norm_num))
    (lineSet_ne x0' hnot'') lv lx

/-- The unit fraction `1/2`. -/
theorem geo_half_one : GeoConstructiblePoint ((1:ℝ) / 2, 0) :=
  geoPoint_half geo_one (by norm_num)

/-- The constant `3/2`. -/
theorem geo_three_halves : GeoConstructiblePoint ((3:ℝ) / 2, 0) :=
  geoPoint_x_congr (by norm_num : (1:ℝ) + 1 / 2 = 3 / 2) (geoPoint_add geo_one geo_half_one)

/-- The constant `5/2`. -/
theorem geo_five_halves : GeoConstructiblePoint ((5:ℝ) / 2, 0) :=
  geoPoint_x_congr (by norm_num : (2:ℝ) + 1 / 2 = 5 / 2) (geoPoint_add geo_two geo_half_one)

/-- **Verticals.**  For every constructed `x` the two points `(x, 2)` and `(x, -2)` are
constructed: they are the intersections of the equal circles of radius `5/2` (the distance between
the constructed points `(0, 0)` and `(5/2, 0)`) centred at the constructed points `(x - 3/2, 0)`
and `(x + 3/2, 0)`.  The line through them is the vertical `x = x`. -/
theorem geoPoint_vert {x : ℝ} (hx : GeoConstructible x) :
    GeoConstructiblePoint (x, 2) ∧ GeoConstructiblePoint (x, -2) := by
  have hcxm : GeoConstructiblePoint (x - 3 / 2, 0) := geoPoint_sub hx geo_three_halves
  have hcxp : GeoConstructiblePoint (x + 3 / 2, 0) := geoPoint_add hx geo_three_halves
  have mA1 : MemGeoCircle (x - 3 / 2, 0) (0, 0) (5 / 2, 0) (x, 2) := by
    simp only [MemGeoCircle]; ring
  have mA2 : MemGeoCircle (x + 3 / 2, 0) (0, 0) (5 / 2, 0) (x, 2) := by
    simp only [MemGeoCircle]; ring
  have wC1 : MemGeoCircle (x - 3 / 2, 0) (0, 0) (5 / 2, 0) (x - 4, 0) := by
    simp only [MemGeoCircle]; ring
  have hnotC2 : ¬ MemGeoCircle (x + 3 / 2, 0) (0, 0) (5 / 2, 0) (x - 4, 0) := by
    intro hmem
    simp only [MemGeoCircle] at hmem
    ring_nf at hmem
    norm_num at hmem
  have hA : GeoConstructiblePoint (x, 2) :=
    @GeoConstructiblePoint.circleCircleIntersect (x - 3 / 2, 0) (0, 0) (5 / 2, 0)
      (x + 3 / 2, 0) (0, 0) (5 / 2, 0) (x, 2)
      hcxm geoPoint_zero geo_five_halves hcxp geoPoint_zero geo_five_halves
      (circleSet_ne wC1 hnotC2) mA1 mA2
  have mA1' : MemGeoCircle (x - 3 / 2, 0) (0, 0) (5 / 2, 0) (x, -2) := by
    simp only [MemGeoCircle]; ring
  have mA2' : MemGeoCircle (x + 3 / 2, 0) (0, 0) (5 / 2, 0) (x, -2) := by
    simp only [MemGeoCircle]; ring
  have hB : GeoConstructiblePoint (x, -2) :=
    @GeoConstructiblePoint.circleCircleIntersect (x - 3 / 2, 0) (0, 0) (5 / 2, 0)
      (x + 3 / 2, 0) (0, 0) (5 / 2, 0) (x, -2)
      hcxm geoPoint_zero geo_five_halves hcxp geoPoint_zero geo_five_halves
      (circleSet_ne wC1 hnotC2) mA1' mA2'
  exact ⟨hA, hB⟩

/-- **Horizontals.**  For every constructed `y` the two points `(0, y)` and `(1, y)` are
constructed: the circle with centre `(0, 0)` (resp. `(1, 0)`) and radius `|y|` (the distance
between the constructed points `(0, 0)` and `(y, 0)`) meets the vertical `x = 0` (resp. `x = 1`)
at the point `(0, y)` (resp. `(1, y)`). -/
theorem geoPoint_horiz {y : ℝ} (hy : GeoConstructible y) :
    GeoConstructiblePoint (0, y) ∧ GeoConstructiblePoint (1, y) := by
  obtain ⟨z1, z2⟩ := geoPoint_vert (x := 0) geo_zero
  obtain ⟨w1, w2⟩ := geoPoint_vert (x := 1) geo_one
  have hA : GeoConstructiblePoint (0, y) :=
    @GeoConstructiblePoint.circleLineIntersect (0, 2) (0, -2) (0, 0) (0, 0) (y, 0) (0, y)
      z1 z2 (pair_snd_ne (by norm_num)) geoPoint_zero geoPoint_zero hy
      ((memGeoLine_vert).mpr rfl) (by simp only [MemGeoCircle, sub_zero]; ring)
  have hB : GeoConstructiblePoint (1, y) :=
    @GeoConstructiblePoint.circleLineIntersect (1, 2) (1, -2) (1, 0) (0, 0) (y, 0) (1, y)
      w1 w2 (pair_snd_ne (by norm_num)) geo_one geoPoint_zero hy
      ((memGeoLine_vert).mpr rfl) (by simp only [MemGeoCircle, sub_zero]; ring)
  exact ⟨hA, hB⟩

/-- **Grid points.**  For constructed `x`, `y` the point `(x, y)` is constructed: it is the
intersection of the vertical `x = x` (through `(x, 2)`, `(x, -2)`) with the horizontal `y = y`
(through `(0, y)`, `(1, y)`). -/
theorem geoPoint_grid {x y : ℝ} (hx : GeoConstructible x) (hy : GeoConstructible y) :
    GeoConstructiblePoint (x, y) := by
  obtain ⟨v1, v2⟩ := geoPoint_vert hx
  obtain ⟨h1, h2⟩ := geoPoint_horiz hy
  have sh : MemGeoLine (0, y) (1, y) (x + 1, y) := (memGeoLine_horiz).mpr rfl
  have gh : MemGeoLine (0, y) (1, y) (x, y) := (memGeoLine_horiz).mpr rfl
  have gv : MemGeoLine (x, 2) (x, -2) (x, y) := (memGeoLine_vert).mpr rfl
  exact @GeoConstructiblePoint.lineIntersect (0, y) (1, y) (x, 2) (x, -2) (x, y)
    h1 h2 (pair_fst_ne (by norm_num)) v1 v2 (pair_snd_ne (by norm_num))
    (lineSet_ne sh (fun hv => by linarith [(memGeoLine_vert).mp hv])) gh gv

/-- **Length transfer.**  From a constructed point `p` whose projection `(p.1, 0)` to the x-axis is
constructed, the distance `|p.2|` from `p` to its projection is a geometrically constructible
length: the circle centred `(0, 0)` with radius `|p.2|` (the distance between the constructed
points `p` and `(p.1, 0)`) meets the x-axis at `(p.2, 0)`. -/
theorem geoPoint_yTransfer {p : ℝ × ℝ} (hp : GeoConstructiblePoint p)
    (hpx : GeoConstructiblePoint (p.1, 0)) : GeoConstructible p.2 :=
  @GeoConstructiblePoint.circleLineIntersect (0, 0) (1, 0) (0, 0) p (p.1, 0) (p.2, 0)
    GeoConstructiblePoint.base1 GeoConstructiblePoint.base2 (pair_fst_ne (by norm_num))
    geoPoint_zero hp hpx
    ((memGeoLine_axis).mpr rfl)
    (by simp only [MemGeoCircle, sub_zero]; ring)

/-- **Multiplication** (intercept theorem with grid parallels).  For constructed `c`, `d` with
`c ≠ 0`: the line through `(c, 0)` and `(c + 1, d)` is parallel to the line through `(0, 0)` and
`(1, d)` (both have direction `(1, d)`); by the intercept theorem it meets the vertical `x = 0`
at `(0, -c·d)`, and length transfer plus origin reflection gives `(c * d, 0)`. -/
theorem geo_mul {c d : ℝ} (hc : GeoConstructible c) (hd : GeoConstructible d) :
    GeoConstructible (c * d) := by
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul]
    exact geo_zero
  · have hcd : GeoConstructiblePoint (c + 1, d) := geoPoint_grid (geoPoint_add hc geo_one) hd
    obtain ⟨z1, z2⟩ := geoPoint_vert (x := 0) geo_zero
    have m1 : MemGeoLine (c, 0) (c + 1, d) (0, -(c * d)) := by simp only [MemGeoLine]; ring
    have m2 : MemGeoLine (0, 2) (0, -2) (0, -(c * d)) := (memGeoLine_vert).mpr rfl
    have s1 : MemGeoLine (c, 0) (c + 1, d) (c, 0) := by simp only [MemGeoLine]; ring
    have hnot : ¬ MemGeoLine (0, 2) (0, -2) (c, 0) := fun hm => hc0 ((memGeoLine_vert).mp hm)
    have hr : GeoConstructiblePoint (0, -(c * d)) :=
      @GeoConstructiblePoint.lineIntersect (c, 0) (c + 1, d) (0, 2) (0, -2) (0, -(c * d))
        hc hcd (pair_fst_ne (fun h => by linarith [h])) z1 z2 (pair_snd_ne (by norm_num))
        (lineSet_ne s1 hnot) m1 m2
    have ht := geoPoint_yTransfer hr geoPoint_zero
    have hneg := geoPoint_neg ht
    rw [neg_neg] at hneg
    exact hneg

/-- **Reciprocal** (intercept theorem).  For constructed `d ≠ 0`: the line through `(1, 0)` and
`(1 + d, 1)` is parallel to the line through `(0, 0)` and `(d, 1)` (both have direction `(d, 1)`);
by the intercept theorem it meets the vertical `x = 0` at `(0, -d⁻¹)`, and length transfer plus
origin reflection gives `(d⁻¹, 0)`. -/
theorem geo_inv {d : ℝ} (hd : GeoConstructible d) (hd0 : d ≠ 0) : GeoConstructible (d⁻¹) := by
  have hpt : GeoConstructiblePoint (1 + d, 1) := geoPoint_grid (geoPoint_add geo_one hd) geo_one
  obtain ⟨z1, z2⟩ := geoPoint_vert (x := 0) geo_zero
  have m1 : MemGeoLine (1, 0) (1 + d, 1) (0, -(d⁻¹)) := by
    simp only [MemGeoLine]
    field_simp
    ring
  have m2 : MemGeoLine (0, 2) (0, -2) (0, -(d⁻¹)) := (memGeoLine_vert).mpr rfl
  have s1 : MemGeoLine (1, 0) (1 + d, 1) (1, 0) := by simp only [MemGeoLine]; ring
  have hnot : ¬ MemGeoLine (0, 2) (0, -2) (1, 0) :=
    fun hm => absurd (((memGeoLine_vert).mp hm).symm) (zero_ne_one : (0:ℝ) ≠ 1)
  have hr : GeoConstructiblePoint (0, -(d⁻¹)) :=
    @GeoConstructiblePoint.lineIntersect (1, 0) (1 + d, 1) (0, 2) (0, -2) (0, -(d⁻¹))
      geo_one hpt (pair_fst_ne (fun h => hd0 (by linarith [h]))) z1 z2 (pair_snd_ne (by norm_num))
      (lineSet_ne s1 hnot) m1 m2
  have ht := geoPoint_yTransfer hr geoPoint_zero
  have hneg := geoPoint_neg ht
  rw [neg_neg] at hneg
  exact hneg

/-- **Square roots** (semicircle construction).  For constructed `x > 0`: the circle with centre
`((x+1)/2, 0)` and radius `(x+1)/2` (the distance between the constructed points `(0, 0)` and
`((x+1)/2, 0)`) meets the vertical `x = 1` at `(1, ±√x)`, since `(1 - (x+1)/2)² + x = ((x+1)/2)²`
(Thales).  Length transfer with radius the distance from `(1, √x)` to the constructed point
`(1, 0)` then gives `(√x, 0)`. -/
theorem geo_sqrt {x : ℝ} (hx : 0 < x) (h : GeoConstructible x) : GeoConstructible (√x) := by
  have hm : GeoConstructiblePoint ((x + 1) / 2, 0) :=
    geoPoint_half (geoPoint_add h geo_one) (fun h0 => by linarith [h0])
  obtain ⟨v1, v2⟩ := geoPoint_vert (x := 1) geo_one
  have hp' : GeoConstructiblePoint (1, Real.sqrt x) :=
    @GeoConstructiblePoint.circleLineIntersect (1, 2) (1, -2) ((x + 1) / 2, 0) (0, 0)
      ((x + 1) / 2, 0) (1, Real.sqrt x)
      v1 v2 (pair_snd_ne (by norm_num)) hm geoPoint_zero hm
      ((memGeoLine_vert).mpr rfl)
      (by simp only [MemGeoCircle, sub_zero, Real.sq_sqrt (le_of_lt hx)]; ring)
  exact geoPoint_yTransfer hp' geo_one

/-- Geometric construction of the natural numbers (repeated addition of the unit). -/
theorem geo_nat (n : ℕ) : GeoConstructible (n : ℝ) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact geo_zero
  | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one]
      exact geoPoint_add ih geo_one

/-- Geometric construction of the integers (origin reflection of the natural numbers). -/
theorem geo_int (z : ℤ) : GeoConstructible (z : ℝ) := by
  rcases Int.eq_nat_or_neg z with ⟨n, hn | hn⟩
  · rw [hn, Int.cast_natCast]
    exact geo_nat n
  · rw [hn, Int.cast_neg, Int.cast_natCast]
    exact geoPoint_neg (geo_nat n)

/-- Geometric construction of the rationals: `q = q.num / q.den` via the intercept-theorem
reciprocal and product. -/
theorem geo_of_rat (q : ℚ) : GeoConstructible (q : ℝ) := by
  have hn : GeoConstructible ((q.num : ℤ) : ℝ) := geo_int q.num
  have hd : GeoConstructible ((q.den : ℝ)) := geo_nat q.den
  have hd0 : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Rat.pos q))
  have hinv : GeoConstructible ((q.den : ℝ)⁻¹) := geo_inv hd hd0
  have hmul : GeoConstructible ((q.num : ℝ) * (q.den : ℝ)⁻¹) := geo_mul hn hinv
  rw [Rat.cast_def]
  exact geoPoint_x_congr
    (show ((q.num : ℝ) / (q.den : ℝ)) = ((q.num : ℝ) * (q.den : ℝ)⁻¹) by
      rw [div_eq_inv_mul, mul_comm])
    hmul

/-- **The reverse bridge** (FT `ef25`, `ef26` for the geometric predicate).  Every constructible
number is geometrically constructible: it occurs as the x-coordinate of a straight-edge-and-compass
constructed point.

Proof idea: induction on the derivation of `Constructible`.  The rationals are constructed by
repeated addition of the unit and the intercept-theorem reciprocal; addition and subtraction by the
two-point-radius circle trick on the x-axis; negation by origin reflection; multiplication and
reciprocal by the intercept theorem (parallels to a constructed line are free once the constructed
grid is available: the line through `(c, 0)` and `(c + 1, d)` is parallel to the line through
`(0, 0)` and `(1, d)`); square roots by Thales' semicircle construction with centre
`((x+1)/2, 0)` through the vertical `x = 1`, plus length transfer. -/
theorem geo_of_constructible {x : ℝ} (h : Constructible x) : GeoConstructible x := by
  induction h with
  | ofRat q => exact geo_of_rat q
  | @ofAdd x y hx hy ihx ihy => exact geoPoint_add ihx ihy
  | @ofNeg x hx ihx => exact geoPoint_neg ihx
  | @ofMul x y hx hy ihx ihy => exact geo_mul ihx ihy
  | @ofInv x hx ihx =>
      by_cases hx0 : x = 0
      · rw [hx0, inv_zero]
        exact geo_zero
      · exact geo_inv ihx hx0
  | @ofSqrt x hpos hx ihx => exact geo_sqrt hpos ihx


/-- **FT `ef26` (ii), encoding.**  The quadratic tower obtained from ℚ by successively
adjoining the square roots of the elements of a list.  The list is read *right-to-left*:
the head is adjoined last, over the tower generated by the remaining elements, so that
`quadTower (a :: as) = quadTower as ⊔ ℚ⟮√a⟯`.  Reading the list backwards gives the
textbook order `ℚ[√a₁, …, √a_r]`. -/
noncomputable def quadTower : List ℝ → IntermediateField ℚ ℝ
  | [] => ⊥
  | a :: as =>
      IntermediateField.restrictScalars ℚ
        (IntermediateField.adjoin (quadTower as) {√a})

/-- **FT `ef26` (ii), encoding.**  Well-formedness of a quadratic tower: each listed element
`a` is positive (`a > 0`) and lies in the previous stage (the tower generated by the
elements to its right, i.e. by the earlier elements in textbook order). -/
inductive TowerOK : List ℝ → Prop
  | nil : TowerOK []
  | cons {a : ℝ} {as : List ℝ} (ha : 0 < a) (ham : a ∈ quadTower as) (h : TowerOK as) :
      TowerOK (a :: as)

/-- The empty tower is ℚ (as a subfield of ℝ). -/
theorem quadTower_nil : quadTower [] = ⊥ := rfl

/-- Each tower step is `K ⊔ ℚ⟮√a⟯` over the previous stage `K`. -/
theorem quadTower_cons (a : ℝ) (as : List ℝ) :
    quadTower (a :: as) = quadTower as ⊔ IntermediateField.adjoin ℚ {√a} :=
  IntermediateField.restrictScalars_adjoin_eq_sup ℚ _ _

/-- Concatenating towers: the left tower is contained in the concatenated tower
(used to find a common tower for sums and products). -/
theorem quadTower_le_append_left (as bs : List ℝ) :
    quadTower as ≤ quadTower (as ++ bs) := by
  induction as with
  | nil => exact bot_le
  | cons a as ih =>
    rw [List.cons_append, quadTower_cons, quadTower_cons]
    exact sup_le_sup_right ih _

/-- Concatenating towers: the right tower is contained in the concatenation. -/
theorem quadTower_le_append_right (as bs : List ℝ) :
    quadTower bs ≤ quadTower (as ++ bs) := by
  induction as with
  | nil => exact le_rfl
  | cons a as ih =>
    rw [List.cons_append, quadTower_cons]
    exact ih.trans (le_sup_left (b := IntermediateField.adjoin ℚ {√a}))

/-- Concatenating two well-formed towers yields a well-formed tower. -/
theorem towerOK_append (as bs : List ℝ) (h1 : TowerOK as) (h2 : TowerOK bs) :
    TowerOK (as ++ bs) := by
  induction as with
  | nil => exact h2
  | cons a as ih =>
    cases h1 with
    | cons ha ham hOK =>
      exact TowerOK.cons ha
        ((SetLike.le_def.mp (quadTower_le_append_left as bs)) ham)
        (ih hOK)

/-- One step of the converse tower direction: elements of `K ⊔ ℚ⟮√a⟯`, with `0 < a ∈ K`,
are constructible whenever the elements of `K` are.  Proof idea (cf. the source's use of
`ef25`): elements of `K ⊔ ℚ⟮√a⟯` lie in the subfield of ℝ generated by `K` and `√a`, and
that subfield is closed under the constructibility rules once `K` and `√a` are
constructible (`Subfield.closure_induction`). -/
theorem constructible_of_mem_sup {K : IntermediateField ℚ ℝ}
    (hK : ∀ x ∈ K, Constructible (x : ℝ)) {a : ℝ} (haK : a ∈ K) (hapos : 0 < a) {x : ℝ}
    (hx : x ∈ K ⊔ IntermediateField.adjoin ℚ {√a}) : Constructible x := by
  have hxc : x ∈ Subfield.closure ((K.toSubfield : Set ℝ) ∪ {√a}) := by
    have h1 : (K ⊔ IntermediateField.adjoin ℚ {√a}).toSubfield ≤
        Subfield.closure ((K.toSubfield : Set ℝ) ∪ {√a}) := by
      rw [IntermediateField.sup_toSubfield, IntermediateField.adjoin_toSubfield]
      refine sup_le ?_ ?_
      · exact SetLike.le_def.mpr fun z hz =>
          Subfield.subset_closure (Set.mem_union_left _ hz)
      · refine Subfield.closure_le.2 ?_
        refine Set.union_subset ?_ ?_
        · rintro y ⟨q, rfl⟩
          exact Subfield.subset_closure (Set.mem_union_left _
            (IntermediateField.mem_toSubfield K _ |>.2 (IntermediateField.algebraMap_mem K q)))
        · exact fun z hz => Subfield.subset_closure (Set.mem_union_right _ hz)
    exact h1 ((IntermediateField.mem_toSubfield _ _).2 hx)
  refine Subfield.closure_induction (s := (K.toSubfield : Set ℝ) ∪ {√a})
    (p := fun y _ => Constructible y) ?_ constructible_one
    (fun _ _ _ _ hpx hpy => Constructible.ofAdd hpx hpy)
    (fun _ _ hpx => Constructible.ofNeg hpx) (fun _ _ hpx => Constructible.ofInv hpx)
    (fun _ _ _ _ hpx hpy => Constructible.ofMul hpx hpy) hxc
  rintro z (hzK | rfl)
  · exact hK z (IntermediateField.mem_toSubfield K z |>.1 hzK)
  · exact Constructible.ofSqrt hapos (hK a haK)

/-- **FT `ef26` (ii), (⇐).**  Every element of a well-formed quadratic tower is
constructible, by induction over the tower: the base case is ℚ (elementary by `ofRat`),
and the step case is `constructible_of_mem_sup` — this is the induction of the source's
proof ("if all elements of ℚ[√a₁,…,√a_{i-1}] are constructible, then √a_i is constructible
by ef25 b, and so are all elements of ℚ[√a₁,…,√a_i] by ef25 a"). -/
theorem constructible_of_towerOK (as : List ℝ) (hOK : TowerOK as) :
    ∀ x ∈ quadTower as, Constructible x := by
  induction hOK with
  | nil =>
    intro x hx
    rw [quadTower_nil] at hx
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
    subst hq
    exact constructible_of_ratCast q
  | @cons a as ha ham hOK ih =>
    intro x hx
    rw [quadTower_cons] at hx
    exact constructible_of_mem_sup ih ham ha hx

/-- **FT `ef26` (ii), (⇒).**  Every constructible number lies in some well-formed quadratic
tower over ℚ.  Proof idea: induction on the construction.  Rational inputs give the empty
tower; field operations combine the two input towers into their concatenation
(`quadTower_le_append_left/right`, `towerOK_append`); and adjoining `√x` on top of a tower
containing `x > 0` is exactly one more well-formed step. -/
theorem towerOK_of_constructible {x : ℝ} (h : Constructible x) :
    ∃ as : List ℝ, TowerOK as ∧ x ∈ quadTower as := by
  induction h with
  | ofRat q =>
    exact ⟨[], TowerOK.nil, by rw [quadTower_nil]; exact IntermediateField.mem_bot.2 ⟨q, rfl⟩⟩
  | @ofAdd x y hx hy ihx ihy =>
    obtain ⟨as, hOK, hxm⟩ := ihx
    obtain ⟨bs, hOK', hym⟩ := ihy
    refine ⟨as ++ bs, towerOK_append as bs hOK hOK', ?_⟩
    exact add_mem
      (SetLike.le_def.mp (quadTower_le_append_left as bs) hxm)
      (SetLike.le_def.mp (quadTower_le_append_right as bs) hym)
  | @ofNeg x hx ihx =>
    obtain ⟨as, hOK, hxm⟩ := ihx
    exact ⟨as, hOK, neg_mem hxm⟩
  | @ofMul x y hx hy ihx ihy =>
    obtain ⟨as, hOK, hxm⟩ := ihx
    obtain ⟨bs, hOK', hym⟩ := ihy
    refine ⟨as ++ bs, towerOK_append as bs hOK hOK', ?_⟩
    exact mul_mem
      (SetLike.le_def.mp (quadTower_le_append_left as bs) hxm)
      (SetLike.le_def.mp (quadTower_le_append_right as bs) hym)
  | @ofInv x hx ihx =>
    obtain ⟨as, hOK, hxm⟩ := ihx
    exact ⟨as, hOK, inv_mem hxm⟩
  | @ofSqrt x hpos hx ihx =>
    obtain ⟨as, hOK, hxm⟩ := ihx
    refine ⟨x :: as, TowerOK.cons hpos hxm hOK, ?_⟩
    rw [quadTower_cons]
    exact SetLike.le_def.mp (le_sup_right (a := quadTower as))
      (IntermediateField.mem_adjoin_simple_self ℚ √x)

/-- **FT `ef26` (ii).**  A number is constructible if and only if it is contained in a
subfield of ℝ of the form `ℚ[√a₁, …, √a_r]` with `a_i > 0` in the previous stage: the
towers of the formalisation are `quadTower as` for well-formed lists `as` (read in reverse
textbook order). -/
theorem constructible_iff_exists_tower (x : ℝ) :
    Constructible x ↔ ∃ as : List ℝ, TowerOK as ∧ x ∈ quadTower as :=
  ⟨fun h => towerOK_of_constructible h, fun ⟨as, hOK, hx⟩ => constructible_of_towerOK as hOK x hx⟩

/-!
Note (closing the semantic audit gap of commit 2a1940f): the reverse bridge
`FT.geo_of_constructible` (geometric closure of `Constructible`, section
`ConstructionsStraightEdgeCompass`) establishes `ef25` (a) and `ef26` (ii) (⇐)
for FT's *geometric* constructibility as well: every element of a quadratic
tower — in particular every constructible length — is the x-coordinate of a
straight-edge-and-compass constructed point, so the closure properties of
`FT.constructible_add` etc. transfer to the geometric notion via
`FT.geo_of_constructible`.
-/

/-- Auxiliary: `(√a)² - a = 0` in ℝ when `0 < a` lies in the intermediate field `K`
(the coefficient `a` is viewed as an element of `K`). -/
theorem aeval_sqrt_two_sub_C {K : IntermediateField ℚ ℝ} {a : ℝ} (haK : a ∈ K) (hapos : 0 < a) :
    (Polynomial.aeval √a) (Polynomial.X ^ 2 - Polynomial.C (⟨a, haK⟩ : K)) = 0 := by
  simp [Real.sq_sqrt hapos.le]

/-- `√a` is integral over `K` when `0 < a ∈ K`: it is a root of `X² - a`. -/
theorem isIntegral_sqrt_of_mem {K : IntermediateField ℚ ℝ} {a : ℝ} (haK : a ∈ K) (hapos : 0 < a) :
    IsIntegral K √a :=
  ⟨Polynomial.X ^ 2 - Polynomial.C (⟨a, haK⟩ : K), Polynomial.monic_X_pow_sub_C _ (by norm_num),
    aeval_sqrt_two_sub_C haK hapos⟩

/-- A single quadratic step `K⟮√a⟯` (with `0 < a ∈ K`) has relative degree at most `2`:
`[K⟮√a⟯ : K] = deg (minpoly K √a)` divides the degree of `X² - a`, which is `2`. -/
theorem finrank_adjoin_sqrt_le (K : IntermediateField ℚ ℝ) {a : ℝ} (haK : a ∈ K) (hapos : 0 < a) :
    Module.finrank ↥K ↥(IntermediateField.adjoin K {√a}) ≤ 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_sqrt_of_mem haK hapos)]
  have hdvd : minpoly K √a ∣ (Polynomial.X ^ 2 - Polynomial.C (⟨a, haK⟩ : K)) :=
    minpoly.dvd K √a (aeval_sqrt_two_sub_C haK hapos)
  refine le_trans (Polynomial.natDegree_le_of_dvd hdvd ?_) ?_
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) _
  · rw [Polynomial.natDegree_X_pow_sub_C]

/-- Each well-formed step multiplies the ℚ-degree by a factor `d ∈ {1, 2}`: the tower law
`[K₁ : ℚ] = [K₁ : K₀] [K₀ : ℚ]` with `[K₁ : K₀] = deg (minpoly K₀ √a) ∈ {1, 2}`. -/
theorem quadTower_finrank_cons (a : ℝ) (as : List ℝ) (haK : a ∈ quadTower as) (hapos : 0 < a) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ∧
      Module.finrank ℚ ↥(quadTower (a :: as)) = Module.finrank ℚ ↥(quadTower as) * d := by
  have hM : Module.finrank ℚ ↥(quadTower (a :: as))
      = Module.finrank ℚ ↥(IntermediateField.adjoin (quadTower as) {√a}) := rfl
  refine ⟨Module.finrank ↥(quadTower as) ↥(IntermediateField.adjoin (quadTower as) {√a}),
    ?_, finrank_adjoin_sqrt_le _ haK hapos, ?_⟩
  · rw [IntermediateField.adjoin.finrank (isIntegral_sqrt_of_mem haK hapos)]
    exact minpoly.natDegree_pos (isIntegral_sqrt_of_mem haK hapos)
  · rw [hM, Module.finrank_mul_finrank ℚ ↥(quadTower as)
      ↥(IntermediateField.adjoin (quadTower as) {√a})]

/-- The ℚ-degree of a well-formed quadratic tower is exactly a power of `2` (a product of
factors `1` and `2`, one per step).  Proof idea: induction on the tower with
`quadTower_finrank_cons`. -/
theorem quadTower_finrank_pow (as : List ℝ) (hOK : TowerOK as) :
    ∃ j, Module.finrank ℚ ↥(quadTower as) = 2 ^ j := by
  induction hOK with
  | nil => exact ⟨0, by rw [quadTower_nil, pow_zero]; exact IntermediateField.finrank_bot⟩
  | @cons a as ha ham hOK ih =>
    obtain ⟨d, hd1, hd2, hd⟩ := quadTower_finrank_cons a as ham ha
    obtain ⟨j, hj⟩ := ih
    rcases Nat.lt_or_ge d 2 with h | h
    · refine ⟨j, ?_⟩
      have h1 : d = 1 := by omega
      rw [hd, hj, h1, mul_one]
    · refine ⟨j + 1, ?_⟩
      have h2 : d = 2 := by omega
      rw [hd, hj, h2, Nat.pow_succ]

/-- A divisor of a power of `2` is a power of `2`.  Proof idea: any prime divisor of `d`
divides `2 ^ r`, hence is `2`; so only the prime `2` occurs in `d`. -/
theorem nat_dvd_two_pow {d r : ℕ} (h : d ∣ 2 ^ r) : ∃ k, d = 2 ^ k := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd d with hk | ⟨p, hp, hpd, hodd⟩
  · exact hk
  · exfalso
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (hpd.trans h)
    have h' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    rw [h'] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega

/-- **FT `ef27`.**  If `α` is constructible then `α` is algebraic over ℚ and
`[ℚ[α] : ℚ]` is a power of `2`.  Here `[ℚ[α] : ℚ]` is read as
`Module.finrank ℚ ↥(ℚ⟮α⟯)`, the degree of the (simple) ℚ-field generated by `α` inside ℝ;
this agrees with the degree of the ring `ℚ[α]` because a constructible `α` is algebraic.
Proof (following the source): `α` lies in a well-formed tower `K` with `[K : ℚ] = 2^j`;
`ℚ⟮α⟯ ≤ K`, so `[ℚ⟮α⟯ : ℚ]` divides `2^j` (tower law, i.e. FT `ef10`), and a divisor of a
power of `2` is a power of `2`; `α` is algebraic because `K` is finite-dimensional over ℚ. -/
theorem constructible_algebraic_and_degree {α : ℝ} (h : Constructible α) :
    IsAlgebraic ℚ α ∧ ∃ j, Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {α}) = 2 ^ j := by
  obtain ⟨as, hOK, hα⟩ := towerOK_of_constructible h
  obtain ⟨j, hj⟩ := quadTower_finrank_pow as hOK
  have hsub : IntermediateField.adjoin ℚ {α} ≤ quadTower as :=
    IntermediateField.adjoin_le_iff.mpr (by simpa using hα)
  have hdvd : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {α}) ∣
      Module.finrank ℚ ↥(quadTower as) := IntermediateField.finrank_dvd_of_le_right hsub
  refine ⟨?_, ?_⟩
  · have hf : 0 < Module.finrank ℚ ↥(quadTower as) := by
      rw [hj]
      positivity
    haveI hfin : Module.Finite ℚ ↥(quadTower as) := Module.finite_of_finrank_pos hf
    have hint : IsIntegral ℚ (⟨α, hα⟩ : ↥(quadTower as)) := IsIntegral.of_finite ℚ _
    have halpha : IsIntegral ℚ α :=
      IsIntegral.map (IsScalarTower.toAlgHom ℚ ↥(quadTower as) ℝ) hint
    exact IsIntegral.isAlgebraic halpha
  · rw [hj] at hdvd
    exact nat_dvd_two_pow hdvd

/-! #### FT `ef28`, `ef29`, `ef30`: the three classical straight-edge-and-compass impossibilities.

Consumes the constructibility interface of FT `ef25`–`ef27` (`Constructible`,
`constructible_algebraic_and_degree`, `constructible_mul`); the interface is only touched at
the final corollaries, everything below is proved against explicit hypothesis parameters. -/

/-- `3` is not a power of two: `3 ≠ 2 ^ k` for all `k : ℕ`.

Proof idea: for `k = 0` the right-hand side is `1`; for `k + 1` it equals `2 ^ k * 2`, an
even number, while `3` is odd. -/
theorem three_ne_two_pow (k : ℕ) : (3 : ℕ) ≠ 2 ^ k := by
  cases k with
  | zero => simp
  | succ k => rw [Nat.pow_succ]; omega

/-- Over a field, a nonzero polynomial of degree `3` which is not
irreducible has a root.  This is the contrapositive of the degree-`3` special case of
"irreducible ⟺ no root" used implicitly in the source proofs.

Proof idea: a non-unit `f` factors nontrivially (`irreducible_or_factor`); since
`natDegree f = natDegree p + natDegree q = 3` with both factors nonconstant (a nonunit
nonzero factor has `natDegree ≥ 1`), one factor has degree `1`; a degree-one polynomial
over a field has a root (`Polynomial.exists_root_of_degree_eq_one`), which is then a root
of `f`. -/
theorem exists_root_of_not_irreducible_cubic {F : Type*} [Field F] {f : F[X]}
    (hf : f ≠ 0) (hnd : f.natDegree = 3) (hirr : ¬ Irreducible f) : ∃ x, f.IsRoot x := by
  have hfu : ¬ IsUnit f := by
    intro hu
    have h0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  rcases irreducible_or_factor hfu with h | ⟨p, q, hpu, hqu, hpq⟩
  · exact absurd h hirr
  have hp0 : p ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hpq; exact hf hpq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpq; exact hf hpq
  have hpos : ∀ g : F[X], ¬IsUnit g → g ∣ f → 0 < g.natDegree := by
    intro g hgu hgf
    have h0 : g.natDegree ≠ 0 := by
      intro h0
      have hgc : g = C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hcne : g.coeff 0 ≠ 0 := by
        intro hc
        rw [hgc, hc, C_0] at hgf
        exact hf (zero_dvd_iff.mp hgf)
      have hu' : IsUnit g := by
        rw [hgc]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne)
      exact hgu hu'
    exact Nat.pos_of_ne_zero h0
  have hd : f.natDegree = p.natDegree + q.natDegree := by
    rw [hpq, Polynomial.natDegree_mul hp0 hq0]
  have hpd : 0 < p.natDegree := hpos p hpu ⟨q, hpq⟩
  have hqd : 0 < q.natDegree := hpos q hqu ⟨p, by rw [mul_comm]; exact hpq⟩
  have hone : p.natDegree = 1 ∨ q.natDegree = 1 := by omega
  rcases hone with h1 | h1
  · obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one
      (show p.degree = 1 by rw [Polynomial.degree_eq_natDegree hp0, h1]; simp)
    have hx' : Polynomial.eval x p = 0 := hx
    refine ⟨x, ?_⟩
    show Polynomial.eval x f = 0
    rw [hpq, Polynomial.eval_mul, hx', zero_mul]
  · obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one
      (show q.degree = 1 by rw [Polynomial.degree_eq_natDegree hq0, h1]; simp)
    have hx' : Polynomial.eval x q = 0 := hx
    refine ⟨x, ?_⟩
    show Polynomial.eval x f = 0
    rw [hpq, Polynomial.eval_mul, hx', mul_zero]

/-- If the real number `α` is a root of an irreducible cubic
`f : ℚ[X]`, then `[ℚ⟮α⟯ : ℚ] = 3` (finrank form).

Proof idea: `α` is integral, so `Module.finrank ℚ ℚ⟮α⟯ = (minpoly ℚ α).natDegree`
(`IntermediateField.adjoin.finrank`); the minimal polynomial is `f` up to the unit
`C (leadingCoeff f)⁻¹` (`minpoly.eq_of_irreducible`), hence has the same degree `3`
(`Polynomial.natDegree_mul_C`). -/
theorem finrank_adjoin_eq_three_of_irreducible_cubic {α : ℝ} {f : ℚ[X]}
    (hnd : f.natDegree = 3) (hirr : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 3 := by
  have hint : IsIntegral ℚ α := isAlgebraic_iff_isIntegral.mp ⟨f, hirr.ne_zero, hroot⟩
  have hmin : f * C f.leadingCoeff⁻¹ = minpoly ℚ α := minpoly.eq_of_irreducible hirr hroot
  rw [IntermediateField.adjoin.finrank hint, ← hmin,
    Polynomial.natDegree_mul_C (a := f.leadingCoeff⁻¹)
      (show (f.leadingCoeff⁻¹ : ℚ) ≠ 0 by
        simpa using Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero),
    hnd]

/-- A constructible number (for a constructibility predicate whose degrees are powers of
two) whose minimal
polynomial has degree `3` cannot exist, because `3` is not a power of two (FT `ef27`). -/
theorem not_constructible_of_irreducible_cubic
    {Constructible' : ℝ → Prop}
    (hpow : ∀ α : ℝ, Constructible' α →
      ∃ k : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2 ^ k)
    {α : ℝ} {f : ℚ[X]} (hnd : f.natDegree = 3) (hirr : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) (h : Constructible' α) : False := by
  obtain ⟨k, hk⟩ := hpow α h
  rw [finrank_adjoin_eq_three_of_irreducible_cubic hnd hirr hroot] at hk
  exact three_ne_two_pow k hk

/-- The defining root relation for the real cube root of `2`, represented
as `(2 : ℝ) ^ (1 / 3)` (this Mathlib checkout has no `Real.cbrt`): `aeval (∛2) (X³ - 2) = 0`.

Proof idea: `(2 ^ (1/3))³ = 2 ^ ((1/3) · 3) = 2` by `Real.rpow_inv_natCast_pow`; the
`aeval` computation is simp. -/
theorem aeval_two_rpow_third :
    Polynomial.aeval ((2 : ℝ) ^ (1 / 3 : ℝ)) (Polynomial.X ^ 3 - Polynomial.C 2 : ℚ[X]) = 0 := by
  have hkey : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [show ((1 : ℝ) / 3) = (3 : ℝ)⁻¹ from by norm_num]
    exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  simp only [Polynomial.aeval_C, Polynomial.aeval_X_pow, map_sub]
  rw [hkey]
  norm_num

/-- `X³ - 2` is irreducible over `ℚ`, by Eisenstein's criterion at the
prime `2` (FT `ef7`), exactly as in the source proof: `2 ∣ -2`, `4 ∤ -2`, `2 ∣ 0, 0` and
`2 ∤ 1`.  This is a source-proof wrapper around `FT.eisenstein_irreducible` (the target's
formalization of FT `ef7`), with coefficient bookkeeping. -/
theorem irreducible_X_pow_three_sub_two :
    Irreducible (Polynomial.X ^ 3 - Polynomial.C 2 : ℚ[X]) := by
  have hnd : (Polynomial.X ^ 3 - Polynomial.C 2 : ℤ[X]).natDegree = 3 :=
    Polynomial.natDegree_X_pow_sub_C
  have hc0 : (Polynomial.X ^ 3 - Polynomial.C 2 : ℤ[X]).coeff 0 = -2 := by simp
  have hlead : ¬ ((2 : ℤ) ∣ (Polynomial.X ^ 3 - Polynomial.C 2 : ℤ[X]).coeff
      (Polynomial.X ^ 3 - Polynomial.C 2 : ℤ[X]).natDegree) := by
    rw [hnd]
    have hc3 : (Polynomial.X ^ 3 - Polynomial.C 2 : ℤ[X]).coeff 3 = 1 := by simp
    rw [hc3]
    rintro ⟨k, hk⟩
    omega
  have h := FT.eisenstein_irreducible (Polynomial.X ^ 3 - Polynomial.C 2) 2 Nat.prime_two
    (by rw [hc0]; exact ⟨-1, by norm_num⟩)
    (by rw [hc0]; rintro ⟨k, hk⟩; omega)
    (by intro i hi; rw [hnd] at hi; interval_cases i
        · rw [hc0]; exact ⟨-1, by norm_num⟩
        · simp
        · simp)
    hlead
  have heq : Polynomial.map (algebraMap ℤ ℚ)
      (Polynomial.X ^ 3 - Polynomial.C 2 : ℤ[X])
      = (Polynomial.X ^ 3 - Polynomial.C 2 : ℚ[X]) := by
    ext i
    rcases i with _ | i
    · simp
    · simp
  rw [heq] at h
  exact h

/-- **FT `ef28`.**  It is impossible to duplicate the cube by straight-edge and compass
constructions.**

Formalization: the cube of volume `2` has side the real cube root of `2` (represented as
`(2 : ℝ) ^ (1 / 3)`, the real root of `X³ - 2`), and that number is not constructible.

Proof idea (the source's): `X³ - 2` is irreducible over `ℚ` (Eisenstein at `2`, FT `ef7`),
so `ℚ⟮∛2⟯` has degree `3` over `ℚ`, which is not a power of `2`; this contradicts FT `ef27`.
Nature: source proof (the `X³ - 2` computation is delegated to `FT.eisenstein_irreducible`
and Mathlib's `minpoly`/power-basis API). -/
theorem not_constructible_cuberoot_two : ¬ Constructible ((2 : ℝ) ^ (1 / 3 : ℝ)) :=
  fun h => not_constructible_of_irreducible_cubic
    (fun _ h => (constructible_algebraic_and_degree h).2)
    (Polynomial.natDegree_X_pow_sub_C) irreducible_X_pow_three_sub_two aeval_two_rpow_third h

/-- Evaluating the trisection cubic `8X³ - 6X - 1 : ℚ[X]` at a rational `c` gives
`8c³ - 6c - 1` (pure simp bookkeeping, used in the rational-root check). -/
theorem eval_trisection_cubic (c : ℚ) :
    Polynomial.eval c
      (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
        - Polynomial.C 1 : ℚ[X]) = 8 * c ^ 3 - 6 * c - 1 := by
  simp

/-- The trisection cubic `8X³ - 6X - 1 ∈ ℚ[X]` of the source proof of the trisection impossibility is
irreducible.  Proof (the source's, via FT `ef4`): if it were reducible, being nonzero of
degree `3` it would have a root
(`FT.exists_root_of_not_irreducible_cubic`); by the rational root test (FT `ef4`, i.e.
`FT.num_dvd_coeff_zero_and_den_dvd_coeff_natDegree'`) a rational root `r` in lowest terms
has numerator dividing the constant coefficient `-1` and denominator dividing the leading
coefficient `8`, so `r ∈ {±1, ±1/2, ±1/4, ±1/8}`; none of these eight candidates is a root. -/
theorem irreducible_trisection_cubic :
    Irreducible (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℚ[X]) := by
  by_contra hnot
  have hnd : (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  have hne : (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℚ[X]) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hnd; omega
  obtain ⟨r, hr⟩ := exists_root_of_not_irreducible_cubic hne hnd hnot
  have hmap : Polynomial.map (algebraMap ℤ ℚ)
      (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
        - Polynomial.C 1 : ℤ[X])
      = (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
        - Polynomial.C 1 : ℚ[X]) := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_C]
    simp
  have ha : Polynomial.aeval r (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℤ[X]) = 0 := by
    rw [FT.aeval_eq_eval_map_algebraMap, hmap]
    exact hr
  obtain ⟨hnum, hden⟩ := FT.num_dvd_coeff_zero_and_den_dvd_coeff_natDegree ha
  have hnd0 : (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℤ[X]).natDegree = 3 := by compute_degree!
  rw [hnd0] at hden
  have hc0 : (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℤ[X]).coeff 0 = -1 := by simp
  have hc3 : (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
      - Polynomial.C 1 : ℤ[X]).coeff 3 = 8 := by
    simp [Polynomial.coeff_X, Polynomial.coeff_one]
  rw [hc0] at hnum
  rw [hc3] at hden
  have hnum1 : (r.num : ℤ) = 1 ∨ (r.num : ℤ) = -1 := by
    have h1 : (r.num : ℤ) ∣ (1 : ℤ) := Int.dvd_neg.mp hnum
    have habs : (r.num : ℤ).natAbs = 1 :=
      Nat.dvd_one.mp (Int.dvd_natCast.mp h1)
    rcases Int.natAbs_eq (r.num : ℤ) with he | he
    · left; omega
    · right; omega
  have hden8 : r.den ∣ (8 : ℕ) := Int.natCast_dvd_natCast.mp hden
  have hpos : 0 < r.den := Rat.pos r
  have hle : r.den ≤ 8 := Nat.le_of_dvd (by norm_num) hden8
  rw [show r = (r.num : ℚ) / r.den from (Rat.num_div_den r).symm,
    FT.aeval_eq_eval_map_algebraMap, hmap, eval_trisection_cubic] at ha
  interval_cases r.den
  all_goals
    rcases hnum1 with hn | hn <;> rw [hn] at ha <;> norm_num at ha

/-- `cos 20° = cos (π/9)` is a root of `8X³ - 6X - 1`, i.e. it solves the
trisection equation of the source proof for `3α = 60°` (`cos 3α = 4cos³α - 3cos α`, with
`cos 60° = 1/2`).

Proof idea: the triple-angle formula `Real.cos_three_mul` at `x = π/9` together with
`Real.cos_pi_div_three : cos (π/3) = 1/2` gives `4c³ - 3c = 1/2`, i.e. `8c³ - 6c - 1 = 0`;
the `aeval` computation itself is simp. -/
theorem aeval_cos_pi_div_nine :
    Polynomial.aeval (Real.cos (Real.pi / 9))
      (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
        - Polynomial.C 1 : ℚ[X]) = 0 := by
  have h3 : Real.cos (Real.pi / 3)
      = 4 * Real.cos (Real.pi / 9) ^ 3 - 3 * Real.cos (Real.pi / 9) := by
    rw [← Real.cos_three_mul]
    congr 1
    ring
  rw [show (Polynomial.aeval (Real.cos (Real.pi / 9))
      (Polynomial.C 8 * Polynomial.X ^ 3 - Polynomial.C 6 * Polynomial.X
        - Polynomial.C 1 : ℚ[X]))
      = 8 * Real.cos (Real.pi / 9) ^ 3 - 6 * Real.cos (Real.pi / 9) - 1 from by
      simp [Polynomial.aeval_C, Polynomial.aeval_X_pow]]
  linarith [h3, Real.cos_pi_div_three]

/-- **FT `ef29`.**  In general, it is impossible to trisect an angle by straight-edge and
compass constructions.**

Formalization: the source proof exhibits the concrete counterexample angle `3α = 60°`
("knowing an angle is equivalent to knowing the cosine of the angle", so constructing the
trisection of `60° = π/3` amounts to constructing `cos(20°) = cos(π/9)`), and shows that
`cos(π/9)` is a root of the irreducible cubic `8X³ - 6X - 1` (trisection equation
`cos 3α = 4cos³α - 3cos α` with `cos 60° = 1/2`), whence `ℚ⟮cos(π/9)⟯` has degree `3`
over `ℚ`, contradicting FT `ef27`.  Note `cos(π/3) = 1/2` *is* constructible, so this is
a genuine counterexample: a constructible angle that cannot be trisected.

The irreducibility is exactly the source's appeal to FT `ef4` (rational root test). -/
theorem not_constructible_cos_pi_div_nine : ¬ Constructible (Real.cos (Real.pi / 9)) :=
  fun h => not_constructible_of_irreducible_cubic
    (fun _ h => (constructible_algebraic_and_degree h).2)
    (by compute_degree!) irreducible_trisection_cubic aeval_cos_pi_div_nine h

/-- External dependency (audible axiom): **the transcendence of `π`** (Lindemann--Weierstrass).
This is deliberately an audible axiom: the transcendence of `π` is an external dependency
cited without proof in the source (footnote referring to Hardy & Wright, *An Introduction
to the Theory of Numbers*, 4th ed., 11.14), and is absent from Mathlib (Mathlib only knows
`Irrational Real.pi`, which is strictly weaker).  No result proved in the source is
admitted this way. -/
axiom transcendental_pi : Transcendental ℚ Real.pi

/-- Bridge: `π` is not constructible.  Proof idea (the source's): a constructible
number is algebraic over `ℚ` (FT `ef27`), but `π` is transcendental. -/
theorem pi_not_constructible : ¬ Constructible Real.pi :=
  fun h => transcendental_pi (constructible_algebraic_and_degree h).1
/-- FT `ef28` as a genuine geometric impossibility: ∛2 is not straight-edge-and-compass
constructible (transfer of `not_constructible_cuberoot_two` along the bridge). -/
theorem not_geoConstructible_cuberoot_two : ¬ GeoConstructible ((2 : ℝ) ^ (1 / 3 : ℝ)) := fun h =>
  not_constructible_cuberoot_two (constructible_of_geo h)

/-- FT `ef29` as a genuine geometric impossibility: `cos 20°` is not straight-edge-and-compass
constructible (transfer of `not_constructible_cos_pi_div_nine` along the bridge). -/
theorem not_geoConstructible_cos_pi_div_nine :
    ¬ GeoConstructible (Real.cos (Real.pi / 9)) := fun h =>
  not_constructible_cos_pi_div_nine (constructible_of_geo h)

/-- FT `ef30` as a genuine geometric impossibility: `π` is not straight-edge-and-compass
constructible (transfer of `pi_not_constructible` along the bridge; inherits the same external
axiom `transcendental_pi` as `pi_not_constructible`). -/
theorem not_geoConstructible_pi : ¬ GeoConstructible Real.pi := fun h =>
  pi_not_constructible (constructible_of_geo h)


/-- **FT `ef30`.**  It is impossible to square the circle by straight-edge and compass
constructions.**

Formalization: a square with the same area as a circle of radius `r` has side `√π · r`, so
it suffices to show that `√π` is not constructible (the source: "Since π is transcendental,
so also is √π").  Proof idea: if `√π` were constructible, then `π = √π · √π` would be
constructible (FT `ef25` (a)), hence algebraic over `ℚ` (FT `ef27`), contradicting the
transcendence of `π` (external dependency `FT.transcendental_pi`). -/
theorem not_constructible_sqrt_pi : ¬ Constructible (Real.sqrt Real.pi) :=
  fun h => pi_not_constructible (by
    have hπ : Constructible (Real.sqrt Real.pi * Real.sqrt Real.pi) :=
      constructible_mul h h
    rwa [Real.mul_self_sqrt Real.pi_pos.le] at hπ)

/-- Auxiliary plumbing.  Substituting `X - C t` into the substituted polynomial
`(p.comp (X + C t))` recovers `p`: this is the trivial inverse property of the change of
variables `X ↦ X + t`, and is the only fact needed to transfer units and irreducibility of
`R[X]` across the substitution `f(X) ↦ f(X + 1)` used in the proof of FT `ef31`.  Proof is a
standard `Polynomial.comp_assoc` computation; mathematically trivial. -/
private theorem comp_X_add_C_comp_X_sub_C {R : Type*} [CommRing R] (t : R) (p : R[X]) :
    (p.comp (X + C t)).comp (X - C t) = p := by
  have h : (X + C t).comp (X - C t) = X := by simp
  rw [Polynomial.comp_assoc, h, Polynomial.comp_X]

/-- Auxiliary plumbing.  A polynomial `p ∈ R[X]` is a unit iff its substitution
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

/-- Auxiliary plumbing.  Mirror of `comp_X_add_C_comp_X_sub_C` for the
substitution `X ↦ X - t`: `(p(X - t))(X + t) = p(X)`.  Proof is the same trivial
`Polynomial.comp_assoc` computation. -/
private theorem comp_X_sub_C_comp_X_add_C {R : Type*} [CommRing R] (t : R) (p : R[X]) :
    (p.comp (X - C t)).comp (X + C t) = p := by
  have h : (X - C t).comp (X + C t) = X := by simp
  rw [Polynomial.comp_assoc, h, Polynomial.comp_X]

/-- Auxiliary plumbing.  A polynomial `p ∈ R[X]` is a unit iff its substitution
image `p(X - t)` is a unit.  Proof identical to `isUnit_comp_X_add_C_iff`. -/
private theorem isUnit_comp_X_sub_C_iff {R : Type*} [CommRing R] (t : R) {p : R[X]} :
    IsUnit (p.comp (X - C t)) ↔ IsUnit p :=
  ⟨fun hu => by
      rw [← comp_X_sub_C_comp_X_add_C t p]
      exact (Polynomial.compRingHom (X + C t)).isUnit_map hu,
   fun hu => (Polynomial.compRingHom (X - C t)).isUnit_map hu⟩

/-- Auxiliary plumbing.  The substitution `f(X) ↦ f(X + t)` is a multiplicative
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

/-- Auxiliary lemma (the Eisenstein step).  With `f(X) = X ^ (p - 1) + ⋯ + 1 =
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

/-- Auxiliary lemma.  For a prime `p`, the polynomial `X ^ (p - 1) + ⋯ + 1` is
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

/-!
### Improvements for Mathlib

(No substantive upstream obligations were identified.  An earlier entry
proposing a cubic no-root irreducibility criterion was withdrawn after the
audit of commit 73801da: Mathlib's
`Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three` and
`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`
(Mathlib/Algebra/Polynomial/SpecificDegree.lean) already package the
degree-≤3 root criterion, so the project's
`FT.exists_root_of_not_irreducible_cubic` is a thin composition rather than
an upstream gap.  The project declaration is retained for source-faithfulness
to the proof of FT `ef29`.)
-/

/-!
### Chapter 2: Splitting fields; multiple roots (FT `sf1`–`sf9`, `ft1`–`ft6`)

Encoding conventions for this chapter:
* FT's `F`-homomorphisms `E → L` (field homomorphisms fixing `F` pointwise) are encoded
  as `AlgHom F E L`, for fields `E`, `L` over `F` via `Algebra F E`, `Algebra F L`.
  FT's `F`-isomorphisms are `AlgEquiv F E L`. Every `F`-homomorphism is injective
  (a field homomorphism is).
* For a homomorphism `φ₀ : F →+* Ω` and `f ∈ F[X]`, FT's polynomial `φ₀f` (apply `φ₀`
  to the coefficients) is `f.map φ₀`.
* FT's "E splits f" is `Polynomial.Splits (f.map (algebraMap F E))`; FT's "E is a
  splitting field for f" (splits and generated by the roots) is Mathlib's
  `Polynomial.IsSplittingField f` (typeclass on `E`), whose fields are
  `Splits (f.map (algebraMap F E))` and `Algebra.adjoin F (f.rootSet E) = ⊤`.
* FT `ft4` (Bourbaki's separable polynomial) is Mathlib's `Polynomial.Separable`
  (`IsCoprime f (derivative f)`); the equivalence with "f has only simple roots"
  is FT `ft3a` below. FT `ft4m` (perfect field) is `FT.PerfectFT` below; the
  equivalence with Mathlib's `PerfectField` (every irreducible separable) is FT `ft5`.
-/

/-- FT `ft4m` (definition). A field is *perfect* if it has characteristic zero, or it has
characteristic `p ≠ 0` and every element of `F` is a `p`th power. -/
def PerfectFT (K : Type*) [Field K] : Prop :=
  CharZero K ∨ (ringChar K ≠ 0 ∧ ∀ a : K, ∃ b : K, a = b ^ ringChar K)
section FT1

open scoped Polynomial in
open scoped Classical in
/-- FT `ft1` (gcd statement). The gcd of two polynomials over `F`, transported to an
extension `Ω` of `F` via the algebra map `F → Ω`, is the gcd of the transported
polynomials in `Ω[X]`: in particular the image of `EuclideanDomain.gcd f g` is
associated to (here: equal to) `EuclideanDomain.gcd (f.map _) (g.map _)`.
This is Milne FT `ft1`: the Euclidean algorithm only manipulates coefficients
lying in `F`, so extending the field cannot change the gcd up to associates. -/
theorem gcd_map_algebraMap {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (f g : F[X]) :
    EuclideanDomain.gcd (f.map (algebraMap F Ω)) (g.map (algebraMap F Ω))
        = (EuclideanDomain.gcd f g).map (algebraMap F Ω) :=
  Polynomial.gcd_map (algebraMap F Ω)

open scoped Polynomial in
/-- FT `ft1` (coprimality form). Coprimality in `F[X]` is preserved by extension of
scalars along `F → Ω`: if `f`, `g ∈ F[X]` satisfy a Bézout relation `af + bg = 1`
over `F`, then the transported polynomials satisfy the same relation over `Ω`.
Immediate from the gcd statement `gcd_map_algebraMap`. -/
theorem isCoprime_map_algebraMap {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {f g : F[X]} :
    IsCoprime (f.map (algebraMap F Ω)) (g.map (algebraMap F Ω)) ↔ IsCoprime f g :=
  Polynomial.isCoprime_map (algebraMap F Ω)

open scoped Polynomial in
/-- FT `ft1` (corollary). If `p`, `q ∈ F[X]` are irreducible and not associated, they
do not acquire a common root in any extension `Ω` of `F`: a common root `ζ` would
force `X - C ζ` to divide both transported polynomials, contradicting coprimality
(since `IsCoprime p q` transports to `Ω[X]` by `isCoprime_map_algebraMap`, and then
`X - C ζ` would be a unit, impossible for a polynomial of degree `1` over a field). -/
theorem no_common_root_of_irreducible_not_associated
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {p q : F[X]}
    (hp : Irreducible p) (hq : Irreducible q) (h : ¬Associated p q) (ζ : Ω) :
    ¬((p.map (algebraMap F Ω)).IsRoot ζ ∧ (q.map (algebraMap F Ω)).IsRoot ζ) := by
  have hcop : IsCoprime p q := by
    rcases dvd_or_isCoprime p q hp with hdvd | hc
    · obtain ⟨c, hc⟩ := hdvd
      rcases hq.isUnit_or_isUnit hc with hu | hu
      · exact absurd hu hp.not_isUnit
      · exact absurd ⟨hu.unit, hc.symm⟩ h
    · exact hc
  intro ⟨h1, h2⟩
  have hd1 : Polynomial.X - Polynomial.C ζ ∣ p.map (algebraMap F Ω) :=
    Polynomial.dvd_iff_isRoot.2 h1
  have hd2 : Polynomial.X - Polynomial.C ζ ∣ q.map (algebraMap F Ω) :=
    Polynomial.dvd_iff_isRoot.2 h2
  have hu : IsUnit (Polynomial.X - Polynomial.C ζ) :=
    (((isCoprime_map_algebraMap).2 hcop).mono hd1 hd2).isUnit_of_dvd dvd_rfl
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_X_sub_C] at hu
  norm_num at hu

open scoped Polynomial in
/-- FT `ft1` (corollary, distinct monic form). Distinct monic irreducible polynomials
over `F` do not acquire a common root in any extension `Ω` of `F`. This is the
form stated in Milne FT: two distinct monic irreducibles are not associated
(`Polynomial.eq_of_monic_of_associated`), and the general case follows from
`no_common_root_of_irreducible_not_associated`. -/
theorem no_common_root_of_irreducible_monic_ne
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {p q : F[X]}
    (hp : Irreducible p) (hq : Irreducible q) (hpM : p.Monic) (hqM : q.Monic)
    (hne : p ≠ q) (ζ : Ω) :
    ¬((p.map (algebraMap F Ω)).IsRoot ζ ∧ (q.map (algebraMap F Ω)).IsRoot ζ) :=
  no_common_root_of_irreducible_not_associated hp hq
    (fun ha => hne (Polynomial.eq_of_monic_of_associated hpM hqM ha)) ζ

end FT1
section SF4

open Polynomial Module
variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The structure map of a field extension of a field is injective (helper for FT `sf4`). -/
private lemma algebraMap_injective_of_field : Function.Injective (algebraMap K E) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_cases h0 : a = 0
  · exact h0
  · exfalso
    have h1 : (1 : E) = algebraMap K E a * algebraMap K E a⁻¹ := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    rw [ha, zero_mul] at h1
    exact one_ne_zero h1

private lemma sf4_aeval_adjoin {F : IntermediateField K E} {α : E} {f : K[X]}
    (hαm : α ∈ F) (h0 : aeval α f = 0) :
    aeval (⟨α, hαm⟩ : ↥F) f = 0 := by
  have h1 := hom_eval₂ f (algebraMap K ↥F) (algebraMap ↥F E) (⟨α, hαm⟩ : ↥F)
  rw [← IsScalarTower.algebraMap_eq K ↥F E] at h1
  simp only [← aeval_def] at h1
  rw [show (algebraMap ↥F E) (⟨α, hαm⟩ : ↥F) = α from rfl, h0] at h1
  exact algebraMap_injective_of_field (h1.trans (map_zero _).symm)

private lemma sf4_aux : ∀ (n : ℕ) {K : Type u} [Field K] {E : Type u} [Field E] [Algebra K E]
    (f : K[X]), f.natDegree = n → f ≠ 0 → [IsSplittingField K E f] →
    Module.finrank K E ≤ Nat.factorial f.natDegree := by
  intro n
  induction n with
  | zero =>
    intro K _ E _ _ f hn hf0 hsp
    have hdeg : f.degree = 0 := by
      rw [degree_eq_natDegree hf0, hn, Nat.cast_zero]
    obtain ⟨a, rfl⟩ : ∃ a : K, f = C a := ⟨f.coeff 0, eq_C_of_degree_eq_zero hdeg⟩
    have htop : (⊤ : Subalgebra K E) = ⊥ := by
      rw [← hsp.adjoin_rootSet']
      ext β
      simp
    have h1 : Module.finrank K E = 1 := by
      rw [← Subalgebra.topEquiv.toLinearEquiv.finrank_eq, htop,
        (Algebra.botEquiv K E).toLinearEquiv.finrank_eq, Module.finrank_self]
    rw [h1, natDegree_C, Nat.factorial_zero]
  | succ n ih =>
    intro K _ E _ _ f hn hf0 hsp
    have hspl : Splits (f.map (algebraMap K E)) := hsp.splits'
    have hinjK : Function.Injective (algebraMap K E) := algebraMap_injective_of_field
    obtain ⟨α, hαE⟩ := hspl.exists_eval_eq_zero
      (by rw [degree_map_eq_of_injective hinjK f, degree_eq_natDegree hf0, hn]
          exact_mod_cast Nat.succ_ne_zero n)
    have hα0 : aeval α f = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact hαE
    have hαi : IsIntegral K α := isAlgebraic_iff_isIntegral.mp ⟨f, hf0, hα0⟩
    have hαm : α ∈ IntermediateField.adjoin K {α} := IntermediateField.mem_adjoin_simple_self K α
    have hinjF : Function.Injective (algebraMap ↥(IntermediateField.adjoin K {α}) E) :=
      algebraMap_injective_of_field
    have hinjKF : Function.Injective (algebraMap K ↥(IntermediateField.adjoin K {α})) :=
      algebraMap_injective_of_field
    have hp0 : f.map (algebraMap K ↥(IntermediateField.adjoin K {α})) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinjKF).mpr hf0
    have haeval : aeval (⟨α, hαm⟩ : ↥(IntermediateField.adjoin K {α})) f = 0 :=
      sf4_aeval_adjoin hαm hα0
    set a : ↥(IntermediateField.adjoin K {α}) := ⟨α, hαm⟩ with ha_def
    have hcoe : (algebraMap ↥(IntermediateField.adjoin K {α}) E) a = α := by
      rw [ha_def, IntermediateField.algebraMap_apply, Subtype.coe_mk]
    have hrootp : IsRoot (f.map (algebraMap K ↥(IntermediateField.adjoin K {α}))) a := by
      rw [IsRoot.def, ← eval₂_eq_eval_map, ← aeval_def]
      exact haeval
    have hmul : (X - C a) * (f.map (algebraMap K ↥(IntermediateField.adjoin K {α})) /ₘ (X - C a))
        = f.map (algebraMap K ↥(IntermediateField.adjoin K {α})) :=
      (mul_divByMonic_eq_iff_isRoot).mpr hrootp
    set h : (↥(IntermediateField.adjoin K {α}))[X] :=
      f.map (algebraMap K ↥(IntermediateField.adjoin K {α})) /ₘ (X - C a) with hh_def
    have h0 : h ≠ 0 := fun hc => hp0 (by rw [← hmul, hc, mul_zero])
    have hnat : h.natDegree = n := by
      rw [hh_def, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_map_eq_of_injective hinjKF f,
        hn, natDegree_X_sub_C, Nat.succ_sub_one]
    have hmapne0 : h.map (algebraMap ↥(IntermediateField.adjoin K {α}) E) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinjF).mpr h0
    have hchain : f.map (algebraMap K E)
        = ((X - C a) * h).map (algebraMap ↥(IntermediateField.adjoin K {α}) E) := by
      rw [hmul, map_map, IsScalarTower.algebraMap_eq K ↥(IntermediateField.adjoin K {α}) E]
    have hdvd : h.map (algebraMap ↥(IntermediateField.adjoin K {α}) E)
        ∣ f.map (algebraMap K E) :=
      ⟨Polynomial.map (algebraMap ↥(IntermediateField.adjoin K {α}) E) (X - C a), by
        rw [hchain, Polynomial.map_mul (algebraMap ↥(IntermediateField.adjoin K {α}) E),
          mul_comm]⟩
    have hsplh : Splits (h.map (algebraMap ↥(IntermediateField.adjoin K {α}) E)) :=
      Splits.of_dvd hspl ((Polynomial.map_ne_zero_iff hinjK).mpr hf0) hdvd
    have hsub : f.rootSet E ⊆ ↑(Algebra.adjoin ↥(IntermediateField.adjoin K {α})
        (h.rootSet E : Set E)) := by
      intro β hβ
      rw [mem_rootSet'] at hβ
      obtain ⟨-, hβ⟩ := hβ
      have hb : aeval β (f.map (algebraMap K E)) = 0 := by
        rw [aeval_map_algebraMap (A := E)]
        exact hβ
      rw [hchain, aeval_map_algebraMap (A := E), map_mul, map_sub, aeval_X, aeval_C, hcoe] at hb
      by_cases hβa : β = α
      · have hmem : ((algebraMap ↥(IntermediateField.adjoin K {α}) E) a) ∈
            ↑(Algebra.adjoin ↥(IntermediateField.adjoin K {α}) (h.rootSet E : Set E)) :=
          Subalgebra.algebraMap_mem _ a
        rw [hβa]
        exact Eq.mp (congrArg (fun x : E =>
          x ∈ ↑(Algebra.adjoin ↥(IntermediateField.adjoin K {α}) (h.rootSet E : Set E)))
          hcoe) hmem
      · have hz : aeval β h = 0 := by
          rcases mul_eq_zero.mp hb with hz | hz
          · exact absurd (sub_eq_zero.mp hz) hβa
          · exact hz
        exact Algebra.subset_adjoin (s := h.rootSet E) (mem_rootSet'.mpr ⟨hmapne0, hz⟩)
    have hadj : Algebra.adjoin ↥(IntermediateField.adjoin K {α}) (h.rootSet E : Set E) = ⊤ := by
      have key : Algebra.adjoin K (f.rootSet E : Set E) ≤
          Subalgebra.restrictScalars K (Algebra.adjoin ↥(IntermediateField.adjoin K {α})
            (h.rootSet E : Set E)) := by
        rw [Algebra.adjoin_le_iff, Subalgebra.coe_restrictScalars]
        exact hsub
      have hle : (⊤ : Subalgebra K E) ≤
          Subalgebra.restrictScalars K (Algebra.adjoin ↥(IntermediateField.adjoin K {α})
            (h.rootSet E : Set E)) :=
        hsp.adjoin_rootSet' ▸ key
      apply Subalgebra.restrictScalars_injective K
      rw [Subalgebra.restrictScalars_top]
      exact top_le_iff.mp hle
    haveI hsp2 : IsSplittingField ↥(IntermediateField.adjoin K {α}) E h := ⟨hsplh, hadj⟩
    have hdegF : Module.finrank K ↥(IntermediateField.adjoin K {α}) = (minpoly K α).natDegree :=
      IntermediateField.adjoin.finrank hαi
    have hminle : (minpoly K α).natDegree ≤ f.natDegree :=
      natDegree_le_of_dvd (minpoly.dvd K α hα0) hf0
    have ihres : Module.finrank ↥(IntermediateField.adjoin K {α}) E ≤ Nat.factorial h.natDegree :=
      ih h hnat h0
    rw [hnat] at ihres
    rw [hn] at hminle
    rw [← Module.finrank_mul_finrank K ↥(IntermediateField.adjoin K {α}) E, hdegF, hn,
      Nat.factorial_succ]
    exact Nat.mul_le_mul hminle ihres

/-- FT `sf4` (existence part). Every polynomial `f ∈ K[X]` has a splitting field: Mathlib's
canonical `Polynomial.SplittingField f` is a splitting field for `f` in the sense of the
`Polynomial.IsSplittingField K E f` predicate (the instance `Polynomial.IsSplittingField.splittingField`). -/
theorem exists_splittingField (f : K[X]) : IsSplittingField K (SplittingField f) f :=
  inferInstance

/-- The canonical splitting field is finite-dimensional over the base field (already an instance
in Mathlib; restated here for the FT record). -/
theorem finiteDimensional_splittingField (f : K[X]) :
    FiniteDimensional K (SplittingField f) :=
  inferInstance

/-- FT `sf4` (degree bound, general form). If `E` is a splitting field over `K` of the
nonzero polynomial `f ∈ K[X]`, then `[E : K] = finrank K E ≤ (deg f)!`. -/
theorem isSplittingField_finrank_le {E : Type u} [Field E] [Algebra K E]
    (f : K[X]) (hf0 : f ≠ 0) [IsSplittingField K E f] :
    Module.finrank K E ≤ Nat.factorial f.natDegree :=
  sf4_aux _ f rfl hf0

/-- FT `sf4` (degree bound). Every polynomial `f ∈ K[X]` has a splitting field `E_f` with
`[E_f : K] = finrank K E_f ≤ (deg f)!` (factorial of `deg f`).

Proof idea (Milne FT, stem-field induction): if `f ≠ 0` has a root `α` in its splitting field
`E`, then `E` is a splitting field over `K⟮α⟯` of `h = f /ₘ (X - α)` with `deg h = deg f - 1`,
so `[E : K] = [K⟮α⟯ : K] · [E : K⟮α⟯] ≤ deg f · (deg f - 1)! ≤ (deg f)!`; a nonzero constant
has splitting field `K` itself (`finrank = 1 = 0!`). -/
theorem splitField_finrank_le (f : K[X]) :
    Module.finrank K (SplittingField f) ≤ Nat.factorial f.natDegree := by
  by_cases hf0 : f = 0
  · subst hf0
    have htb : (⊤ : Subalgebra K (SplittingField (0 : K[X]))) = ⊥ :=
      (IsSplittingField.splits_iff (K := K) (L := SplittingField (0 : K[X]))
        (0 : K[X])).mp Splits.zero
    have h1 : Module.finrank K (SplittingField (0 : K[X])) = 1 := by
      rw [← Subalgebra.topEquiv.toLinearEquiv.finrank_eq, htb,
        (Algebra.botEquiv K (SplittingField (0 : K[X]))).toLinearEquiv.finrank_eq,
        Module.finrank_self]
    rw [h1, natDegree_zero, Nat.factorial_zero]
  · exact sf4_aux _ f rfl hf0

end SF4
/-- FT `sf7` (a), existence clause.  Let `f ∈ F[X]`, let `E` be an extension of `F` generated
by the roots of `f` in `E`, and let `Ω` be an extension of `F` splitting `f`.  Then there exists
an `F`-homomorphism `φ : E → Ω`.

Proof idea (following FT): each root `α` of `f` in `E` is integral over `F` (its minimal
polynomial divides the nonzero polynomial `f`), and since `f` splits in `Ω`, that minimal
polynomial also splits in `Ω`.  Hence, adjoining the finitely many roots of `f` in `E` one at a
time, each adjoin step admits a lift into `Ω` (Mathlib's `Polynomial.lift_of_splits`, the formal
heart of FT's Propositions `sf1`/`sf2`); as `E = F[roots of f in E]`, the resulting homomorphism
out of the adjoin transports to an `F`-homomorphism `E → Ω`.  The degenerate case `f = 0` is
vacuous here since Mathlib's `rootSet` of `0` is empty (so `E ≅ F` and `Ω` receives `F`). -/
theorem exists_algHom_of_adjoin_rootSet_eq_top_of_splits {F E Ω : Type*} [Field F] [Field E]
    [Field Ω] [Algebra F E] [Algebra F Ω] (f : Polynomial F)
    (hgen : Algebra.adjoin F (f.rootSet E) = ⊤)
    (hsplits : (f.map (algebraMap F Ω)).Splits) : Nonempty (E →ₐ[F] Ω) := by
  classical
  have hfin : ((f.rootSet E).toFinset : Set E) = f.rootSet E := by
    rw [← (Polynomial.rootSet_finite f E).toFinset_eq_toFinset,
      (Polynomial.rootSet_finite f E).coe_toFinset]
  have hs : ∀ x ∈ (f.rootSet E).toFinset, IsIntegral F x ∧
      ((minpoly F x).map (algebraMap F Ω)).Splits := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    obtain ⟨hmap, hae⟩ := Polynomial.mem_rootSet'.1 hx
    have hf0 : f ≠ 0 := fun h => hmap (by rw [h]; exact Polynomial.map_zero _)
    have hdvd : minpoly F x ∣ f := minpoly.dvd F x hae
    have hmi : minpoly F x ≠ 0 := fun h => hf0 (zero_dvd_iff.mp (h ▸ hdvd))
    exact ⟨minpoly.ne_zero_iff.mp hmi,
      Polynomial.Splits.of_dvd hsplits (Polynomial.map_ne_zero hf0)
        (Polynomial.map_dvd (algebraMap F Ω) hdvd)⟩
  obtain ⟨φ₀⟩ := Polynomial.lift_of_splits (f.rootSet E).toFinset hs
  exact ⟨φ₀.comp (by rw [hfin, hgen]; exact Algebra.toTop)⟩

/-- FT `sf7` (a), existence clause, special case: `E` is a splitting field for `f` (Mathlib's
`Polynomial.IsSplittingField f` on `E`) and `Ω` is an extension of `F` splitting `f`.  Then there
exists an `F`-homomorphism `E → Ω` (thin wrapper; in this case the homomorphism exists by
`Polynomial.IsSplittingField.lift` directly). -/
theorem exists_algHom_of_isSplittingField_of_splits {F E Ω : Type*} [Field F] [Field E]
    [Field Ω] [Algebra F E] [Algebra F Ω] (f : Polynomial F) [Polynomial.IsSplittingField F E f]
    (hsplits : (f.map (algebraMap F Ω)).Splits) : Nonempty (E →ₐ[F] Ω) :=
  exists_algHom_of_adjoin_rootSet_eq_top_of_splits f
    (Polynomial.IsSplittingField.adjoin_rootSet E f) hsplits
/-!
### FT `sf1`: Homomorphisms from simple extensions

FT `sf1` (Milne, *Fields and Galois Theory*, Prop. 5.6/sf1): let `F` be a field, `E` an
extension of `F`, `α : E`, and `Ω` a further extension of `F`.

(a) If `α` is transcendental over `F`, then `φ ↦ φ(α)` is a bijection from the `F`-homomorphisms
`F(α) → Ω` to the elements of `Ω` transcendental over `F`.

(b) If `α` is algebraic over `F` with minimal polynomial `f = minpoly F α`, then `φ ↦ φ(α)`
is a bijection from the `F`-homomorphisms `F[α] → Ω` to the roots of `f` in `Ω`; in particular
the number of such homomorphisms is the number of distinct roots.

Encoding: `F(α) = F[α]` is `IntermediateField.adjoin F {α}` (notation `F⟮α⟯`; for algebraic
`α` this coincides with `F[α] = Algebra.adjoin F {α}` as a subalgebra, by Mathlib's
`IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`).  The `F`-homomorphisms are
`AlgHom F (F⟮α⟯) Ω` per the chapter conventions.

Proof idea.
* (b) is Mathlib's `IntermediateField.algHomAdjoinIntegralEquiv` (via the power basis of
  `F⟮α⟯`), reindexed from `aroots` (multiset of roots) to `rootSet` (set of roots).
* (a): if `φ(α)` were algebraic over `F`, a vanishing polynomial for `φ(α)` pulls back along
  the injective `φ` to one for `α`, contradicting transcendence.  Conversely, for
  transcendental `γ ∈ Ω` the isomorphism `F[X] ≃ₐ[F] F[α]` (`Polynomial.algEquivOfTranscendental`)
  composed with evaluation at `γ` is injective, and lifts to `F⟮α⟯ = Frac F[α]` by
  `IsFractionRing.liftAlgHom`, using Mathlib's instance that `F⟮s⟯` is the fraction field of
  `F[s]` (`IntermediateField.algebraAdjoinAdjoin`).  Uniqueness is
  `IntermediateField.adjoin_algHom_ext`.
-/

open scoped IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

section SF1

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {Ω : Type*} [Field Ω]
  [Algebra F Ω] {α : E}

/-- FT `sf1` (a), forward direction: the image of `α` under an `F`-homomorphism out of `F⟮α⟯`
is transcendental over `F` (else a vanishing polynomial pulls back along the injective `φ`). -/
theorem transcendental_map_adjoinGen (hα : Transcendental F α) (φ : F⟮α⟯ →ₐ[F] Ω) :
    Transcendental F (φ (IntermediateField.AdjoinSimple.gen F α)) := by
  intro ⟨p, hp0, hp⟩
  have hinj : Function.Injective ⇑φ := φ.toRingHom.injective
  have h2 : Polynomial.aeval (IntermediateField.AdjoinSimple.gen F α) p = 0 := by
    have h1 : Polynomial.aeval (φ (IntermediateField.AdjoinSimple.gen F α)) p = 0 := hp
    rw [Polynomial.aeval_algHom_apply] at h1
    exact hinj (by rw [map_zero]; exact h1)
  have h3 : Polynomial.aeval α p = 0 := by
    rw [← IntermediateField.AdjoinSimple.coe_aeval_gen_apply F α p]
    exact congrArg Subtype.val h2
  exact hα ⟨p, hp0, h3⟩

/-- Injectivity of `p ↦ p(γ)` precomposed with `F[X] ≃ₐ[F] F[α]` (`α`, `γ` transcendental). -/
theorem injective_aeval_comp_algEquivOfTranscendental_symm (hα : Transcendental F α) {γ : Ω}
    (hγ : Transcendental F γ) :
    Function.Injective ⇑((Polynomial.aeval γ).comp
      (Polynomial.algEquivOfTranscendental F α hα).symm.toAlgHom) := by
  intro x y hxy
  simp only [AlgHom.comp_apply] at hxy
  exact (Polynomial.algEquivOfTranscendental F α hα).symm.injective
    (transcendental_iff_injective.mp hγ hxy)

/-- FT `sf1` (a), inverse construction: the `F`-homomorphism `F⟮α⟯ → Ω` sending a transcendental
`α` to a transcendental `γ ∈ Ω`.  It is the lift (`IsFractionRing.liftAlgHom`, using the
instance `IntermediateField.algebraAdjoinAdjoin.isFractionRing` that `F⟮α⟯ = Frac F[α]`) of
the injective homomorphism `F[α] → Ω`, `p(α) ↦ p(γ)`, obtained from the isomorphism
`F[X] ≃ₐ[F] F[α]` of `Polynomial.algEquivOfTranscendental` composed with evaluation at `γ`. -/
noncomputable def liftAlgHomOfTranscendental (hα : Transcendental F α) {γ : Ω}
    (hγ : Transcendental F γ) : F⟮α⟯ →ₐ[F] Ω :=
  IsFractionRing.liftAlgHom (g := (Polynomial.aeval γ).comp
    (Polynomial.algEquivOfTranscendental F α hα).symm.toAlgHom)
    (injective_aeval_comp_algEquivOfTranscendental_symm F hα hγ)

theorem liftAlgHomOfTranscendental_def (hα : Transcendental F α) {γ : Ω}
    (hγ : Transcendental F γ) : liftAlgHomOfTranscendental F hα hγ =
    IsFractionRing.liftAlgHom (g := (Polynomial.aeval γ).comp
      (Polynomial.algEquivOfTranscendental F α hα).symm.toAlgHom)
      (injective_aeval_comp_algEquivOfTranscendental_symm F hα hγ) := rfl

/-- FT `sf1` (a): the constructed homomorphism sends `α` to `γ`. -/
@[simp]
theorem liftAlgHomOfTranscendental_gen (hα : Transcendental F α) {γ : Ω}
    (hγ : Transcendental F γ) :
    liftAlgHomOfTranscendental F hα hγ (IntermediateField.AdjoinSimple.gen F α) = γ := by
  rw [liftAlgHomOfTranscendental_def, IsFractionRing.liftAlgHom_apply,
    show (IntermediateField.AdjoinSimple.gen F α : F⟮α⟯) =
      algebraMap (Algebra.adjoin F {α}) (IntermediateField.adjoin F {α})
        (⟨α, Algebra.self_mem_adjoin_singleton F α⟩ : Algebra.adjoin F {α}) from rfl,
    IsFractionRing.lift_algebraMap]
  simp

/-- FT `sf1` (a): an `F`-homomorphism out of `F⟮α⟯` is determined by the image of `α`. -/
theorem liftAlgHomOfTranscendental_unique (hα : Transcendental F α) {γ : Ω}
    (hγ : Transcendental F γ) (φ : F⟮α⟯ →ₐ[F] Ω)
    (hφ : φ (IntermediateField.AdjoinSimple.gen F α) = γ) :
    φ = liftAlgHomOfTranscendental F hα hγ :=
  IntermediateField.adjoin_algHom_ext F fun x hx => by
    obtain rfl : x = α := by simpa using hx
    exact hφ.trans (liftAlgHomOfTranscendental_gen F hα hγ).symm

/-- **FT `sf1` (a).**  For `α` transcendental over `F`, `φ ↦ φ(α)` is a bijection
`{F`-homomorphisms `F⟮α⟯ → Ω`} ↔ {elements of `Ω` transcendental over `F`}. -/
noncomputable def algHomAdjoinTranscendentalEquiv (hα : Transcendental F α) :
    (F⟮α⟯ →ₐ[F] Ω) ≃ {γ : Ω // Transcendental F γ} := by
  refine ⟨fun φ => ⟨φ (IntermediateField.AdjoinSimple.gen F α),
    transcendental_map_adjoinGen F hα φ⟩, fun γ => liftAlgHomOfTranscendental F hα γ.2, ?_, ?_⟩
  · intro φ
    exact (liftAlgHomOfTranscendental_unique F hα
      (transcendental_map_adjoinGen F hα φ) φ rfl).symm
  · intro γ
    exact Subtype.ext (liftAlgHomOfTranscendental_gen F hα γ.2)

/-- Reindexing between "roots of `p` in `Ω` as a multiset" (`p.aroots Ω`) and "roots of `p`
in `Ω` as a set" (`p.rootSet Ω`); both memberships mean `p.map (algebraMap F Ω) ≠ 0` and
`p(γ) = 0`. -/
noncomputable def arootsSubtypeEquivRootSet (p : Polynomial F) :
    {γ : Ω // γ ∈ p.aroots Ω} ≃ {γ : Ω // γ ∈ p.rootSet Ω} where
  toFun x := ⟨x.1, (Polynomial.mem_rootSet'.trans Polynomial.mem_aroots'.symm).mpr x.2⟩
  invFun x := ⟨x.1, (Polynomial.mem_rootSet'.trans Polynomial.mem_aroots'.symm).mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem arootsSubtypeEquivRootSet_apply (p : Polynomial F)
    (x : {γ : Ω // γ ∈ p.aroots Ω}) :
    arootsSubtypeEquivRootSet F p x =
      ⟨x.1, (Polynomial.mem_rootSet'.trans Polynomial.mem_aroots'.symm).mpr x.2⟩ := rfl

@[simp]
theorem arootsSubtypeEquivRootSet_symm_apply (p : Polynomial F)
    (x : {γ : Ω // γ ∈ p.rootSet Ω}) :
    (arootsSubtypeEquivRootSet F p).symm x =
      ⟨x.1, (Polynomial.mem_rootSet'.trans Polynomial.mem_aroots'.symm).mp x.2⟩ := rfl

/-- **FT `sf1` (b).**  For `α` integral over `F` with minimal polynomial `f = minpoly F α`,
`φ ↦ φ(α)` is a bijection `{F`-homomorphisms `F⟮α⟯ → Ω`} ↔ {roots of `f` in `Ω`}.  This is
Mathlib's `IntermediateField.algHomAdjoinIntegralEquiv` (roots as a multiset, via the power
basis of `F⟮α⟯`) reindexed to roots as a set by `arootsSubtypeEquivRootSet`. -/
noncomputable def algHomAdjoinIntegralEquivRootSet (hα : IsIntegral F α) :
    (F⟮α⟯ →ₐ[F] Ω) ≃ {γ : Ω // γ ∈ (minpoly F α).rootSet Ω} :=
  (IntermediateField.algHomAdjoinIntegralEquiv F hα).trans (arootsSubtypeEquivRootSet F _)

/-- FT `sf1` (b): the bijection is `φ ↦ φ(α)`. -/
theorem algHomAdjoinIntegralEquivRootSet_apply (hα : IsIntegral F α) (φ : F⟮α⟯ →ₐ[F] Ω) :
    (algHomAdjoinIntegralEquivRootSet F hα φ).1 =
      φ (IntermediateField.AdjoinSimple.gen F α) := by
  simp only [algHomAdjoinIntegralEquivRootSet, IntermediateField.algHomAdjoinIntegralEquiv,
    Equiv.trans_apply, Equiv.subtypeEquiv_apply, IntermediateField.adjoin.powerBasis_gen,
    PowerBasis.liftEquiv'_apply_coe, Equiv.refl_apply, arootsSubtypeEquivRootSet_apply]

/-- FT `sf1` (b): the inverse sends a root `γ` of `minpoly F α` to the unique `F`-homomorphism
`F⟮α⟯ → Ω` mapping `α` to `γ`. -/
theorem algHomAdjoinIntegralEquivRootSet_symm_gen (hα : IsIntegral F α)
    (γ : {γ : Ω // γ ∈ (minpoly F α).rootSet Ω}) :
    (algHomAdjoinIntegralEquivRootSet F hα).symm γ
      (IntermediateField.AdjoinSimple.gen F α) = γ.1 := by
  show (IntermediateField.algHomAdjoinIntegralEquiv F hα).symm
    ((arootsSubtypeEquivRootSet F (minpoly F α)).symm γ)
    (IntermediateField.AdjoinSimple.gen F α) = γ.1
  rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen,
    arootsSubtypeEquivRootSet_symm_apply]

/-- FT `sf1` (b), counting form: the number of `F`-homomorphisms `F⟮α⟯ → Ω` equals the number
of roots of `minpoly F α` in `Ω`. -/
theorem natCard_algHomAdjoinIntegralEquivRootSet (hα : IsIntegral F α) :
    Nat.card (F⟮α⟯ →ₐ[F] Ω) = ((minpoly F α).rootSet Ω).ncard :=
  (Nat.card_congr (algHomAdjoinIntegralEquivRootSet F hα)).trans (Nat.card_coe_set_eq _)

end SF1
/-!
### FT `sf2`: Extensions of a homomorphism to a simple extension

FT `sf2` (Milne, *Fields and Galois Theory*, Prop. 5.6/sf2): let `F(α)` be a simple
extension of `F` and `φ₀ : F →+* Ω` a homomorphism from `F` into a second field `Ω`.
An *extension of `φ₀`* to `F(α)` is a homomorphism `φ : F(α) → Ω` whose restriction to
`F` is `φ₀`.

Encoding: `Ω` is made an `F`-algebra *via* `φ₀` (`let _ : Algebra F Ω :=
RingHom.toAlgebra φ₀`; then `algebraMap F Ω = φ₀` holds by `rfl`), so FT's extensions of
`φ₀` are exactly the `AlgHom F F⟮α⟯ Ω` for the induced structure, and FT's `φ₀f` is
`f.map φ₀`.  Under this structure `Transcendental F γ` says exactly that `γ` is
transcendental over `φ₀(F)` (see `FT.transcendental_toAlgebra_iff`), while the root
condition `Polynomial.eval γ ((minpoly F α).map φ₀) = 0` does not mention the induced
structure at all.
-/

section SF2

open scoped IntermediateField
open scoped Polynomial

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {Ω : Type*} [Field Ω]
  {α : E}

/-- FT `sf2`, auxiliary (b): for a nonzero polynomial `p ∈ F[X]` and a homomorphism
`φ₀ : F →+* Ω` (making `Ω` an `F`-algebra via `φ₀`), reindexing "roots of `φ₀p` in `Ω`
as a multiset" (`p.aroots Ω`) to "roots of `φ₀p` in `Ω` as bare elements"
(`eval γ (p.map φ₀) = 0`). -/
noncomputable def sf2RootsSubtypeEquiv (φ₀ : F →+* Ω) (p : F[X]) (hp : p ≠ 0) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    {γ : Ω // γ ∈ p.aroots Ω} ≃ {γ : Ω // Polynomial.eval γ (p.map φ₀) = 0} :=
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  { toFun := fun x => ⟨x.1, by
      obtain ⟨-, hae⟩ := Polynomial.mem_aroots'.mp x.2
      rw [Polynomial.aeval_def] at hae
      rw [Polynomial.eval_map]
      exact hae⟩,
    invFun := fun x => ⟨x.1, by
      rw [Polynomial.mem_aroots']
      refine ⟨(Polynomial.map_ne_zero_iff (RingHom.injective φ₀)).mpr hp, ?_⟩
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact x.2⟩,
    left_inv := fun x => rfl,
    right_inv := fun x => rfl }

/-- **FT `sf2` (b).**  Let `F(α)` be a simple extension of `F` and `φ₀ : F →+* Ω` a
homomorphism into a second field `Ω`.  If `α` is algebraic over `F` with minimal polynomial
`f = minpoly F α`, then `φ ↦ φ(α)` is a bijection from the extensions `φ : F⟮α⟯ →ₐ[F] Ω`
of `φ₀` (i.e. `F`-algebra homomorphisms for the `F`-algebra structure on `Ω` induced by
`φ₀` via `RingHom.toAlgebra`; such a `φ` satisfies `φ (algebraMap F _ a) = φ₀ a`, so it is
an extension of `φ₀`) to the roots of `φ₀f` in `Ω`, where `φ₀f = f.map φ₀`.

In particular, the number of extensions of `φ₀` to `F[α]` is the number of distinct roots
of `φ₀f` in `Ω` (count via `Nat.card_congr sf2ExtEquiv`).

Construction: Mathlib's `IntermediateField.algHomAdjoinIntegralEquiv` (via the power basis
of `F⟮α⟯`), reindexed by `FT.sf2RootsSubtypeEquiv` from multiset-roots to bare roots. -/
noncomputable def sf2ExtEquiv (φ₀ : F →+* Ω) (hα : IsIntegral F α) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    (F⟮α⟯ →ₐ[F] Ω) ≃ {γ : Ω // Polynomial.eval γ ((minpoly F α).map φ₀) = 0} :=
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  (IntermediateField.algHomAdjoinIntegralEquiv F hα).trans
    (sf2RootsSubtypeEquiv F φ₀ (minpoly F α) (minpoly.ne_zero hα))

/-- FT `sf2` (b): the bijection is `φ ↦ φ(α)`. -/
theorem sf2ExtEquiv_apply (φ₀ : F →+* Ω) (hα : IsIntegral F α) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    ∀ (φ : F⟮α⟯ →ₐ[F] Ω),
      (sf2ExtEquiv F φ₀ hα φ).1 = φ (IntermediateField.AdjoinSimple.gen F α) := by
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  show ∀ (φ : F⟮α⟯ →ₐ[F] Ω),
    (sf2ExtEquiv F φ₀ hα φ).1 = φ (IntermediateField.AdjoinSimple.gen F α)
  intro φ
  simp only [sf2ExtEquiv, Equiv.trans_apply, IntermediateField.algHomAdjoinIntegralEquiv,
    Equiv.subtypeEquiv_apply, IntermediateField.adjoin.powerBasis_gen,
    PowerBasis.liftEquiv'_apply_coe, Equiv.refl_apply]
  rfl

/-- FT `sf2` (b): the inverse sends a root `γ` of `φ₀(minpoly F α)` to the extension
`F⟮α⟯ → Ω` of `φ₀` mapping `α` to `γ`. -/
theorem sf2ExtEquiv_symm_gen (φ₀ : F →+* Ω) (hα : IsIntegral F α) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    ∀ (γ : {γ : Ω // Polynomial.eval γ ((minpoly F α).map φ₀) = 0}),
      (sf2ExtEquiv F φ₀ hα).symm γ (IntermediateField.AdjoinSimple.gen F α) = γ.1 := by
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  show ∀ (γ : {γ : Ω // Polynomial.eval γ ((minpoly F α).map φ₀) = 0}),
    (sf2ExtEquiv F φ₀ hα).symm γ (IntermediateField.AdjoinSimple.gen F α) = γ.1
  intro γ
  show (IntermediateField.algHomAdjoinIntegralEquiv F hα).symm
    ((sf2RootsSubtypeEquiv F φ₀ (minpoly F α) (minpoly.ne_zero hα)).symm γ)
    (IntermediateField.AdjoinSimple.gen F α) = γ.1
  rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
  rfl

/-- **FT `sf2` (a).**  Let `F(α)` be a simple extension of `F` and `φ₀ : F →+* Ω` a
homomorphism into a second field `Ω`.  If `α` is transcendental over `F`, then `φ ↦ φ(α)`
is a bijection from the extensions `φ : F⟮α⟯ →ₐ[F] Ω` of `φ₀` (`F`-algebra homomorphisms
for the `F`-algebra structure on `Ω` induced by `φ₀` via `RingHom.toAlgebra`) to the
elements of `Ω` transcendental over `φ₀(F)` — encoded as `Transcendental F γ` for the
induced structure: no nonzero `p ∈ F[X]` has `p(γ) = 0` after applying `φ₀` to the
coefficients.

This is FT's `sf2` (a); it is FT `sf1` (a) (`FT.algHomAdjoinTranscendentalEquiv`) read
over the `φ₀`-induced `F`-algebra structure on `Ω`. -/
noncomputable def sf2ExtTranscendentalEquiv (φ₀ : F →+* Ω) (hα : Transcendental F α) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    (F⟮α⟯ →ₐ[F] Ω) ≃ {γ : Ω // Transcendental F γ} :=
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  algHomAdjoinTranscendentalEquiv F hα

/-- FT `sf2` (a), interpretation: for the `F`-algebra structure on `Ω` induced by `φ₀`,
`Transcendental F γ` says exactly that `γ` is transcendental over `φ₀(F)` in FT's sense:
no nonzero `p ∈ F[X]` vanishes at `γ` after `φ₀` is applied to its coefficients. -/
theorem transcendental_toAlgebra_iff (φ₀ : F →+* Ω) (γ : Ω) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    (Transcendental F γ ↔ ∀ p : F[X], p ≠ 0 → Polynomial.eval γ (p.map φ₀) ≠ 0) := by
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  show (Transcendental F γ ↔ ∀ p : F[X], p ≠ 0 → Polynomial.eval γ (p.map φ₀) ≠ 0)
  constructor
  · intro h p hp hev
    exact h ⟨p, hp, by rw [Polynomial.aeval_def]; rw [Polynomial.eval_map] at hev; exact hev⟩
  · intro h ⟨p, hp, hae⟩
    refine h p hp ?_
    rw [Polynomial.aeval_def] at hae
    rw [Polynomial.eval_map]
    exact hae

/-- FT `sf2` (a): the bijection is `φ ↦ φ(α)`. -/
theorem sf2ExtTranscendentalEquiv_apply (φ₀ : F →+* Ω) (hα : Transcendental F α) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    ∀ (φ : F⟮α⟯ →ₐ[F] Ω),
      (sf2ExtTranscendentalEquiv F φ₀ hα φ).1 =
        φ (IntermediateField.AdjoinSimple.gen F α) := by
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  show ∀ (φ : F⟮α⟯ →ₐ[F] Ω),
    (sf2ExtTranscendentalEquiv F φ₀ hα φ).1 = φ (IntermediateField.AdjoinSimple.gen F α)
  intro φ
  rfl

/-- FT `sf2` (a): the inverse sends `γ` transcendental over `φ₀(F)` to the extension
`F⟮α⟯ → Ω` of `φ₀` mapping `α` to `γ`. -/
theorem sf2ExtTranscendentalEquiv_symm_gen (φ₀ : F →+* Ω) (hα : Transcendental F α) :
    let _ : Algebra F Ω := RingHom.toAlgebra φ₀
    ∀ (γ : {γ : Ω // Transcendental F γ}),
      (sf2ExtTranscendentalEquiv F φ₀ hα).symm γ
        (IntermediateField.AdjoinSimple.gen F α) = γ.1 := by
  letI : Algebra F Ω := RingHom.toAlgebra φ₀
  show ∀ (γ : {γ : Ω // Transcendental F γ}),
    (sf2ExtTranscendentalEquiv F φ₀ hα).symm γ
      (IntermediateField.AdjoinSimple.gen F α) = γ.1
  intro γ
  show (FT.liftAlgHomOfTranscendental F hα γ.2)
    (IntermediateField.AdjoinSimple.gen F α) = γ.1
  exact FT.liftAlgHomOfTranscendental_gen F hα γ.2

end SF2

section FT3

open Polynomial

variable {F : Type*} [Field F] {f : F[X]}

/-- FT `ft3` auxiliary: a nonzero polynomial stays nonzero under the (injective) algebra map
into its canonical splitting field `Polynomial.SplittingField f`. -/
private theorem ft3_map_ne_zero (hf : f ≠ 0) :
    f.map (algebraMap F f.SplittingField) ≠ 0 :=
  (Polynomial.map_ne_zero_iff (algebraMap F f.SplittingField).injective).mpr hf

/-- FT `ft3` auxiliary: the canonical splitting field `Polynomial.SplittingField f` splits `f`
(field of the `IsSplittingField` structure of `f.SplittingField`). -/
private theorem ft3_splits : (f.map (algebraMap F f.SplittingField)).Splits :=
  (IsSplittingField.splittingField f).splits'

/-- FT `ft3` auxiliary: a nonconstant irreducible polynomial has a root in its canonical
splitting field (its map splits there and has positive degree, so its `roots` is nonempty). -/
private theorem ft3_exists_root (hf : Irreducible f) :
    ∃ ζ, ζ ∈ (f.map (algebraMap F f.SplittingField)).roots := by
  have hfnd : f.natDegree ≠ 0 :=
    ((natDegree_pos_iff_degree_pos).mpr (degree_pos_of_irreducible hf)).ne'
  exact Multiset.exists_mem_of_ne_zero
    (ft3_splits.roots_ne_zero (by rw [natDegree_map]; exact hfnd))

/-- FT `ft3` auxiliary (source eq. (2) step): a common root `ζ` of `f` and `f'` in the
splitting field of `f` obstructs separability, because mapping a Bézout identity
`u · f + v · f' = 1` into the splitting field and evaluating at `ζ` gives `0 = 1`. -/
private theorem ft3_notSeparable_of_commonRoot {ζ : f.SplittingField}
    (hr1 : (f.map (algebraMap F f.SplittingField)).IsRoot ζ)
    (hr2 : ((f.map (algebraMap F f.SplittingField)).derivative).IsRoot ζ) :
    ¬ f.Separable := by
  intro hsep
  have hcop : IsCoprime (f.map (algebraMap F f.SplittingField))
      ((f.map (algebraMap F f.SplittingField)).derivative) := by
    rw [derivative_map]
    exact IsCoprime.map ((separable_def f).1 hsep)
      (mapRingHom (algebraMap F f.SplittingField))
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (((u * f.map (algebraMap F f.SplittingField) +
      v * (f.map (algebraMap F f.SplittingField)).derivative :
      f.SplittingField[X]).eval ζ)) = 1 := by
    rw [huv]; simp
  have e1 : (f.map (algebraMap F f.SplittingField)).eval ζ = 0 := hr1
  have e2 : ((f.map (algebraMap F f.SplittingField)).derivative).eval ζ = 0 := hr2
  simp only [eval_add, eval_mul] at h1
  rw [e1, e2] at h1
  simp at h1

/-- FT `ft3` auxiliary: if `f' = 0` for a nonconstant irreducible `f`, then `F` has nonzero
characteristic `p = ringChar F` and `f` is a polynomial in `X ^ p`, namely
`f = (contract p f)(X ^ p)` (Mathlib's `Polynomial.contract`). -/
private theorem ft3_char_of_derivative_eq_zero (hf : Irreducible f)
    (hf' : derivative f = 0) :
    ringChar F ≠ 0 ∧ ∃ g : F[X], f = g.comp (X ^ ringChar F) := by
  have hrc : ringChar F ≠ 0 := by
    intro h0
    haveI hchar : CharP F 0 := by have h := ringChar.charP F; rwa [h0] at h
    haveI : CharZero F := CharP.charP_to_charZero F
    exact ((natDegree_pos_iff_degree_pos).mpr (degree_pos_of_irreducible hf)).ne'
      (derivative_eq_zero |>.1 hf')
  exact ⟨hrc, contract (ringChar F) f, by
    rw [← expand_eq_comp_X_pow, expand_contract (ringChar F) hf' hrc]⟩

/-- FT `ft3` auxiliary: if `f = g(X ^ p)` with `p = ringChar F`, then `f' = 0`, since
`(X ^ p)' = p · X ^ (p - 1) = 0` in characteristic `p`. -/
private theorem ft3_derivative_eq_zero_of_comp (g : F[X])
    (hgc : f = g.comp (X ^ ringChar F)) :
    derivative f = 0 := by
  have hpF : (ringChar F : F) = 0 := (ringChar.spec F (ringChar F)).mpr dvd_rfl
  rw [hgc, derivative_comp, derivative_X_pow, hpF, C_0, zero_mul, zero_mul]

/-- **FT `ft3`** (source, Proposition ft3).  For a nonconstant irreducible polynomial
`f ∈ F[X]` the following are equivalent:
(a) `f` has a multiple root (in the canonical splitting field `Polynomial.SplittingField f`);
(b) `gcd(f, f') ≠ 1`, i.e. `f` is not separable (Mathlib's `Polynomial.Separable`, defined
as `IsCoprime f (derivative f)`);
(c) `F` has nonzero characteristic `p` and `f` is a polynomial in `X ^ p`
(namely `p = ringChar F`);
(d) all the roots of `f` are multiple.

Proof idea (following the text).  The key identity (source eq. (2)) that a root of `f` is
multiple iff it is also a root of `f'` is Mathlib's
`Polynomial.one_lt_rootMultiplicity_iff_isRoot`.  (a) → (b): a common root of `f` and `f'`
evaluates a Bézout identity for `(f, f')` to `0 = 1`.  (b) → (c): since `deg f' < deg f`,
`gcd(f, f') ≠ 1` forces `f' = 0` for irreducible `f`
(`Polynomial.separable_iff_derivative_ne_zero`), and then `f = g(X ^ ringChar F)` by
Mathlib's `Polynomial.contract`.  (c) → (d): `f = g(X ^ p)` has `f' = 0`, so every root of
`f` is multiple by eq. (2) again.  (d) → (a): `f` has a root in its splitting field. -/
theorem ft3 (hf : Irreducible f) :
    ((∃ ζ ∈ (f.map (algebraMap F f.SplittingField)).roots,
        1 < (f.map (algebraMap F f.SplittingField)).rootMultiplicity ζ) ↔
      ¬f.Separable) ∧
    (¬f.Separable ↔
      ringChar F ≠ 0 ∧ ∃ g : F[X], f = g.comp (X ^ ringChar F)) ∧
    ((ringChar F ≠ 0 ∧ ∃ g : F[X], f = g.comp (X ^ ringChar F)) ↔
      ∀ ζ ∈ (f.map (algebraMap F f.SplittingField)).roots,
        1 < (f.map (algebraMap F f.SplittingField)).rootMultiplicity ζ) := by
  have hinj : Function.Injective (algebraMap F f.SplittingField) :=
    (algebraMap F f.SplittingField).injective
  have hfm : f.map (algebraMap F f.SplittingField) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hf.ne_zero
  have hroot := ft3_exists_root hf
  refine ⟨?_, ?_, ?_⟩
  · -- (a) ↔ (b)
    constructor
    · rintro ⟨ζ, hζ, hm⟩
      obtain ⟨hr1, hr2⟩ := (one_lt_rootMultiplicity_iff_isRoot hfm).1 hm
      exact ft3_notSeparable_of_commonRoot hr1 hr2
    · intro hsep
      have hf' : derivative f = 0 := by
        by_contra h
        exact hsep ((separable_iff_derivative_ne_zero hf).2 h)
      obtain ⟨ζ, hζ⟩ := hroot
      refine ⟨ζ, hζ, ?_⟩
      rw [one_lt_rootMultiplicity_iff_isRoot hfm]
      exact ⟨(mem_roots' |>.1 hζ).2, by
        rw [derivative_map, hf', Polynomial.map_zero]; exact eval_zero⟩
  · -- (b) ↔ (c)
    constructor
    · intro hsep
      exact ft3_char_of_derivative_eq_zero hf
        (by by_contra h; exact hsep ((separable_iff_derivative_ne_zero hf).2 h))
    · rintro ⟨hrc, g, hgc⟩ hsep
      exact absurd (ft3_derivative_eq_zero_of_comp g hgc)
        ((separable_iff_derivative_ne_zero hf).1 hsep)
  · -- (c) ↔ (d)
    constructor
    · rintro ⟨hrc, g, hgc⟩ ζ hζ
      have hf' := ft3_derivative_eq_zero_of_comp g hgc
      rw [one_lt_rootMultiplicity_iff_isRoot hfm]
      exact ⟨(mem_roots' |>.1 hζ).2, by
        rw [derivative_map, hf', Polynomial.map_zero]; exact eval_zero⟩
    · intro hd
      obtain ⟨ζ, hζ⟩ := hroot
      obtain ⟨hr1, hr2⟩ := (one_lt_rootMultiplicity_iff_isRoot hfm).1 (hd ζ hζ)
      have hns := ft3_notSeparable_of_commonRoot hr1 hr2
      exact ft3_char_of_derivative_eq_zero hf
        (by by_contra h; exact hns ((separable_iff_derivative_ne_zero hf).2 h))

end FT3
section FT3A

open Polynomial

variable {F : Type*} [Field F]

/-- FT `ft4` (Bourbaki's definition, condition (ii) of FT `ft3a`).  The polynomial `f ∈ F[X]`
has *only simple roots* if every root of `f` in the canonical splitting field
`Polynomial.SplittingField f` has multiplicity exactly one.  (The source says "in an
extension of `F` splitting `f`"; we use Mathlib's canonical splitting field.) -/
def OnlySimpleRoots (f : F[X]) : Prop :=
  ∀ ζ ∈ (f.map (algebraMap F (SplittingField f))).roots,
    rootMultiplicity ζ (f.map (algebraMap F (SplittingField f))) = 1

/-- FT `ft3a` (helper).  "Only simple roots" is the same as the roots multiset being
duplicate-free, i.e. every root occurring with multiplicity `≤ 1`.  Proof: a root has
multiplicity ≥ 1 (`Multiset.one_le_count_iff_mem`, `Polynomial.count_roots`), so
multiplicity exactly one is multiplicity ≤ 1 for members and vacuous for nonmembers. -/
theorem onlySimpleRoots_iff_nodup {f : F[X]} (hf : f ≠ 0) :
    OnlySimpleRoots f ↔ (f.map (algebraMap F (SplittingField f))).roots.Nodup := by
  classical
  have hg : (f.map (algebraMap F (SplittingField f))) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F (SplittingField f)).injective).2 hf
  constructor
  · intro h
    rw [Multiset.nodup_iff_count_le_one]
    intro ζ
    by_cases hmem : ζ ∈ (f.map (algebraMap F (SplittingField f))).roots
    · rw [Polynomial.count_roots (f.map (algebraMap F (SplittingField f))), h ζ hmem]
    · rw [Polynomial.count_roots (f.map (algebraMap F (SplittingField f))),
        rootMultiplicity_eq_zero (fun hroot ↦ hmem ((Polynomial.mem_roots hg).2 hroot))]
      exact Nat.zero_le 1
  · intro hnodup ζ hmem
    have h1 : 1 ≤ (f.map (algebraMap F (SplittingField f))).roots.count ζ :=
      Multiset.one_le_count_iff_mem.2 hmem
    have h2 : (f.map (algebraMap F (SplittingField f))).roots.count ζ ≤ 1 :=
      Multiset.nodup_iff_count_le_one.1 hnodup ζ
    rw [← Polynomial.count_roots (f.map (algebraMap F (SplittingField f)))]
    exact Nat.le_antisymm h2 h1

/-- FT `ft3a`.  For a nonzero polynomial `f ∈ F[X]` the following are equivalent:
(i) `gcd(f, f′) = 1` in `F[X]`, i.e. `IsCoprime f (derivative f)`, Mathlib's
`Polynomial.Separable f`; (ii) `f` has only simple roots (`FT.OnlySimpleRoots`).
Proof (FT, via FT eq2): a root of `f` is multiple iff it is also a root of `f′`
(Mathlib's `Polynomial.one_lt_rootMultiplicity_iff_isRoot`, the packaged form of
eq2's computation `f′ = m(X−ζ)^{m−1}g + (X−ζ)^m g′` for `f = (X−ζ)^m g`).  If `f` and
`f′` had a common root in a splitting extension, the roots multiset would have a
repeated entry; Mathlib's `Polynomial.nodup_roots_iff_of_splits` (whose proof extracts
a root of a nonunit `gcd` of `f` and `f′` and evaluates the Bezout identity at it,
yielding `1 = 0`) gives nonseparability; conversely
`Polynomial.rootMultiplicity_le_one_of_separable` forces every root multiplicity `≤ 1`
there. -/
theorem onlySimpleRoots_iff_separable {f : F[X]} (hf : f ≠ 0) :
    OnlySimpleRoots f ↔ f.Separable := by
  have hg : (f.map (algebraMap F (SplittingField f))) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F (SplittingField f)).injective).2 hf
  rw [onlySimpleRoots_iff_nodup hf, nodup_roots_iff_of_splits hg (SplittingField.splits f),
    separable_map (algebraMap F _)]

/-- FT `ft4` (Bourbaki's definition).  A polynomial is *separable* if it is nonzero and
satisfies the equivalent conditions of FT `ft3a`.  Mathlib encodes this as
`Polynomial.Separable f` (`IsCoprime f (derivative f)`), for which nonvanishing is
automatic (`Polynomial.Separable.ne_zero`); hence FT `ft4` = `Polynomial.Separable`.
(Bourbaki's footnote: Jacobson's variant, "each irreducible factor has only simple
roots", is `Polynomial.separable_iff_derivative_ne_zero` for irreducible polynomials.) -/
theorem separable_iff_nonzero_and_onlySimpleRoots (f : F[X]) :
    f.Separable ↔ (f ≠ 0 ∧ OnlySimpleRoots f) := by
  constructor
  · intro h
    exact ⟨h.ne_zero, (onlySimpleRoots_iff_separable h.ne_zero).2 h⟩
  · rintro ⟨h0, hr⟩
    exact (onlySimpleRoots_iff_separable h0).1 hr

end FT3A
section FT5

/-- FT `ft2` (auxiliary).  In characteristic `p` the binomial/Frobenius expansion collapses:
`(X - C b) ^ p = X ^ p - C (b ^ p)`, i.e. `X ^ p - C a = (X - C b) ^ p` whenever `a = b ^ p`.
Proof: `expand F p (X - C b) = X ^ p - C b` (`Polynomial.expand_X`, `Polynomial.expand_C`,
mixed coefficients are killed by the characteristic), and `Polynomial.map_frobenius_expand`
identifies `expand F p (X - C b)` mapped by Frobenius with `(X - C b) ^ p`. -/
theorem X_pow_sub_C_eq_sub_pow {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (b : F) :
    Polynomial.X ^ p - Polynomial.C (b ^ p) = (Polynomial.X - Polynomial.C b) ^ p := by
  rw [← Polynomial.map_frobenius_expand p (Polynomial.X - Polynomial.C b)]
  have h : Polynomial.expand F p (Polynomial.X - Polynomial.C b) =
      Polynomial.X ^ p - Polynomial.C b := by
    simp [Polynomial.expand_X, Polynomial.expand_C]
  rw [h, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, frobenius_def]

/-- FT `ft2` (auxiliary).  In characteristic `p` the derivative of `X ^ p - C a` is
`C p * X ^ (p - 1) - 0 = 0` because `p = 0` in `F`. -/
theorem derivative_X_pow_sub_C_eq_zero {F : Type*} [Field F] {p : ℕ} [CharP F p] (a : F) :
    (Polynomial.X ^ p - Polynomial.C a).derivative = 0 := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
    CharP.cast_eq_zero]
  simp

/-- FT `ft2` (example, "multiple roots" half).  If `F` has characteristic `p` prime, then
`X ^ p - C a` is *not* separable (FT `ft4` fails for it): its derivative is `0`, so
`IsCoprime (X ^ p - C a) 0` would force `X ^ p - C a` to be a unit, while its degree is
`p > 0` (`Polynomial.degree_X_pow_sub_C`). -/
theorem not_separable_X_pow_sub_C {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) [CharP F p]
    (a : F) : ¬ (Polynomial.X ^ p - Polynomial.C a).Separable := by
  have hd := derivative_X_pow_sub_C_eq_zero a
  intro h
  rw [Polynomial.separable_def, hd, isCoprime_zero_right,
    Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_X_pow_sub_C hp.pos] at h
  exact hp.ne_zero (Nat.cast_eq_zero.mp h)

/-- FT `ft2` (example, "irreducible" half).  If `p` is prime and `a : F` is not a `p`th power
in `F` (`∀ b : F, b ^ p ≠ a`), then `X ^ p - C a` is irreducible in `F[X]`.  This wraps
Mathlib's `X_pow_sub_C_irreducible_of_prime` (Mathlib/FieldTheory/KummerPolynomial.lean;
`X_pow_sub_C_irreducible_iff_of_prime` gives the converse), whose proof is the classical one:
in a splitting field `X ^ p - C a = (X - C α) ^ p`, so any proper factor is a unit times
`(X - C α) ^ m` with `0 < m < p`, and its constant term would exhibit `a` as a `p`th power
since `gcd (m, p) = 1`. -/
theorem X_pow_sub_C_irreducible_of_not_pow {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    [CharP F p] {a : F} (ha : ∀ b : F, b ^ p ≠ a) :
    Irreducible (Polynomial.X ^ p - Polynomial.C a) :=
  X_pow_sub_C_irreducible_of_prime hp ha

/-- FT `ft2` (example).  In characteristic `p` prime, `X ^ p - C a` with `a : F` not a
`p`th power is irreducible in `F[X]` but has multiple roots: it is not separable (FT `ft4`). -/
theorem irreducible_not_separable_X_pow_sub_C {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    [CharP F p] {a : F} (ha : ∀ b : F, b ^ p ≠ a) :
    Irreducible (Polynomial.X ^ p - Polynomial.C a) ∧
      ¬ (Polynomial.X ^ p - Polynomial.C a).Separable :=
  ⟨X_pow_sub_C_irreducible_of_not_pow hp ha, not_separable_X_pow_sub_C hp a⟩

/-- FT `ft5`, forward direction.  A perfect field in the sense of FT `ft4m` is perfect in the
sense of Mathlib (every irreducible is separable).  Characteristic zero is `Irreducible.separable`
(as in `PerfectField.ofCharZero`); in characteristic `p = ringChar F` the surjectivity
`∀ a, ∃ b, a = b ^ p` of FT `ft4m` makes the Frobenius automorphism bijective (injectivity is
`frobenius_inj`, a field is reduced), so `PerfectRing.toPerfectField` applies. -/
theorem perfectField_of_perfectFT (F : Type*) [Field F] (h : FT.PerfectFT F) : PerfectField F := by
  rcases h with h0 | ⟨hp, hsurj⟩
  · haveI := h0
    exact ⟨fun hf => hf.separable⟩
  · haveI : CharP F (ringChar F) := ringChar.charP F
    have hprime : (ringChar F).Prime := (CharP.char_is_prime_or_zero F _).resolve_right hp
    haveI : ExpChar F (ringChar F) := ExpChar.prime hprime
    haveI : PerfectRing F (ringChar F) :=
      ⟨⟨frobenius_inj F (ringChar F), fun y =>
          ⟨(hsurj y).choose, (hsurj y).choose_spec.symm⟩⟩⟩
    exact PerfectRing.toPerfectField F (ringChar F)

/-- FT `ft5`, reverse direction.  A Mathlib-perfect field is perfect in the sense of FT `ft4m`:
if `ringChar F = 0` we are done (`CharP.ringChar_zero_iff_CharZero`); otherwise `ringChar F` is
prime, and if some `a : F` were not a `p`th power then `X ^ p - C a` would be irreducible
(`X_pow_sub_C_irreducible_of_prime`, FT `ft2`) yet inseparable (FT `ft2`, derivative `0`),
contradicting `PerfectField.separable_of_irreducible`.  This is Mathlib's
`PerfectField.toPerfectRing` argument. -/
theorem perfectFT_of_perfectField (F : Type*) [Field F] (h : PerfectField F) : FT.PerfectFT F := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hprime | h0
  · right
    refine ⟨hprime.ne_zero, fun a => ?_⟩
    by_contra hn
    exact not_separable_X_pow_sub_C hprime a
      (h.separable_of_irreducible
        (X_pow_sub_C_irreducible_of_prime hprime (fun b hb => hn ⟨b, hb.symm⟩)))
  · left
    exact CharP.ringChar_zero_iff_CharZero F |>.mp h0

/-- FT `ft5`.  FT `ft4m` (`FT.PerfectFT`: characteristic zero, or characteristic `p ≠ 0` with
every element a `p`th power) is equivalent to Mathlib's `PerfectField` (every irreducible
polynomial is separable). -/
theorem perfectFT_iff_perfectField (F : Type*) [Field F] :
    FT.PerfectFT F ↔ PerfectField F :=
  ⟨perfectField_of_perfectFT F, perfectFT_of_perfectField F⟩

end FT5
/-!
### FT `sf7`: counting `F`-homomorphisms of root-generated extensions; isomorphism of
splitting fields

FT `sf7` (Milne, *Fields and Galois Theory*, Prop. sf7).  Let `f ∈ F[X]`, let `E` be an
extension of `F` generated by the roots of `f` in `E` (encoded `Algebra.adjoin F (f.rootSet E) =
⊤`), and let `Ω` be an extension of `F` splitting `f` (`(f.map (algebraMap F Ω)).Splits`).

(a) There exists an `F`-homomorphism `E → Ω` (delivered above as
`FT.exists_algHom_of_adjoin_rootSet_eq_top_of_splits`); the number of such homomorphisms is at
most `[E : F] = Module.finrank F E` (`natCard_algHom_le_of_adjoin_rootSet_eq_top_of_splits`),
with equality when `f` has distinct roots in `Ω` (encoded `(f.map (algebraMap F Ω)).roots`
is `Nodup`; `natCard_algHom_eq_of_adjoin_rootSet_eq_top_of_splits`).

(b) If `E` and `Ω` are both splitting fields for `f` (`Polynomial.IsSplittingField`), then every
`F`-homomorphism `E → Ω` is an `F`-isomorphism
(`algEquiv_of_algHom_of_isSplittingField`); in particular any two splitting fields for `f` are
`F`-isomorphic (`exists_algEquiv_of_isSplittingField`).
-/

section SF7

open scoped IntermediateField
open Polynomial

variable {F E Ω : Type*} [Field F] [Field E] [Algebra F E] [Field Ω] [Algebra F Ω]

/-- FT `sf7` (a), auxiliary.  If `s ∈ E` is a root of `f ∈ F[X]` (i.e. `s ∈ f.rootSet E`), then
`s` is integral over `F`, and if `Ω` is an extension of `F` splitting `f`, then the minimal
polynomial of `s` over `F` splits in `Ω` (it divides `f`, and `f` splits in `Ω`). -/
theorem isIntegral_and_splits_of_mem_rootSet {f : F[X]} {s : E} (hmem : s ∈ f.rootSet E)
    (hsplits : (f.map (algebraMap F Ω)).Splits) :
    IsIntegral F s ∧ ((minpoly F s).map (algebraMap F Ω)).Splits := by
  obtain ⟨hf0, hae⟩ := Polynomial.mem_rootSet'.1 hmem
  have hf0' : f ≠ 0 := fun h => hf0 (by rw [h]; exact Polynomial.map_zero _)
  have hdvd : minpoly F s ∣ f := minpoly.dvd F s hae
  exact ⟨isAlgebraic_iff_isIntegral.mp ⟨f, hf0', hae⟩,
    Polynomial.Splits.of_dvd hsplits (Polynomial.map_ne_zero hf0')
      (Polynomial.map_dvd (algebraMap F Ω) hdvd)⟩

/-- FT `sf7` (a), auxiliary.  If `E` is generated over `F` by the roots of `f` in `E` (encoded as
`Algebra.adjoin F (f.rootSet E) = ⊤`), then the intermediate field generated by these roots is
top: `IntermediateField.adjoin F (f.rootSet E) = ⊤`. -/
private lemma intermediateField_adjoin_rootSet_eq_top (f : F[X])
    (hgen : Algebra.adjoin F (f.rootSet E) = ⊤) :
    IntermediateField.adjoin F (f.rootSet E : Set E) = ⊤ := by
  refine top_le_iff.mp (fun x _ => ?_)
  exact IntermediateField.algebra_adjoin_le_adjoin F (f.rootSet E : Set E) (by rw [hgen]; trivial)

/-- FT `sf7` (a), auxiliary.  If `E` is generated over `F` by the roots of `f` in `E` and `Ω`
splits `f`, then `E` is finite-dimensional over `F`: it is the (top) intermediate field generated
by the finitely many roots, each of which is integral over `F`. -/
private lemma finiteDimensional_of_adjoin_rootSet (f : F[X])
    (hgen : Algebra.adjoin F (f.rootSet E) = ⊤)
    (hsplits : (f.map (algebraMap F Ω)).Splits) : FiniteDimensional F E := by
  have hadj : IntermediateField.adjoin F (f.rootSet E : Set E) = ⊤ :=
    intermediateField_adjoin_rootSet_eq_top f hgen
  haveI hfd1 : FiniteDimensional F ↥(IntermediateField.adjoin F (f.rootSet E : Set E)) :=
    IntermediateField.finiteDimensional_adjoin
      (fun s hs => (isIntegral_and_splits_of_mem_rootSet hs hsplits).1)
  refine FiniteDimensional.of_injective
    (((IntermediateField.equivOfEq hadj).trans (IntermediateField.topEquiv)).symm.toLinearMap) ?_
  intro x y h
  exact ((IntermediateField.equivOfEq hadj).trans (IntermediateField.topEquiv)).symm.injective h

/-- FT `sf7` (a), counting clause, upper bound.  Let `f ∈ F[X]`, let `E` be an extension of `F`
generated by the roots of `f` in `E` (encoded `Algebra.adjoin F (f.rootSet E) = ⊤`), and let `Ω`
be an extension of `F` splitting `f`.  The number of `F`-homomorphisms `E → Ω` is at most
`[E : F] = Module.finrank F E`.

Proof idea: by `Field.finSepDegree_eq_of_adjoin_splits` the number of `F`-homomorphisms equals
the separable degree `Field.finSepDegree F E`, which is at most the degree `Module.finrank F E`
(`Field.finSepDegree_le_finrank`). -/
theorem natCard_algHom_le_of_adjoin_rootSet_eq_top_of_splits (f : F[X])
    (hgen : Algebra.adjoin F (f.rootSet E) = ⊤)
    (hsplits : (f.map (algebraMap F Ω)).Splits) :
    Nat.card (E →ₐ[F] Ω) ≤ Module.finrank F E := by
  haveI hfd : FiniteDimensional F E := finiteDimensional_of_adjoin_rootSet f hgen hsplits
  rw [← Field.finSepDegree_eq_of_adjoin_splits F E Ω
    (intermediateField_adjoin_rootSet_eq_top f hgen)
    (fun s hs => (isIntegral_and_splits_of_mem_rootSet hs hsplits))]
  exact Field.finSepDegree_le_finrank F E

/-- FT `sf7` (a), counting clause, equality.  Let `f ∈ F[X]`, let `E` be an extension of `F`
generated by the roots of `f` in `E`, and let `Ω` be an extension of `F` splitting `f` with
distinct roots (`(f.map (algebraMap F Ω)).roots` is duplicate-free).  Then the number of
`F`-homomorphisms `E → Ω` equals `[E : F] = Module.finrank F E`.

Proof idea: as in the upper bound, the number of homomorphisms is the separable degree; `f`
having distinct roots in `Ω` forces `f` separable (`Polynomial.nodup_roots_iff_of_splits` and
`Polynomial.separable_map`), hence every root of `f` is separable over `F`, hence `E = F[roots]`
is separable over `F`, and for separable finite extensions the separable degree equals the
degree (`Field.finSepDegree_eq_finrank_of_isSeparable`). -/
theorem natCard_algHom_eq_of_adjoin_rootSet_eq_top_of_splits (f : F[X])
    (hgen : Algebra.adjoin F (f.rootSet E) = ⊤)
    (hsplits : (f.map (algebraMap F Ω)).Splits)
    (hnodup : (f.map (algebraMap F Ω)).roots.Nodup) :
    Nat.card (E →ₐ[F] Ω) = Module.finrank F E := by
  classical
  haveI hfd : FiniteDimensional F E := finiteDimensional_of_adjoin_rootSet f hgen hsplits
  have hsep : Algebra.IsSeparable F E := by
    have key : ∀ s ∈ (f.rootSet E : Set E), IsSeparable F s := by
      intro s hs
      obtain ⟨hf0, hae⟩ := Polynomial.mem_rootSet'.1 hs
      have hf0' : f ≠ 0 := fun h => hf0 (by rw [h]; exact Polynomial.map_zero _)
      have hdvd : minpoly F s ∣ f := minpoly.dvd F s hae
      have h1 : (f.map (algebraMap F Ω)) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (algebraMap F Ω).injective).mpr hf0'
      have hsepF : f.Separable := by
        rw [← Polynomial.separable_map (algebraMap F Ω)]
        exact (nodup_roots_iff_of_splits h1 hsplits).mp hnodup
      exact Separable.of_dvd hsepF hdvd
    rw [← AlgEquiv.Algebra.isSeparable_iff
      (((IntermediateField.equivOfEq (intermediateField_adjoin_rootSet_eq_top f hgen)).trans
        (IntermediateField.topEquiv)))]
    exact (IntermediateField.isSeparable_adjoin_iff_isSeparable F _).mpr key
  rw [← Field.finSepDegree_eq_of_adjoin_splits F E Ω
    (intermediateField_adjoin_rootSet_eq_top f hgen)
    (fun s hs => (isIntegral_and_splits_of_mem_rootSet hs hsplits))]
  exact Field.finSepDegree_eq_finrank_of_isSeparable F E

/-- FT `sf7` (b).  Let `f ∈ F[X]`, and let `E` and `Ω` be splitting fields for `f` (Mathlib's
`Polynomial.IsSplittingField`).  Then every `F`-homomorphism `φ : E → Ω` is an `F`-isomorphism:
it is of the form `⇑e` for an `F`-isomorphism `e : E ≃ₐ[F] Ω`.

Proof idea (FT): `φ` is injective (a homomorphism of fields); the canonical identifications of
`E` and `Ω` with the model splitting field `f.SplittingField` (`IsSplittingField.algEquiv`)
give `[E : F] = [Ω : F]`; an injective linear map between finite-dimensional spaces of equal
dimension is bijective, so `φ` is surjective as well. -/
theorem algEquiv_of_algHom_of_isSplittingField (f : F[X]) [Polynomial.IsSplittingField F E f]
    [Polynomial.IsSplittingField F Ω f] (φ : E →ₐ[F] Ω) :
    ∃ e : E ≃ₐ[F] Ω, ⇑e = ⇑φ := by
  classical
  haveI hfdE : FiniteDimensional F E := Polynomial.IsSplittingField.finiteDimensional E f
  haveI hfdΩ : FiniteDimensional F Ω := Polynomial.IsSplittingField.finiteDimensional Ω f
  have hinj : Function.Injective ⇑φ := φ.toRingHom.injective
  have hfr : Module.finrank F E = Module.finrank F f.SplittingField :=
    LinearEquiv.finrank_eq (IsSplittingField.algEquiv (L := E) f).toLinearEquiv
  set eΩ : Ω ≃ₐ[F] f.SplittingField := IsSplittingField.algEquiv (L := Ω) f with heΩ
  have hcompL : Function.Injective ⇑((eΩ.toAlgHom.comp φ).toLinearMap) :=
    eΩ.toAlgHom.injective.comp hinj
  have hsurjcomp : Function.Surjective ⇑(eΩ.toAlgHom.comp φ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (eΩ.toAlgHom.comp φ).toLinearMap) hfr).mp hcompL
  refine ⟨AlgEquiv.ofBijective φ ⟨hinj, fun y => ?_⟩, rfl⟩
  obtain ⟨x, hx⟩ := hsurjcomp (eΩ.toAlgHom y)
  exact ⟨x, eΩ.injective hx⟩

/-- FT `sf7` (b), "in particular" clause.  Any two splitting fields for `f` (over `F`) are
`F`-isomorphic: each is `F`-isomorphic to the canonical model splitting field
`Polynomial.SplittingField f` (`IsSplittingField.algEquiv`). -/
theorem exists_algEquiv_of_isSplittingField (f : F[X]) [Polynomial.IsSplittingField F E f]
    [Polynomial.IsSplittingField F Ω f] : Nonempty (E ≃ₐ[F] Ω) :=
  ⟨(show (E ≃ₐ[F] f.SplittingField) from IsSplittingField.algEquiv (L := E) f).trans
    (show (f.SplittingField ≃ₐ[F] Ω) from (IsSplittingField.algEquiv (L := Ω) f).symm)⟩

/-- FT `sf7` (a), counting clause, upper bound; special case where `E` is a splitting field
for `f`. -/
theorem natCard_algHom_le_of_isSplittingField_of_splits (f : F[X])
    [Polynomial.IsSplittingField F E f] (hsplits : (f.map (algebraMap F Ω)).Splits) :
    Nat.card (E →ₐ[F] Ω) ≤ Module.finrank F E :=
  natCard_algHom_le_of_adjoin_rootSet_eq_top_of_splits f
    (Polynomial.IsSplittingField.adjoin_rootSet E f) hsplits

/-- FT `sf7` (a), counting clause, equality; special case where `E` is a splitting field
for `f`. -/
theorem natCard_algHom_eq_of_isSplittingField_of_splits (f : F[X])
    [Polynomial.IsSplittingField F E f] (hsplits : (f.map (algebraMap F Ω)).Splits)
    (hnodup : (f.map (algebraMap F Ω)).roots.Nodup) :
    Nat.card (E →ₐ[F] Ω) = Module.finrank F E :=
  natCard_algHom_eq_of_adjoin_rootSet_eq_top_of_splits f
    (Polynomial.IsSplittingField.adjoin_rootSet E f) hsplits hnodup

end SF7
/-! ### FT `sf8` (corollary: F-homomorphisms from a finite extension) -/

section Sf8Aux

open Polynomial BigOperators

variable {A B C : Type*} [Field A] [Field B] [Field C] [Algebra A B] [Algebra A C]

/-- Auxiliary for FT `sf8` (i): there are only finitely many `A`-algebra homomorphisms out of a
finite-dimensional `A`-algebra domain `B`. -/
theorem finite_algHom_of_finiteDimensional [FiniteDimensional A B] : Finite (B →ₐ[A] C) := by
  classical
  have hint : ∀ x : B, IsIntegral A x := Algebra.IsIntegral.isIntegral
  have key : Finite (∀ i : Module.Free.ChooseBasisIndex A B,
      {y : C // aeval y (minpoly A (Module.Free.chooseBasis A B i)) = 0}) :=
    @Pi.finite _ _ (inferInstance) (fun i =>
      Finite.of_injective (fun y => (⟨y,
        (Polynomial.mem_rootSet' (S := C)).2
          ⟨Polynomial.map_monic_ne_zero (minpoly.monic (hint _)), y.2⟩⟩ :
        {z : C // z ∈ (minpoly A (Module.Free.chooseBasis A B i)).rootSet C}))
        (fun y z h => Subtype.ext (by simpa using h)))
  refine Finite.of_injective (f := fun (φ : B →ₐ[A] C) (i : Module.Free.ChooseBasisIndex A B) =>
      (⟨φ (Module.Free.chooseBasis A B i),
        by rw [Polynomial.aeval_algHom_apply, minpoly.aeval A _, map_zero]⟩ :
        {y : C // aeval y (minpoly A (Module.Free.chooseBasis A B i)) = 0})) ?_
  intro φ₁ φ₂ h
  simp only [] at h
  have hlin : φ₁.toLinearMap = φ₂.toLinearMap :=
    (Module.Free.chooseBasis A B).ext
      (fun i => congrArg Subtype.val (congrFun h i))
  exact AlgHom.ext fun x => DFunLike.congr_fun hlin x

/-- Auxiliary (card of the subtype of elements of a multiset, as a set, is at most its
cardinality). -/
theorem card_multiset_subtype_le {L : Type*} [DecidableEq L] (m : Multiset L) :
    Fintype.card {z : L // z ∈ m} ≤ Multiset.card m := by
  have e : {z : L // z ∈ m} ≃ {w : L // w ∈ m.toFinset} :=
    { toFun := fun z => ⟨z.val, Multiset.mem_toFinset.mpr z.2⟩
      invFun := fun w => ⟨w.val, Multiset.mem_toFinset.mp w.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl }
  calc Fintype.card {z : L // z ∈ m}
      ≤ Fintype.card {w : L // w ∈ m.toFinset} := Fintype.card_le_of_injective _ e.injective
    _ = m.toFinset.card := Fintype.card_coe _
    _ ≤ Multiset.card m := Multiset.toFinset_card_le m

/-- Auxiliary for FT `sf8` (i): homomorphisms out of a simple adjunction are bounded by the
degree of the minimal polynomial (the one-step count of the FT `sf7` argument). -/
theorem card_algHom_adjoin_le {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra F L] {x : K} (hx : IsIntegral F x) :
    Nat.card (↥(IntermediateField.adjoin F {x}) →ₐ[F] L) ≤ (minpoly F x).natDegree := by
  classical
  haveI hfintype : Fintype (↥(IntermediateField.adjoin F {x}) →ₐ[F] L) :=
    IntermediateField.fintypeOfAlgHomAdjoinIntegral F hx
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (IntermediateField.algHomAdjoinIntegralEquiv F hx)]
  refine le_trans (card_multiset_subtype_le _) ?_
  rw [show ((minpoly F x).aroots L) = ((minpoly F x).map (algebraMap F L)).roots from rfl]
  have h1 : ((minpoly F x).map (algebraMap F L)).roots.card
      ≤ ((minpoly F x).map (algebraMap F L)).natDegree := Polynomial.card_roots' _
  rw [Polynomial.natDegree_map (algebraMap F L)] at h1
  exact h1

private theorem sf8_algebraMap_injective_of_field : Function.Injective (algebraMap A B) :=
  fun a b h => by
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero_of_ne hne
    have h0 : algebraMap A B (a - b) = 0 := by rw [map_sub, h, sub_self]
    have h1 : (1 : B) = 0 := by
      have e1 : algebraMap A B ((a - b)⁻¹ * (a - b)) = 1 := by
        rw [inv_mul_cancel₀ hne', map_one]
      rw [← e1, map_mul, h0, mul_zero]
    exact absurd h1 (one_ne_zero)

private theorem finrank_eq_one_of_surjective (hsurj : Function.Surjective (algebraMap A B)) :
    Module.finrank A B = 1 :=
  ((LinearEquiv.ofBijective
      ((IsScalarTower.toAlgHom A A B : A →ₐ[A] B).toLinearMap)
      ⟨sf8_algebraMap_injective_of_field, hsurj⟩).symm.finrank_eq).trans (Module.finrank_self A)

private theorem subsingleton_algHom_of_surjective (hsurj : Function.Surjective (algebraMap A B)) :
    Subsingleton (B →ₐ[A] C) :=
  ⟨fun f g => AlgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hsurj b
    rw [f.commutes a, g.commutes a]⟩

private theorem finiteDimensional_of_tower (I : IntermediateField A B) [FiniteDimensional A B] :
    FiniteDimensional ↥I B := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A B).fg_top
  refine ⟨?_⟩
  refine ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hle : (Submodule.span ↥I (↑s : Set B)).restrictScalars A = ⊤ := by
    apply top_le_iff.mp
    rw [← hs]
    exact Submodule.span_le.mpr fun x hx =>
      (Submodule.restrictScalars_mem A _ x).mpr (Submodule.subset_span hx)
  exact (Submodule.restrictScalars_mem A _ x).mp (by rw [hle]; exact Submodule.mem_top)

/-- Auxiliary for FT `sf8` (i): if `y : B` is outside the copy of `A` and each homomorphism
`A⟮y⟯ →ₐ[A] C` has at most `[B : A⟮y⟯]` extensions to `B`, then the total number of
homomorphisms `B →ₐ[A] C` is at most `[B : A]`. -/
theorem count_of_fiber_bound (y : B) (hyint : IsIntegral A y)
    (hyout : y ∉ Set.range (algebraMap A B))
    (hbound : ∀ (_ : ↥(IntermediateField.adjoin A {y}) →ₐ[A] C)
        (_ : Algebra ↥(IntermediateField.adjoin A {y}) C)
        (_ : IsScalarTower A ↥(IntermediateField.adjoin A {y}) C),
        Nat.card (B →ₐ[↥(IntermediateField.adjoin A {y})] C)
          ≤ Module.finrank ↥(IntermediateField.adjoin A {y}) B)
    [FiniteDimensional A B] [DecidableEq C] :
    Nat.card (B →ₐ[A] C) ≤ Module.finrank A B := by
  classical
  set I : IntermediateField A B := IntermediateField.adjoin A {y} with hIdef
  have hdeg : Module.finrank A ↥I = (minpoly A y).natDegree := by
    rw [← IntermediateField.adjoin.powerBasis_dim hyint]
    exact (IntermediateField.adjoin.powerBasis hyint).finrank
  have hn1 : 2 ≤ (minpoly A y).natDegree := by
    have hne1 : (minpoly A y).natDegree ≠ 1 := by
      intro h1
      have hmonic : (minpoly A y).Monic := minpoly.monic hyint
      obtain ⟨a, b, hexp⟩ :=
        Polynomial.exists_eq_X_add_C_of_natDegree_le_one h1.le
      have hae : aeval y (minpoly A y) = 0 := minpoly.aeval A y
      rw [hexp, aeval_add, aeval_mul, aeval_C, aeval_X, aeval_C] at hae
      have hd1 : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 := by
        rw [← hexp]; exact h1
      have ha1 : a = 1 := by
        have hlc := hmonic.leadingCoeff
        rw [hexp, ← Polynomial.coeff_natDegree, hd1] at hlc
        simpa using hlc
      rw [ha1, map_one, one_mul] at hae
      refine hyout ⟨-b, ?_⟩
      rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]
      exact hae
    have hpos' : 0 < (minpoly A y).natDegree := by
      rw [Polynomial.natDegree_pos_iff_degree_pos]
      exact minpoly.degree_pos hyint
    omega
  have htw : (minpoly A y).natDegree * Module.finrank ↥I B = Module.finrank A B := by
    rw [← hdeg]
    exact Module.finrank_mul_finrank A ↥I B
  have hn2 : 0 < Module.finrank ↥I B :=
    (Module.finrank_pos_iff_of_free ↥I B).mpr inferInstance
  haveI hfinX : Finite (B →ₐ[A] C) := finite_algHom_of_finiteDimensional
  haveI : Fintype (B →ₐ[A] C) := Fintype.ofFinite _
  haveI hfinI : Fintype (↥I →ₐ[A] C) :=
    IntermediateField.fintypeOfAlgHomAdjoinIntegral A hyint
  have hfib : ∀ ψ₀ : ↥I →ₐ[A] C,
      Fintype.card {φ : B →ₐ[A] C // φ.comp (IsScalarTower.toAlgHom A ↥I B) = ψ₀}
        ≤ Module.finrank ↥I B := by
    intro ψ₀
    letI instAC : Algebra ↥I C := RingHom.toAlgebra ψ₀.toRingHom
    haveI instST : IsScalarTower A ↥I C :=
      IsScalarTower.of_algebraMap_eq fun a => (ψ₀.commutes a).symm
    have e : {φ : B →ₐ[A] C // φ.comp (IsScalarTower.toAlgHom A ↥I B) = ψ₀} ≃ (B →ₐ[↥I] C) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨φ, hφ⟩
        exact AlgHom.mk φ.toRingHom (fun x => congrArg (fun ψ => ψ x) hφ)
      · intro χ
        refine ⟨AlgHom.mk χ.toRingHom (fun a => by
          show χ (algebraMap A B a) = algebraMap A C a
          rw [IsScalarTower.algebraMap_apply A ↥I B, χ.commutes]
          exact ψ₀.commutes a), ?_⟩
        refine AlgHom.ext fun x => ?_
        show (χ (IsScalarTower.toAlgHom A ↥I B x)) = ψ₀ x
        rw [IsScalarTower.toAlgHom_apply, χ.commutes]
        rfl
      · rintro ⟨φ, hφ⟩
        exact Subtype.ext (AlgHom.ext fun x => rfl)
      · intro χ
        exact AlgHom.ext fun x => rfl
    haveI hfdIB : FiniteDimensional ↥I B := finiteDimensional_of_tower I
    haveI hfin : Finite (B →ₐ[↥I] C) := finite_algHom_of_finiteDimensional
    rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
    exact hbound ψ₀ instAC instST
  set ρ : (B →ₐ[A] C) → (↥I →ₐ[A] C) :=
    fun φ => φ.comp (IsScalarTower.toAlgHom A ↥I B) with hrho
  have eSig : (B →ₐ[A] C) ≃ (Σ ψ₀ : ↥I →ₐ[A] C, {φ : B →ₐ[A] C // ρ φ = ψ₀}) := by
    refine ⟨fun φ => ⟨ρ φ, ⟨φ, rfl⟩⟩, fun p => p.2, fun φ => rfl, ?_⟩
    rintro ⟨ψ₀, p⟩
    obtain ⟨φ, hφ⟩ := p
    subst hφ
    exact congrArg (Sigma.mk (ρ φ)) (Subtype.ext rfl).symm
  calc Nat.card (B →ₐ[A] C)
    = Fintype.card (B →ₐ[A] C) := Nat.card_eq_fintype_card
  _ = Fintype.card (Σ ψ₀ : ↥I →ₐ[A] C, {φ : B →ₐ[A] C // ρ φ = ψ₀}) :=
      Fintype.card_congr eSig
  _ = ∑ ψ₀ ∈ Finset.univ, Fintype.card {φ : B →ₐ[A] C // ρ φ = ψ₀} :=
      Fintype.card_sigma
  _ ≤ Finset.univ.card • Module.finrank ↥I B :=
      Finset.sum_le_card_nsmul _ _ _ (fun ψ₀ _ => hfib ψ₀)
  _ = Fintype.card (↥I →ₐ[A] C) * Module.finrank ↥I B := by
      simp [Finset.card_univ]
  _ ≤ (minpoly A y).natDegree * Module.finrank ↥I B := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.mul_le_mul_right _ (card_algHom_adjoin_le hyint)
  _ = Module.finrank A B := htw

universe u v

/-- **FT `sf8` (i), core**: the number of `A`-algebra homomorphisms from a finite-dimensional
field extension `B / A` into any field `C` is at most `[B : A]`. -/
theorem natCard_algHom_le_finrank : ∀ n : ℕ, ∀ (A B : Type u) (C : Type v) [Field A] [Field B]
    [Field C] [Algebra A B] [Algebra A C] [FiniteDimensional A B], Module.finrank A B = n →
    Nat.card (B →ₐ[A] C) ≤ n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B C _ _ _ _ _ _ hrank
    by_cases hsurj : Function.Surjective (algebraMap A B)
    · haveI hfinX : Finite (B →ₐ[A] C) := finite_algHom_of_finiteDimensional
      haveI : Fintype (B →ₐ[A] C) := Fintype.ofFinite _
      rw [← hrank, finrank_eq_one_of_surjective hsurj,
        Finite.card_le_one_iff_subsingleton]
      exact subsingleton_algHom_of_surjective hsurj
    · have hy : ∃ y : B, y ∉ Set.range (algebraMap A B) := by
        by_contra hc
        refine hsurj fun b => ?_
        by_contra hb
        exact hc ⟨b, hb⟩
      obtain ⟨y, hyout⟩ := hy
      have hyint : IsIntegral A y := Algebra.IsIntegral.isIntegral y
      have hdeg : Module.finrank A ↥(IntermediateField.adjoin A {y})
          = (minpoly A y).natDegree := by
        rw [← IntermediateField.adjoin.powerBasis_dim hyint]
        exact (IntermediateField.adjoin.powerBasis hyint).finrank
      have hn2 : 0 < Module.finrank ↥(IntermediateField.adjoin A {y}) B :=
        (Module.finrank_pos_iff_of_free
          ↥(IntermediateField.adjoin A {y}) B).mpr inferInstance
      have htw : (minpoly A y).natDegree *
          Module.finrank ↥(IntermediateField.adjoin A {y}) B = Module.finrank A B := by
        rw [← hdeg]
        exact Module.finrank_mul_finrank A ↥(IntermediateField.adjoin A {y}) B
      have hn2lt : Module.finrank ↥(IntermediateField.adjoin A {y}) B < n := by
        rw [← hrank, ← htw]
        calc Module.finrank ↥(IntermediateField.adjoin A {y}) B
            < 2 * Module.finrank ↥(IntermediateField.adjoin A {y}) B := by
              rw [two_mul]; omega
          _ ≤ (minpoly A y).natDegree *
              Module.finrank ↥(IntermediateField.adjoin A {y}) B :=
              Nat.mul_le_mul_right _ (by
                have hpos' : 0 < (minpoly A y).natDegree := by
                  rw [Polynomial.natDegree_pos_iff_degree_pos]
                  exact minpoly.degree_pos hyint
                have hne1 : (minpoly A y).natDegree ≠ 1 := by
                  intro h1
                  have hmonic : (minpoly A y).Monic := minpoly.monic hyint
                  obtain ⟨a, b, hexp⟩ :=
                    Polynomial.exists_eq_X_add_C_of_natDegree_le_one h1.le
                  have hae : aeval y (minpoly A y) = 0 := minpoly.aeval A y
                  rw [hexp, aeval_add, aeval_mul, aeval_C, aeval_X, aeval_C] at hae
                  have hd1 :
                      (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 := by
                    rw [← hexp]; exact h1
                  have ha1 : a = 1 := by
                    have hlc := hmonic.leadingCoeff
                    rw [hexp, ← Polynomial.coeff_natDegree, hd1] at hlc
                    simpa using hlc
                  rw [ha1, map_one, one_mul] at hae
                  refine hyout ⟨-b, ?_⟩
                  rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]
                  exact hae
                omega)
      rw [← hrank]
      refine count_of_fiber_bound y hyint hyout (C := C) ?_
      intro ψ₀ instAC instST
      haveI := finiteDimensional_of_tower (IntermediateField.adjoin A {y})
      exact ih (Module.finrank ↥(IntermediateField.adjoin A {y}) B) hn2lt
        ↥(IntermediateField.adjoin A {y}) B C rfl

end Sf8Aux

section Sf8

open Polynomial BigOperators

variable {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]

/-- **FT `sf8` (i)**: if `E` is finite over `F`, then the number of `F`-algebra homomorphisms
`E → L` is at most `[E : F]`. -/
theorem sf8_natCard_algHom_le [FiniteDimensional F E] :
    Nat.card (E →ₐ[F] L) ≤ Module.finrank F E := by
  classical
  by_cases hsurj : Function.Surjective (algebraMap F E)
  · haveI hfinX : Finite (E →ₐ[F] L) := finite_algHom_of_finiteDimensional
    haveI : Fintype (E →ₐ[F] L) := Fintype.ofFinite _
    rw [finrank_eq_one_of_surjective hsurj, Finite.card_le_one_iff_subsingleton]
    exact subsingleton_algHom_of_surjective hsurj
  · obtain ⟨y, hyout⟩ : ∃ y : E, y ∉ Set.range (algebraMap F E) := by
      by_contra hc
      refine hsurj fun b => ?_
      by_contra hb
      exact hc ⟨b, hb⟩
    have hyint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
    refine count_of_fiber_bound y hyint hyout (C := L) ?_
    intro ψ₀ instAC instST
    haveI := finiteDimensional_of_tower (IntermediateField.adjoin F {y})
    exact natCard_algHom_le_finrank (Module.finrank ↥(IntermediateField.adjoin F {y}) E)
      ↥(IntermediateField.adjoin F {y}) E L rfl

set_option maxHeartbeats 1000000 in
/-- Helper for FT `sf8` (ii): each `minpoly F x` splits over the splitting field over `L` of
`f.map (algebraMap F L)`. -/
theorem sf8_minpoly_splits (s : Finset E) (f : F[X]) (hfmon : f.Monic)
    (hfdvd : ∀ x ∈ s, minpoly F x ∣ f) (x : E) (hx : x ∈ s) :
    ((minpoly F x).map
      (algebraMap F (Polynomial.SplittingField (f.map (algebraMap F L))))).Splits := by
  have hqmon : (f.map (algebraMap F L)).Monic := Monic.map (algebraMap F L) hfmon
  have hdvd : minpoly F x ∣ f := hfdvd x hx
  have hsplit0 : ((f.map (algebraMap F L)).map
      (algebraMap L (Polynomial.SplittingField (f.map (algebraMap F L))))).Splits :=
    Polynomial.IsSplittingField.splits
      (Polynomial.SplittingField (f.map (algebraMap F L))) (f.map (algebraMap F L))
  have hne : (f.map (algebraMap F L)).map
      (algebraMap L (Polynomial.SplittingField (f.map (algebraMap F L)))) ≠ 0 :=
    map_monic_ne_zero hqmon
  have hdvd' : ((minpoly F x).map (algebraMap F L)).map
      (algebraMap L (Polynomial.SplittingField (f.map (algebraMap F L)))) ∣
      (f.map (algebraMap F L)).map
      (algebraMap L (Polynomial.SplittingField (f.map (algebraMap F L)))) :=
    Polynomial.map_dvd _ (Polynomial.map_dvd (algebraMap F L) hdvd)
  rw [IsScalarTower.algebraMap_eq F L (Polynomial.SplittingField (f.map (algebraMap F L))),
    ← map_map]
  exact Polynomial.Splits.of_dvd hsplit0 hne hdvd'

/-- Transport for FT `sf8` (ii): an `F`-algebra homomorphism out of `↥(Algebra.adjoin F ↑s)`
extends to an `F`-algebra homomorphism out of `E` when `E = Algebra.adjoin F ↑s`. -/
theorem sf8_hom_of_adjoin_eq_top (s : Finset E)
    (htop : Algebra.adjoin F (s : Set E) = ⊤) (Ω : Type (max u_1 u_2 u_3)) [Field Ω]
    [Algebra F Ω]
    (h : Nonempty (↥(Algebra.adjoin F (s : Set E)) →ₐ[F] Ω)) : Nonempty (E →ₐ[F] Ω) := by
  rw [htop] at h
  exact h.map fun φ => φ.comp ((Subalgebra.topEquiv (R := F) (A := E)).symm.toAlgHom)

end Sf8
section Sf8ii

open Polynomial BigOperators

variable {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]

set_option maxHeartbeats 1000000 in
/-- **FT `sf8` (ii)**: if `E` is finite over `F`, there exist a field `Ω`, algebra structures of
`L` and of `F` on `Ω` (with `F → L → Ω` the structure map, i.e. `Ω` is an `L`-extension with the
`F`-structure induced by `algebraMap F L`), such that `Ω` is finite-dimensional over `L` and
there exists an `F`-homomorphism `E → Ω`.

Proof idea (FT): `E = F[α₁, …, α_m]` with the `αᵢ` the images of a basis (all integral over `F`);
let `f = ∏ minpoly F αᵢ ∈ F[X]` and `Ω = SplittingField (f.map (algebraMap F L))`.  Then `Ω` is
finite over `L` (a splitting field), each `minpoly F αᵢ` splits in `Ω` (it divides `f`), so
`Polynomial.lift_of_splits` gives an `F`-homomorphism out of `F[α₁, …, α_m] = E` into `Ω`
(transported out of the adjoin by `FT.sf8_hom_of_adjoin_eq_top`).  The instance fields are
supplied by hand (concrete `Ω` first, so instance synthesis never runs on a metavariable). -/
theorem sf8_ii {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra L Ω) (_ : Algebra F Ω)
        (_ : IsScalarTower F L Ω), FiniteDimensional L Ω ∧ Nonempty (E →ₐ[F] Ω) := by
  classical
  have hint : ∀ x : E, IsIntegral F x := Algebra.IsIntegral.isIntegral
  have htop : Algebra.adjoin F (Set.range (Module.Free.chooseBasis F E)) = ⊤ := by
    have h1 : (⊤ : Submodule F E) ≤
        (Algebra.adjoin F (Set.range (Module.Free.chooseBasis F E))).toSubmodule := by
      rw [← (Module.Free.chooseBasis F E).span_eq]
      exact Submodule.span_le.mpr fun x hx => Algebra.subset_adjoin hx
    exact eq_top_iff.2 fun x _ => h1 (Submodule.mem_top)
  have htop' : Algebra.adjoin F
      ((Set.range (Module.Free.chooseBasis F E)).toFinset : Set E) = ⊤ := by
    rw [Set.coe_toFinset]
    exact htop
  set f : F[X] := ∏ x ∈ (Set.range (Module.Free.chooseBasis F E)).toFinset, minpoly F x with hf
  refine ⟨Polynomial.SplittingField (f.map (algebraMap F L)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · exact Polynomial.IsSplittingField.finiteDimensional
      (Polynomial.SplittingField (f.map (algebraMap F L))) (f.map (algebraMap F L))
  · refine sf8_hom_of_adjoin_eq_top _ htop'
      (Polynomial.SplittingField (f.map (algebraMap F L)))
      (Polynomial.lift_of_splits
        (Set.range (Module.Free.chooseBasis F E)).toFinset ?_)
    intro x hx
    refine ⟨hint x, sf8_minpoly_splits
      (Set.range (Module.Free.chooseBasis F E)).toFinset f ?_
      (fun x hx => Finset.dvd_prod_of_mem _ hx) x hx⟩
    exact Polynomial.monic_prod_of_monic _ (fun x => minpoly F x)
      (fun x _ => minpoly.monic (hint x))

end Sf8ii
