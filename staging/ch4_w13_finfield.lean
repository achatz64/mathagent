-- STAGING: FT ch. IV §6 finite fields (cg15/cg16/cg17/cg18/cg18m/cg18n), re-derivation
-- worker w13 deliverable, received verbatim. All declarations axiom-checked
-- [propext, Classical.choice, Quot.sound]. Name-mapping caveat: cg16/cg17 clean proofs
-- re-verified under session names cg16Final/cg17Final (identical statements/proofs);
-- integration build confirms under final names.
-- Needs imports beyond the current Target block:
--   Mathlib.FieldTheory.Finite.Basic, Mathlib.FieldTheory.Finite.GaloisField,
--   Mathlib.FieldTheory.PrimitiveElement, Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure,
--   Mathlib.Algebra.Ring.GeomSum (and CharP.Lemmas transitively).
-- Overlap note: FT.cg15_gal_eq_zpowers_frobenius (ZMod p setting) coexists with
-- FT.cg19F_gal_eq_zpowers_frobenius (general finite fields); interderivable, kept both.
-- Paste inside namespace FT.

open Polynomial

/-!
## Finite fields (FT chapter IV §6, FT.tex 4064–4200)

Small-power lemmas in characteristic `p` (Block A), the subfield of roots of
`X ^ (p ^ n) - X`, and the labels `cg15`, `cg16`, `cg17`, `cg18`, `cg18m`, `cg18n`.
-/

section ExpCharPowers

variable {K : Type*} [Field K] {p : ℕ} [ExpChar K p]

/-- FT ch. IV §6 (Block A): in exponential characteristic `p` one has `(-1) ^ (p ^ n) = -1`.
When `p = 2` this reads `(-1) ^ (p ^ n) = 1`, since `-1 = 1` in characteristic two. -/
theorem neg_one_pow_expChar_pow (n : ℕ) : (-1 : K) ^ p ^ n = -1 :=
  _root_.neg_one_pow_expChar_pow K p n

/-- FT ch. IV §6 (Block A): Frobenius powers are compatible with negation:
`(-a) ^ (p ^ n) = -(a ^ (p ^ n))`. -/
theorem pow_expChar_pow_neg (n : ℕ) (a : K) : (-a) ^ p ^ n = -(a ^ p ^ n) := by
  rw [← neg_one_mul, mul_pow, neg_one_pow_expChar_pow, neg_one_mul]

/-- FT ch. IV §6: Frobenius powers respect subtraction, `(a - b) ^ (p ^ n) = a ^ (p ^ n) -
b ^ (p ^ n)`; this is the identity used to show that the roots of `X ^ (p ^ n) - X` are closed
under subtraction. -/
theorem sub_pow_expChar_pow (n : ℕ) (a b : K) :
    (a - b) ^ p ^ n = a ^ p ^ n - b ^ p ^ n :=
  sub_pow_expChar_pow_of_commute p n (Commute.all a b)

/-- FT ch. IV §6 (Block A): in a field with `p ^ n` elements, every element is a root of
`X ^ (p ^ n) - X`. -/
theorem pow_pow_eq_self {K : Type*} [Field K] [Fintype K] {p : ℕ} [ExpChar K p] {n : ℕ}
    (hcard : Fintype.card K = p ^ n) (x : K) : x ^ p ^ n = x := by
  rw [← hcard]
  simpa using FiniteField.pow_card_pow 1 x

end ExpCharPowers

/-- FT ch. IV §6: if `m ∣ n` then every root of `X ^ (p ^ m) - X` is a root of
`X ^ (p ^ n) - X`. -/
theorem pow_pow_eq_self_of_dvd {K : Type*} [Field K] {p : ℕ} {m n : ℕ} (h : m ∣ n) {x : K}
    (hx : x ^ p ^ m = x) : x ^ p ^ n = x := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => rw [Nat.mul_zero, pow_zero, pow_one]
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]

section RootsSubfield

variable {K : Type*} [Field K] {p : ℕ} [ExpChar K p]

/-- FT ch. IV §6 (before `cg15`): the set of roots of `X ^ (p ^ n) - X` in a field of
exponential characteristic `p` is a subfield: it is closed under multiplication and inverses
because Frobenius powers are multiplicative, and under addition/subtraction/negation because
Frobenius powers are additive (`(a - b) ^ (p ^ n) = a ^ (p ^ n) - b ^ (p ^ n)`). -/
def rootsSubfield (hp : p.Prime) (n : ℕ) : Subfield K where
  carrier := {x : K | x ^ p ^ n = x}
  mul_mem' ha hb := by
    dsimp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]
  one_mem' := one_pow (p ^ n)
  add_mem' ha hb := by
    dsimp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_pow_expChar_pow, ha, hb]
  zero_mem' := by
    dsimp only [Set.mem_setOf_eq]
    rw [zero_pow (pow_pos hp.pos n).ne']
  neg_mem' ha := by
    dsimp only [Set.mem_setOf_eq] at ha ⊢
    rw [pow_expChar_pow_neg n, ha]
  inv_mem' x ha := by
    dsimp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha]

/-- Membership in `FT.rootsSubfield` is being a root of `X ^ (p ^ n) - X`. -/
theorem mem_rootsSubfield {x : K} (hp : p.Prime) {n : ℕ} :
    x ∈ rootsSubfield hp n ↔ x ^ p ^ n = x := Iff.rfl

/-- FT ch. IV §6: an element of a subfield with `p ^ n` elements is a root of
`X ^ (p ^ n) - X`. -/
theorem pow_pow_eq_self_of_card (hp : p.Prime) {n : ℕ} {S : Subfield K}
    (hS : Nat.card ↥S = p ^ n) {x : K} (hx : x ∈ S) : x ^ p ^ n = x := by
  have hpos : 0 < Nat.card ↥S := by rw [hS]; exact pow_pos hp.pos n
  haveI : Finite ↥S := (Nat.card_pos_iff.mp hpos).2
  haveI : Fintype ↥S := Fintype.ofFinite ↥S
  have hcard : Fintype.card ↥S = p ^ n := by rw [← hS, Nat.card_eq_fintype_card]
  have h : (⟨x, hx⟩ : S) ^ Fintype.card ↥S ^ 1 = (⟨x, hx⟩ : S) :=
    FiniteField.pow_card_pow 1 (⟨x, hx⟩ : S)
  rw [pow_one] at h
  have h2 := congrArg (Subfield.subtype S) h
  rw [map_pow] at h2
  rw [hcard] at h2
  exact h2

/-- Roots of `X ^ (p ^ n) - X` are fixed points of the `n`-th Frobenius power. -/
theorem aeval_rootsSubfield_iff {x : K} {n : ℕ} (hne : (X ^ p ^ n - X : K[X]) ≠ 0) :
    x ∈ (X ^ p ^ n - X : K[X]).rootSet K ↔ x ^ p ^ n = x := by
  rw [mem_rootSet_of_ne hne, aeval_sub, aeval_X_pow, aeval_X, sub_eq_zero]

/-- FT ch. IV §6: if `X ^ (p ^ n) - X` splits in `K` (e.g. if `K` is a field with `p ^ n`
elements, or an algebraic closure of `𝔽_p`), the set of its roots -- the carrier of
`FT.rootsSubfield hp n` -- has exactly `p ^ n` elements. -/
theorem natCard_rootsSubfield [CharP K p] (hp : p.Prime) {n : ℕ} (hn : n ≠ 0)
    (hsplit : Splits (X ^ p ^ n - X : K[X])) : Nat.card {x : K // x ^ p ^ n = x} = p ^ n := by
  have hnd : (X ^ p ^ n - X : K[X]).natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn hp.one_lt
  have hne : (X ^ p ^ n - X : K[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hnd
    exact pow_ne_zero n hp.ne_zero hnd.symm
  have hmap : map (algebraMap K K) (X ^ p ^ n - X) = (X ^ p ^ n - X : K[X]) := by simp
  have hsplit' : Splits (map (algebraMap K K) (X ^ p ^ n - X)) := by rw [hmap]; exact hsplit
  have he : {x : K // x ^ p ^ n = x} ≃
      {x : K // x ∈ ((X ^ p ^ n - X : K[X]).rootSet K : Set K)} :=
    Equiv.subtypeEquivRight fun x => (aeval_rootsSubfield_iff hne).symm
  have h1 : Nat.card {x : K // x ^ p ^ n = x} =
      Nat.card ↥((X ^ p ^ n - X : K[X]).rootSet K) := Nat.card_congr he
  rw [h1, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree (galois_poly_separable p (p ^ n) (dvd_pow_self p hn)) hsplit']
  exact hnd

/-- FT ch. IV §6 (`cg16`, `cg18m`): a subfield with `p ^ n` elements is exactly the subfield
of roots of `X ^ (p ^ n) - X`; in particular such a subfield is unique. -/
theorem eq_rootsSubfield_of_card_eq [CharP K p] (hp : p.Prime) {n : ℕ} (hn : n ≠ 0)
    {S : Subfield K} (hS : Nat.card ↥S = p ^ n)
    (hsplit : Splits (X ^ p ^ n - X : K[X])) : S = rootsSubfield hp n := by
  haveI : ExpChar K p := ExpChar.prime hp
  have hcardR : Nat.card {x : K // x ^ p ^ n = x} = p ^ n := natCard_rootsSubfield hp hn hsplit
  have hsub : (S : Set K) ⊆ {x : K | x ^ p ^ n = x} := fun x hx =>
    (mem_rootsSubfield hp).2 (pow_pow_eq_self_of_card hp hS hx)
  have hc : Nat.card {x : K // x ^ p ^ n = x} ≤ Nat.card ↥S := by rw [hcardR, hS]
  have hfinT : ({x : K | x ^ p ^ n = x} : Set K).Finite := by
    have hnd : (X ^ p ^ n - X : K[X]).natDegree = p ^ n :=
      FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn hp.one_lt
    have hne : (X ^ p ^ n - X : K[X]) ≠ 0 := by
      intro h; rw [h, natDegree_zero] at hnd; exact pow_ne_zero n hp.ne_zero hnd.symm
    have hset : {x : K | x ^ p ^ n = x} = (X ^ p ^ n - X : K[X]).rootSet K := by
      ext x; rw [Set.mem_setOf_eq, aeval_rootsSubfield_iff hne]
    rw [hset]
    exact Polynomial.rootSet_finite _ _
  have he : (S : Set K) = {x : K | x ^ p ^ n = x} :=
    Set.Finite.eq_of_subset_of_card_le hfinT hsub hc
  refine Subfield.ext fun x => ?_
  constructor
  · intro hx
    exact (mem_rootsSubfield hp).2 (pow_pow_eq_self_of_card hp hS hx)
  · intro hx
    have hx' : x ∈ {x : K | x ^ p ^ n = x} := (mem_rootsSubfield hp).1 hx
    show x ∈ (S : Set K)
    rw [he]
    exact hx'

/-- FT `cg16`: a field with `p ^ n` elements contains, for each divisor `m` of `n`, exactly one
subfield with `p ^ m` elements, namely the subfield of roots of `X ^ (p ^ m) - X`. -/
theorem cg16 (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Fintype E] [Algebra (ZMod p) E]
    {n m : ℕ} (hcard : Fintype.card E = p ^ n) (hm : m ∣ n) (hm0 : m ≠ 0) :
    ∃! S : Subfield E, Nat.card ↥S = p ^ m := by
  have hp : p.Prime := Fact.out
  haveI : CharP E p := (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  haveI : ExpChar E p := ExpChar.prime hp
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hcard
    exact Fintype.one_lt_card.ne hcard.symm
  have hsplN : Splits (X ^ p ^ n - X : E[X]) := by
    rw [← hcard, ← Nat.card_eq_fintype_card]
    exact splits_X_pow_nat_card_sub_X
  have hsplM : Splits (X ^ p ^ m - X : E[X]) := by
    have hnd : (X ^ p ^ n - X : E[X]).natDegree = p ^ n :=
      FiniteField.X_pow_card_pow_sub_X_natDegree_eq E hn0 hp.one_lt
    refine Splits.of_dvd hsplN ?_ (dvd_pow_pow_sub_self_of_dvd hm)
    intro h
    rw [h, natDegree_zero] at hnd
    exact pow_ne_zero n hp.ne_zero hnd.symm
  refine ⟨rootsSubfield hp m, ?_, fun S hS => eq_rootsSubfield_of_card_eq hp hm0 hS hsplM⟩
  exact natCard_rootsSubfield hp hm0 hsplM

end RootsSubfield

/-- FT `cg15` (existence clause): for every prime `p` and every `n ≥ 1` there exists a field
with `p ^ n` elements, namely the splitting field `GaloisField p n` of `X ^ (p ^ n) - X` over
`𝔽_p`. -/
theorem cg15_exists (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    ∃ K : Type, Nonempty (Field K) ∧ Nat.card K = p ^ n :=
  ⟨GaloisField p n, ⟨inferInstance⟩, GaloisField.card p n hn⟩

/-- FT `cg15` (splitting-field clause): the splitting field of `X ^ (p ^ n) - X` over `𝔽_p`
has exactly `p ^ n` elements. -/
theorem cg15_card_splittingField (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (SplittingField (X ^ p ^ n - X : (ZMod p)[X])) = p ^ n :=
  GaloisField.card p n hn

/-- FT `cg15` (splitting-field clause): every field with `p ^ n` elements is a splitting field
for `X ^ (p ^ n) - X` over `𝔽_p`. -/
theorem cg15_isSplittingField (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [Algebra (ZMod p) E] {n : ℕ} (hcard : Fintype.card E = p ^ n) :
    IsSplittingField (ZMod p) E (X ^ p ^ n - X) :=
  FiniteField.isSplittingField_of_card_eq p n hcard

/-- FT `cg15` (uniqueness clause): any two fields with the same number of elements are
isomorphic as `𝔽_p`-algebras. -/
theorem cg15_algEquivOfCardEq (p : ℕ) [Fact p.Prime] {E E' : Type*} [Field E] [Field E']
    [Fintype E] [Fintype E'] [Algebra (ZMod p) E] [Algebra (ZMod p) E']
    (h : Fintype.card E = Fintype.card E') : Nonempty (E ≃ₐ[ZMod p] E') :=
  ⟨FiniteField.algEquivOfCardEq p h⟩

/-- FT `cg15` (Galois clause): for a field `E` with `p ^ n` elements the Galois group
`Gal(E / 𝔽_p)` is generated by the Frobenius automorphism `x ↦ x ^ p`; in particular
`Gal(E / 𝔽_p)` is cyclic. -/
theorem cg15_gal_eq_zpowers_frobenius (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [Algebra (ZMod p) E] :
    Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) E) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) E).2 g
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨(i.1 : ℤ), by simpa using hi⟩

/-- FT (Block A, `FrobeniusFixedField` section): in a `𝔽_p`-algebra `E`, an element fixed by
the Frobenius `x ↦ x ^ p` lies in the base field `𝔽_p` (the image of `ZMod p` in `E`). -/
theorem mem_bot_of_pow_expChar (p : ℕ) [hp : Fact p.Prime] {E : Type*} [Field E]
    [Algebra (ZMod p) E] (x : E) (hx : x ^ p = x) : x ∈ (⊥ : IntermediateField (ZMod p) E) := by
  have hsplit : Splits (X ^ p - X : (ZMod p)[X]) := GaloisField.splits_zmod_X_pow_sub_X p
  have hnd : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt
  have hne : (X ^ p - X : (ZMod p)[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hnd
    exact hp.out.ne_zero hnd.symm
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = (Finset.univ : Finset (ZMod p)).val := by
    have h1 : (X ^ p - X : (ZMod p)[X]) = (X ^ Fintype.card (ZMod p) - X) := by
      rw [ZMod.card p]
    rw [h1]
    exact FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hxroot : x ∈ (X ^ p - X : (ZMod p)[X]).aroots E := by
    rw [mem_aroots]
    exact ⟨hne, by rw [aeval_sub, aeval_X_pow, aeval_X, hx, sub_self]⟩
  have h2 : (X ^ p - X : (ZMod p)[X]).aroots E =
      (Finset.univ : Finset (ZMod p)).val.map (algebraMap (ZMod p) E) := by
    rw [aroots_def, Splits.roots_map hsplit, hroots]
  rw [h2] at hxroot
  rw [Multiset.mem_map] at hxroot
  obtain ⟨a, -, ha⟩ := hxroot
  rw [IntermediateField.mem_bot]
  exact ⟨a, ha⟩

/-- FT (Block A, `FrobeniusFixedField` section): the fixed field of the Frobenius automorphism
`x ↦ x ^ p` of a field `E` with `p ^ n` elements is the base field `𝔽_p`. -/
theorem frobeniusFixedField_eq_bot (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [Algebra (ZMod p) E] :
    IntermediateField.fixedField
        (Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) E)) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hfix : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) E x = x :=
    hx _ (Subgroup.mem_zpowers _)
  have hcoe : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) E) x =
      x ^ Fintype.card (ZMod p) := rfl
  rw [hcoe] at hfix
  rw [ZMod.card p] at hfix
  exact mem_bot_of_pow_expChar p x hfix

/-- FT `cg17`: every extension `E / F` with `E` finite is simple, i.e. `E = F[ζ]` for some
`ζ ∈ E` (indeed `Eˣ` is cyclic and a generator of `Eˣ` generates `E` over `F`). -/
theorem cg17 (K E : Type*) [Field K] [Field E] [Algebra K E] [Finite E] :
    ∃ α : E, IntermediateField.adjoin K {α} = ⊤ :=
  Field.exists_primitive_element_of_finite_top K E

/-- FT ch. IV §6 (`cg18m`): if `2 ≤ p` and `p ^ m - 1 ∣ p ^ n - 1`, then `m ∣ n`. -/
theorem nat_pow_sub_one_dvd_of_dvd (p : ℕ) (hp : 2 ≤ p) (m n : ℕ)
    (h : p ^ m - 1 ∣ p ^ n - 1) : m ∣ n := by
  have hp1 : 0 < p := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact dvd_zero m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨c, hc⟩ := h
    rw [Nat.pow_zero, Nat.sub_self, Nat.zero_mul] at hc
    exfalso
    have hle : p ^ n ≤ 1 := Nat.sub_eq_zero_iff_le.mp hc
    have hpeq : p ^ n = 1 := Nat.le_antisymm hle (Nat.one_le_pow n p hp1)
    have h1 : 1 < p ^ n := Nat.one_lt_pow (ne_of_gt hn0) hp
    rw [hpeq] at h1
    exact absurd h1 (Nat.lt_irrefl 1)
  · set q := n / m with hq
    set r := n % m with hr
    have hdm : m * q + r = n := Nat.div_add_mod n m
    have hrlt : r < m := Nat.mod_lt _ hm
    have hd1 : (p ^ m) ^ 1 - 1 ∣ (p ^ m) ^ q - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one (p ^ m) (one_dvd q)
    rw [pow_one] at hd1
    obtain ⟨s, hs⟩ := hd1
    have hle1 : 1 ≤ (p ^ m) ^ q := Nat.one_le_pow q (p ^ m) (Nat.one_le_pow m p hp1)
    have e1 : (p ^ m) ^ q = (p ^ m - 1) * s + 1 := Nat.eq_add_of_sub_eq hle1 hs
    have hpn2 : p ^ n = p ^ r + (p ^ m - 1) * (s * p ^ r) := by
      have e0 : p ^ n = (p ^ m) ^ q * p ^ r := by rw [← hdm, pow_add, pow_mul]
      rw [e0, e1]; ring
    have hpr1 : 1 ≤ p ^ r := Nat.one_le_pow r p hp1
    have heq : p ^ n = (p ^ r - 1) + (p ^ m - 1) * (s * p ^ r) + 1 := by
      calc p ^ n = p ^ r + (p ^ m - 1) * (s * p ^ r) := hpn2
        _ = ((p ^ r - 1) + 1) + (p ^ m - 1) * (s * p ^ r) := by
              rw [Nat.sub_add_cancel hpr1]
        _ = (p ^ r - 1) + (p ^ m - 1) * (s * p ^ r) + 1 := by ring
    obtain ⟨t, ht⟩ := h
    have h2 : p ^ n = (p ^ m - 1) * t + 1 := Nat.eq_add_of_sub_eq (Nat.one_le_pow n p hp1) ht
    have ht' : (p ^ r - 1) + (p ^ m - 1) * (s * p ^ r) = (p ^ m - 1) * t :=
      Nat.add_right_cancel (heq.symm.trans h2)
    have hAeq : (p ^ m - 1) * t - (p ^ m - 1) * (s * p ^ r) = p ^ r - 1 := by
      rw [← ht', Nat.add_sub_cancel_right]
    have hdA : (p ^ m - 1) ∣ p ^ r - 1 := by
      rw [← hAeq]
      exact Nat.dvd_sub (dvd_mul_right _ _) (dvd_mul_right _ _)
    rcases Nat.eq_zero_or_pos r with h0 | hr0
    · refine ⟨q, ?_⟩
      rw [h0, Nat.add_zero] at hdm
      exact hdm.symm
    · exfalso
      have hlt1 : 0 < p ^ r - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (ne_of_gt hr0) hp)
      have hlt2 : p ^ r - 1 < p ^ m - 1 :=
        Nat.sub_lt_sub_right hpr1 (Nat.pow_lt_pow_right (by linarith) hrlt)
      exact absurd hlt2 (Nat.not_lt.mpr (Nat.le_of_dvd hlt1 hdA))

section Cg18

open Polynomial in
/-- FT `cg18`: each monic irreducible `f` over `𝔽_p` divides `X ^ (p ^ deg f) - X`:
in `AdjoinRoot f` (a field with `p ^ deg f` elements) the class of `X` is a root of
`X ^ (p ^ deg f) - X`, hence `f` is its minimal polynomial and divides it. -/
theorem cg18_dvd_self (p : ℕ) [Fact p.Prime] {f : (ZMod p)[X]} (hf : f.Monic)
    (hirr : Irreducible f) : f ∣ (X ^ p ^ f.natDegree - X : (ZMod p)[X]) := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hp : p.Prime := Fact.out
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  haveI : Module.Finite (ZMod p) (AdjoinRoot f) := Monic.finite_adjoinRoot hf
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  haveI : CharP (AdjoinRoot f) p :=
    (Algebra.charP_iff (ZMod p) (AdjoinRoot f) p).mp (ZMod.charP p)
  haveI : ExpChar (AdjoinRoot f) p := ExpChar.prime hp
  have h3 : (AdjoinRoot.root f : AdjoinRoot f) ^ Fintype.card (AdjoinRoot f) ^ 1 =
      (AdjoinRoot.root f : AdjoinRoot f) :=
    FiniteField.pow_card_pow (K := AdjoinRoot f) 1 _
  have h2 : Fintype.card (AdjoinRoot f) =
      Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (AdjoinRoot f) :=
    Module.card_eq_pow_finrank (K := ZMod p) (V := AdjoinRoot f)
  have hfr : Module.finrank (ZMod p) (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf0).finrank
  rw [pow_one, h2, ZMod.card p, hfr] at h3
  have hmin : minpoly (ZMod p) (AdjoinRoot.root f) = f :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hf
  have hae : aeval (AdjoinRoot.root f : AdjoinRoot f)
      (X ^ p ^ f.natDegree - X : (ZMod p)[X]) = 0 := by
    rw [aeval_sub, aeval_X_pow, aeval_X, sub_eq_zero]
    exact h3
  have hd : minpoly (ZMod p) (AdjoinRoot.root f) ∣
      (X ^ p ^ f.natDegree - X : (ZMod p)[X]) := minpoly.dvd (ZMod p) _ hae
  rw [hmin] at hd
  exact hd

/-- FT `cg18`: each monic irreducible `f` of degree `d ∣ n` in `𝔽_p[X]` divides
`X ^ (p ^ n) - X`. -/
theorem cg18_dvd (p : ℕ) [Fact p.Prime] {f : (ZMod p)[X]} (hf : f.Monic)
    (hirr : Irreducible f) {n : ℕ} (hm : f.natDegree ∣ n) :
    f ∣ (X ^ p ^ n - X : (ZMod p)[X]) :=
  (cg18_dvd_self p hf hirr).trans (dvd_pow_pow_sub_self_of_dvd hm)

/-- FT `cg18`: `X ^ (p ^ n) - X` is squarefree (its factors are distinct), since it is
separable: `galois_poly_separable`. -/
theorem cg18_squarefree (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Squarefree (X ^ p ^ n - X : (ZMod p)[X]) :=
  (galois_poly_separable p (p ^ n) (dvd_pow_self p hn)).squarefree

/-- FT `cg18`: each monic irreducible `f` of degree `d ∣ n` occurs exactly once as a factor
of `X ^ (p ^ n) - X`, i.e. its multiplicity is `1`. -/
theorem cg18_emultiplicity_eq_one (p : ℕ) [Fact p.Prime] {f : (ZMod p)[X]} (hf : f.Monic)
    (hirr : Irreducible f) {n : ℕ} (hm : f.natDegree ∣ n) (hn : n ≠ 0) :
    emultiplicity f (X ^ p ^ n - X : (ZMod p)[X]) = 1 := by
  have hsep : Separable (X ^ p ^ n - X : (ZMod p)[X]) :=
    galois_poly_separable p (p ^ n) (dvd_pow_self p hn)
  have h2 : emultiplicity f (X ^ p ^ n - X) ≤ 1 :=
    Polynomial.emultiplicity_le_one_of_separable hirr.not_isUnit hsep
  have h1 : 1 ≤ emultiplicity f (X ^ p ^ n - X) := by
    have hd : f ^ 1 ∣ (X ^ p ^ n - X : (ZMod p)[X]) := by
      simpa using cg18_dvd p hf hirr hm
    exact pow_dvd_iff_le_emultiplicity.mp hd
  exact le_antisymm h2 h1

/-- FT `cg18`: the degree of the splitting field of a monic irreducible `f` over `𝔽_p` is
exactly `deg f` (so in particular `≤ deg f`): `f` splits in `𝔽_p[X]/(f)`, a field with
`p ^ deg f` elements in which every element is a root of `X ^ (p ^ deg f) - X`. -/
theorem cg18_finrank_splittingField (p : ℕ) [Fact p.Prime] {f : (ZMod p)[X]} (hf : f.Monic)
    (hirr : Irreducible f) : Module.finrank (ZMod p) (SplittingField f) = f.natDegree := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hp : p.Prime := Fact.out
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  haveI : Module.Finite (ZMod p) (AdjoinRoot f) := Monic.finite_adjoinRoot hf
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  have hdvd : f ∣ (X ^ p ^ f.natDegree - X : (ZMod p)[X]) := cg18_dvd_self p hf hirr
  have hfr : Module.finrank (ZMod p) (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf0).finrank
  have hcardN : Nat.card (AdjoinRoot f) = p ^ f.natDegree := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := AdjoinRoot f),
      ZMod.card p, hfr]
  have hsplBig : Splits (X ^ p ^ f.natDegree - X : (AdjoinRoot f)[X]) := by
    have h := splits_X_pow_nat_card_sub_X (K := AdjoinRoot f)
    rwa [hcardN] at h
  have hmap' : map (algebraMap (ZMod p) (AdjoinRoot f)) (X ^ p ^ f.natDegree - X)
      = (X ^ p ^ f.natDegree - X : (AdjoinRoot f)[X]) := by simp
  have hnd' : (X ^ p ^ f.natDegree - X : (AdjoinRoot f)[X]).natDegree = p ^ f.natDegree :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _
      (ne_of_gt (Nat.pos_of_ne_zero fun h => hf0 (by
        have h1 : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h
        have h2 : f.coeff 0 = 1 := by
          have h3 := hf.leadingCoeff
          rw [h1, leadingCoeff_C] at h3
          exact h3
        exact (hirr.not_isUnit (by rw [h1, h2, C_1]; exact isUnit_one)).elim))) hp.one_lt
  have hsplf : Splits (map (algebraMap (ZMod p) (AdjoinRoot f)) f) := by
    refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap (ZMod p) (AdjoinRoot f)) hdvd)
    · rw [hmap']; exact hsplBig
    · rw [hmap']
      intro hgen
      rw [hgen, natDegree_zero] at hnd'
      exact pow_ne_zero _ hp.ne_zero hnd'.symm
  have hroot : AdjoinRoot.root f ∈ f.rootSet (AdjoinRoot f) := by
    rw [mem_rootSet]
    refine ⟨hf0, ?_⟩
    have h := minpoly.aeval (ZMod p) (AdjoinRoot.root f)
    rw [AdjoinRoot.minpoly_root hf0] at h
    simp at h
    exact h
  have hadj : Algebra.adjoin (ZMod p) (f.rootSet (AdjoinRoot f)) = ⊤ := by
    refine le_antisymm le_top ?_
    have h1 : Algebra.adjoin (ZMod p) {AdjoinRoot.root f} = ⊤ := AdjoinRoot.adjoinRoot_eq_top
    have h2 : Algebra.adjoin (ZMod p) {AdjoinRoot.root f} ≤
        Algebra.adjoin (ZMod p) (f.rootSet (AdjoinRoot f)) :=
      Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hroot)
    rwa [h1] at h2
  haveI : IsSplittingField (ZMod p) (AdjoinRoot f) f := ⟨hsplf, hadj⟩
  calc Module.finrank (ZMod p) (SplittingField f)
      = Module.finrank (ZMod p) (AdjoinRoot f) :=
          (IsSplittingField.algEquiv (AdjoinRoot f) f).symm.toLinearEquiv.finrank_eq
    _ = f.natDegree := hfr

end Cg18

/-- FT `cg18m` (existence and uniqueness): an algebraic closure `Ω` of `𝔽_p` contains exactly
one subfield with `p ^ n` elements, namely the subfield of roots of `X ^ (p ^ n) - X`
(FT's `𝔽_{p^n}` "consists of the roots of `X ^ (p ^ n) - X`"). -/
theorem cg18m_exists_unique (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    ∃! S : Subfield (AlgebraicClosure (ZMod p)), Nat.card ↥S = p ^ n := by
  have hp : p.Prime := Fact.out
  haveI : ExpChar (AlgebraicClosure (ZMod p)) p := ExpChar.prime hp
  have hspl : Splits (X ^ p ^ n - X : (AlgebraicClosure (ZMod p))[X]) := IsAlgClosed.splits _
  refine ⟨rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n,
    natCard_rootsSubfield hp hn hspl, ?_⟩
  intro S hS
  exact eq_rootsSubfield_of_card_eq hp hn hS hspl

/-- FT `cg18m`: for subfields of an algebraic closure `Ω` of `𝔽_p`,
`𝔽_{p^m} ⊆ 𝔽_{p^n} ↔ m ∣ n`, where `𝔽_{p^k}` is the subfield of roots of `X ^ (p ^ k) - X`.
(→) uses that the unit group of `𝔽_{p^m}` embeds in that of `𝔽_{p^n}`, so `p^m - 1 ∣ p^n - 1`;
(←) is the elementwise Frobenius iteration. -/
theorem cg18m_subset_iff (p : ℕ) [Fact p.Prime] (hp : p.Prime) (m n : ℕ) :
    (FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp m ≤
      FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) ↔ m ∣ n := by
  haveI : ExpChar (AlgebraicClosure (ZMod p)) p := ExpChar.prime hp
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact dvd_zero m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exfalso
      have huniv : ∀ x : AlgebraicClosure (ZMod p), x ^ p ^ n = x := by
        intro x
        have hx0 : x ^ p ^ 0 = x := by rw [pow_zero, pow_one]
        have hxm : x ∈ FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp 0 :=
          (mem_rootsSubfield hp).2 hx0
        exact (mem_rootsSubfield hp).1 (h hxm)
      have hfin : ({x : AlgebraicClosure (ZMod p) | x ^ p ^ n = x} : Set _).Finite := by
        have hnd : (X ^ p ^ n - X : (AlgebraicClosure (ZMod p))[X]).natDegree = p ^ n :=
          FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ (ne_of_gt hn0) hp.one_lt
        have hne : (X ^ p ^ n - X : (AlgebraicClosure (ZMod p))[X]) ≠ 0 := by
          intro hgen; rw [hgen, natDegree_zero] at hnd
          exact pow_ne_zero n hp.ne_zero hnd.symm
        have hset : {x : AlgebraicClosure (ZMod p) | x ^ p ^ n = x} =
            (X ^ p ^ n - X : (AlgebraicClosure (ZMod p))[X]).rootSet _ := by
          ext x; rw [Set.mem_setOf_eq, aeval_rootsSubfield_iff hne]
        rw [hset]
        exact Polynomial.rootSet_finite _ _
      have hinj : Function.Injective
          (fun x : AlgebraicClosure (ZMod p) =>
            (⟨x, huniv x⟩ : {y : AlgebraicClosure (ZMod p) | y ^ p ^ n = y})) := by
        intro a b hab
        exact congrArg Subtype.val hab
      haveI : Finite ↥({y : AlgebraicClosure (ZMod p) | y ^ p ^ n = y} : Set _) :=
        hfin.to_subtype
      have hfinΩ : Finite (AlgebraicClosure (ZMod p)) :=
        Finite.of_injective (fun x : AlgebraicClosure (ZMod p) =>
          (⟨x, huniv x⟩ : {y : AlgebraicClosure (ZMod p) | y ^ p ^ n = y})) hinj
      have hnf : ¬ Finite (AlgebraicClosure (ZMod p)) :=
        (inferInstance : Infinite (AlgebraicClosure (ZMod p))).not_finite
      exact absurd hfinΩ hnf
    · have hsplM : Splits (X ^ p ^ m - X : (AlgebraicClosure (ZMod p))[X]) := IsAlgClosed.splits _
      have hsplN : Splits (X ^ p ^ n - X : (AlgebraicClosure (ZMod p))[X]) := IsAlgClosed.splits _
      have hcardM : Nat.card {x : AlgebraicClosure (ZMod p) // x ^ p ^ m = x} = p ^ m :=
        natCard_rootsSubfield hp (ne_of_gt hm) hsplM
      have hcardN : Nat.card {x : AlgebraicClosure (ZMod p) // x ^ p ^ n = x} = p ^ n :=
        natCard_rootsSubfield hp (ne_of_gt hn0) hsplN
      have hN : Nat.card ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) = p ^ n :=
        hcardN
      haveI : Finite ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) := by
        have hpos : 0 < Nat.card ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) := by
          rw [hN]; exact pow_pos hp.pos n
        exact (Nat.card_pos_iff.mp hpos).2
      algebraize [Subfield.inclusion h]
      haveI : Module.Finite ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp m)
          ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) := Module.Finite.of_finite
      have hcard : Nat.card ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) =
          (Nat.card ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp m)) ^
            Module.finrank ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp m)
              ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n) :=
        Module.natCard_eq_pow_finrank
      have hM : Nat.card ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp m) = p ^ m :=
        hcardM
      rw [hM, hN, ← pow_mul] at hcard
      refine ⟨Module.finrank ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp m)
        ↥(FT.rootsSubfield (K := AlgebraicClosure (ZMod p)) hp n), ?_⟩
      exact Nat.pow_right_injective (by linarith [Nat.Prime.one_lt hp]) hcard
  · intro h x hx
    exact (mem_rootsSubfield hp).2
      (pow_pow_eq_self_of_dvd h ((mem_rootsSubfield hp).1 hx))

/-- FT `cg18n`: the field `𝔽_p` has an algebraic closure, namely Mathlib's
`AlgebraicClosure (ZMod p)` (which carries the `IsAlgClosure (ZMod p)` instance). -/
theorem cg18n (p : ℕ) [Fact p.Prime] :
    IsAlgClosure (ZMod p) (AlgebraicClosure (ZMod p)) := inferInstance
