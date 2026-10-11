-- staging/ch4_w23_insep.lean — worker w23 (label w21-insep-clauses-cg5cg6), delivered verbatim.
-- FT cg5/cg6 inseparable clauses. Integration notes:
-- * Uses Target's `not_separable_X_pow_sub_C` (FT ft2, ~Target.lean:3764) — must precede.
-- * Deviation vs. request: added degree hypotheses `f.natDegree = 2/3` (mathematically
--   necessary; without them the iff is false, cf. X⁴−T over 𝔽₂(T)).
-- * CharP produced from `(p : F) = 0` via private helper `charP_of_natCast_eq_zero`.

namespace FT

section CgDegree23Inseparable

open Polynomial

variable {F : Type u} [Field F]

/-- FT cg5/cg6 (auxiliary).  In a field `F`, a prime `p` with `(p : F) = 0` gives `CharP F p`:
`ringChar F` divides `p`, hence equals `p` (it cannot be `1` since `(1 : F) ≠ 0`). -/
private theorem charP_of_natCast_eq_zero {p : ℕ} (hp : Nat.Prime p) (hpF : (p : F) = 0) :
    CharP F p := by
  haveI hchar0 : CharP F (ringChar F) := ringChar.charP F
  rcases (Nat.dvd_prime hp).mp (ringChar.dvd hpF) with h1 | hp'
  · exact absurd ((CharP.cast_eq_zero_iff F (ringChar F) 1).mpr (by rw [h1]))
      (by norm_num : ((1 : ℕ) : F) ≠ 0)
  · exact ringChar.of_eq hp'

/-- FT cg5 (inseparable clause).  For a monic irreducible quadratic `f ∈ F[X]`
(`f.natDegree = 2`), `f` is inseparable iff `F` has characteristic `2` and
`f = X ^ 2 - C a` for some `a ∈ F ∖ F ^ 2`.  (Milne's statement "a polynomial of degree 2"
is encoded by the degree hypothesis `hf2`; without it the equivalence is false, cf.
`X ^ 4 - C t` over `𝔽₂(t)`.)

Proof idea.  (⇒) `¬Separable` forces `derivative f = 0`
(`Polynomial.separable_iff_derivative_ne_zero`); comparing coefficients via
`Polynomial.coeff_derivative` gives `(2 : F) = 0` (whence `CharP F 2` by
`charP_of_natCast_eq_zero`) and `f.coeff 1 = 0`, so `f = X ^ 2 - C (-f.coeff 0)` by
coefficient comparison (`Polynomial.ext`).  If `b ^ 2 = a`, then `f = X ^ 2 - C (b ^ 2)` is
irreducible (`hirr`) yet Mathlib's `X_pow_sub_C_irreducible_iff_of_prime` makes its
irreducibility equivalent to `b ^ 2 ≠ b ^ 2` — contradiction.  (⇐) `not_separable_X_pow_sub_C`
(FT `ft2`): in characteristic `2` the derivative of `X ^ 2 - C a` vanishes and
`IsCoprime f 0` would make `f` a unit. -/
theorem irreducible_quad_inseparable_iff {f : F[X]} (hf : f.Monic) (hf2 : f.natDegree = 2)
    (hirr : Irreducible f) :
    ¬ f.Separable ↔ CharP F 2 ∧ ∃ a : F, f = X ^ 2 - C a ∧ ¬ ∃ b : F, b ^ 2 = a := by
  constructor
  · -- (⇒) derivative f = 0, coefficient comparison, a := -f.coeff 0 ∉ F ^ 2
    intro hns
    have hf' : derivative f = 0 := by
      by_contra h
      exact hns ((separable_iff_derivative_ne_zero hirr).2 h)
    have h2f : f.coeff 2 = 1 := by rw [← hf2]; exact hf
    have e1 : f.coeff 2 * (2 : F) = 0 := by
      have h : (derivative f).coeff 1 = f.coeff 2 * (2 : F) := by
        rw [coeff_derivative]
        norm_num
      rw [hf', coeff_zero] at h
      exact h.symm
    rw [h2f] at e1
    have h2F : (2 : F) = 0 := by rwa [one_mul] at e1
    haveI hchar : CharP F 2 := charP_of_natCast_eq_zero Nat.prime_two h2F
    have e0 : f.coeff 1 * (1 : F) = 0 := by
      have h : (derivative f).coeff 0 = f.coeff 1 * (1 : F) := by
        rw [coeff_derivative]
        norm_num
      rw [hf', coeff_zero] at h
      exact h.symm
    have hb0 : f.coeff 1 = 0 := by rwa [mul_one] at e0
    have hfX : f = X ^ 2 - C (-f.coeff 0) := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp [hb0]
      | 2 => simp [h2f]
      | n + 3 =>
        have hL : f.coeff (n + 3) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hf2]; omega)
        simp [hL]
    refine ⟨hchar, -f.coeff 0, hfX, ?_⟩
    rintro ⟨b, hb⟩
    have hirr' : Irreducible (X ^ 2 - C (b ^ 2)) := by
      rw [hb, ← hfX]
      exact hirr
    exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mp hirr' b rfl
  · -- (⇐) FT ft2: in characteristic 2, X ^ 2 - C a is inseparable
    rintro ⟨hchar, a, rfl, -⟩
    exact not_separable_X_pow_sub_C Nat.prime_two a

/-- FT cg6 (inseparable clause).  For a monic irreducible cubic `f ∈ F[X]`
(`f.natDegree = 3`), `f` is inseparable iff `F` has characteristic `3` and
`f = X ^ 3 - C a` for some `a ∈ F ∖ F ^ 3`.  (The irreducibility hypothesis is Milne's "we
can assume `f` to be irreducible": a reducible square `(X - α) ^ 2` in characteristic ≠ 2
also fails to be separable, so degree/irreducibility is what makes the clause correct.)

Proof idea.  (⇒) `¬Separable` forces `derivative f = 0`
(`Polynomial.separable_iff_derivative_ne_zero`); comparing coefficients via
`Polynomial.coeff_derivative` gives `(3 : F) = 0` (whence `CharP F 3` by
`charP_of_natCast_eq_zero`), then `f.coeff 2 = 0` since `(2 : F) ≠ 0` in characteristic `3`
(otherwise `1 = 3 - 2 = 0`), and `f.coeff 1 = 0`, so `f = X ^ 3 - C (-f.coeff 0)` by
coefficient comparison (`Polynomial.ext`).  If `b ^ 3 = a`, then `f = X ^ 3 - C (b ^ 3)` is
irreducible (`hirr`) yet Mathlib's `X_pow_sub_C_irreducible_iff_of_prime` makes its
irreducibility equivalent to `b ^ 3 ≠ b ^ 3` — contradiction.  (⇐) `not_separable_X_pow_sub_C`
(FT `ft2`): in characteristic `3` the derivative of `X ^ 3 - C a` vanishes and
`IsCoprime f 0` would make `f` a unit. -/
theorem irreducible_cubic_inseparable_iff {f : F[X]} (hf : f.Monic) (hf3 : f.natDegree = 3)
    (hirr : Irreducible f) :
    ¬ f.Separable ↔ CharP F 3 ∧ ∃ a : F, f = X ^ 3 - C a ∧ ¬ ∃ b : F, b ^ 3 = a := by
  constructor
  · -- (⇒) derivative f = 0, coefficient comparison, a := -f.coeff 0 ∉ F ^ 3
    intro hns
    have hf' : derivative f = 0 := by
      by_contra h
      exact hns ((separable_iff_derivative_ne_zero hirr).2 h)
    have h3f : f.coeff 3 = 1 := by rw [← hf3]; exact hf
    have e2 : f.coeff 3 * (3 : F) = 0 := by
      have h : (derivative f).coeff 2 = f.coeff 3 * (3 : F) := by
        rw [coeff_derivative]
        norm_num
      rw [hf', coeff_zero] at h
      exact h.symm
    rw [h3f] at e2
    have h3F : (3 : F) = 0 := by rwa [one_mul] at e2
    haveI hchar : CharP F 3 := charP_of_natCast_eq_zero Nat.prime_three h3F
    have h2ne : (2 : F) ≠ 0 := by
      intro h2
      have h31 : (3 : F) = (2 : F) + (1 : F) := by norm_num
      have hsum : (2 : F) + (1 : F) = 0 := by rw [← h31]; exact h3F
      rw [h2] at hsum
      have h1 : (1 : F) = 0 := by
        calc (1 : F) = (0 : F) + (1 : F) := (zero_add (1 : F)).symm
          _ = 0 := hsum
      exact one_ne_zero h1
    have e1 : f.coeff 2 * (2 : F) = 0 := by
      have h : (derivative f).coeff 1 = f.coeff 2 * (2 : F) := by
        rw [coeff_derivative]
        norm_num
      rw [hf', coeff_zero] at h
      exact h.symm
    have hp0 : f.coeff 2 = 0 := by
      rcases mul_eq_zero.mp e1 with hc | hc
      · exact hc
      · exact absurd hc h2ne
    have e0 : f.coeff 1 * (1 : F) = 0 := by
      have h : (derivative f).coeff 0 = f.coeff 1 * (1 : F) := by
        rw [coeff_derivative]
        norm_num
      rw [hf', coeff_zero] at h
      exact h.symm
    have hq0 : f.coeff 1 = 0 := by rwa [mul_one] at e0
    have hfX : f = X ^ 3 - C (-f.coeff 0) := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp [hq0]
      | 2 => simp [hp0]
      | 3 => simp [h3f]
      | n + 4 =>
        have hL : f.coeff (n + 4) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hf3]; omega)
        simp [hL]
    refine ⟨hchar, -f.coeff 0, hfX, ?_⟩
    rintro ⟨b, hb⟩
    have hirr' : Irreducible (X ^ 3 - C (b ^ 3)) := by
      rw [hb, ← hfX]
      exact hirr
    exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three).mp hirr' b rfl
  · -- (⇐) FT ft2: in characteristic 3, X ^ 3 - C a is inseparable
    rintro ⟨hchar, a, rfl, -⟩
    exact not_separable_X_pow_sub_C Nat.prime_three a

end CgDegree23Inseparable

end FT
