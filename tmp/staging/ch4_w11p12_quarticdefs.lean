-- STAGING: FT ch. IV quartic resolvent DEFINITIONS block (cg8 + preliminaries),
-- re-derivation worker w15 (qw11-defs) deliverable, received verbatim.
-- REPL-verified in generation 8; five declarations verified under _v-suffixed temp names
-- (see mapping in the report) — pure renames, proofs character-identical:
--   qcoeff_prod3_X_sub_C, qcoeff_prod3_X_sub_C_zero, qcoeff_prod4_X_sub_C,
--   coeff_resolvent_cubic_target, quartic_resolvent_cubic (also fin4_filter_pairs,
--   quartic_resolvent_vandermonde, quartic_resolvent_discriminant, probe).
-- Paste inside namespace FT, BEFORE staging/ch4_w11p3_cg7gal.lean content.

open Polynomial

/-- Auxiliary: the coefficient of `X - C a` is `-a` at degree `0`, `1` at degree `1`,
and `0` elsewhere. -/
theorem qcoeff_X_sub_C {K : Type*} [CommRing K] (a : K) (n : ℕ) :
    (X - C a).coeff n = if n = 0 then -a else if n = 1 then 1 else 0 := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  rcases n with _ | _ | n
  · simp
  · simp
  · simp [show ¬(1 = n + 1 + 1) by omega, show ¬(n + 1 + 1 = 1) by omega]

/-- Auxiliary: multiplying by `X - C a` changes the constant coefficient to `-a` times
the old one. -/
theorem qcoeff_mul_X_sub_C_zero {K : Type*} [CommRing K] (p : K[X]) (a : K) :
    (p * (X - C a)).coeff 0 = -(a * p.coeff 0) := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_zero]
  simp only [Finset.sum_singleton, qcoeff_X_sub_C, if_pos]
  ring

/-- Auxiliary: coefficients of `(X - C a1) * (X - C a2)`, i.e. the expansion
`X² − (a1+a2)X + a1a2`. -/
theorem qcoeff_prod2_X_sub_C {K : Type*} [CommRing K] (a1 a2 : K) (n : ℕ) :
    ((X - C a1) * (X - C a2)).coeff n
      = if n = 2 then 1 else if n = 1 then -(a1 + a2) else if n = 0 then a1 * a2 else 0 := by
  rcases n with _ | _ | _ | n
  · rw [qcoeff_mul_X_sub_C_zero, qcoeff_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_X_sub_C, qcoeff_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_X_sub_C, qcoeff_X_sub_C]
    simp
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_X_sub_C, qcoeff_X_sub_C]
    simp [show ¬ (n + 2 = 0) by omega, show ¬ (n + 3 = 0) by omega]

/-- Auxiliary: for degree ≥ 3 all coefficients of `(X - C a1) * (X - C a2)` vanish. -/
theorem qcoeff_prod2_X_sub_C_zero {K : Type*} [CommRing K] (a1 a2 : K) (m : ℕ) (hm : 3 ≤ m) :
    ((X - C a1) * (X - C a2)).coeff m = 0 := by
  rw [qcoeff_prod2_X_sub_C]
  split_ifs with h1 h2 h3
  · exact absurd h1 (by omega)
  · exact absurd h2 (by omega)
  · exact absurd h3 (by omega)
  · rfl

/-- Auxiliary: coefficients of `(X - C a1) * (X - C a2) * (X - C a3)`, i.e. the expansion
`X³ − (a1+a2+a3)X² + (a1a2+a1a3+a2a3)X − a1a2a3`. -/
theorem qcoeff_prod3_X_sub_C {K : Type*} [CommRing K] (a1 a2 a3 : K) (n : ℕ) :
    ((X - C a1) * (X - C a2) * (X - C a3)).coeff n
      = if n = 3 then 1
        else if n = 2 then -(a1 + a2 + a3)
        else if n = 1 then a1 * a2 + a1 * a3 + a2 * a3
        else if n = 0 then -(a1 * a2 * a3) else 0 := by
  rcases n with _ | _ | _ | _ | n
  · rw [qcoeff_mul_X_sub_C_zero, qcoeff_prod2_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod2_X_sub_C, qcoeff_prod2_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod2_X_sub_C, qcoeff_prod2_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod2_X_sub_C, qcoeff_prod2_X_sub_C]
    simp
  · rw [Polynomial.coeff_mul_X_sub_C]
    have h3 : 3 ≤ n + 3 := by omega
    have h4 : 3 ≤ n + 4 := by omega
    rw [qcoeff_prod2_X_sub_C_zero _ _ _ h3, qcoeff_prod2_X_sub_C_zero _ _ _ h4]
    simp [show ¬ (n + 3 + 1 = 3) by omega, show ¬ (n + 3 + 1 = 2) by omega]

/-- Auxiliary: for degree ≥ 4 all coefficients of the cubic product vanish. -/
theorem qcoeff_prod3_X_sub_C_zero {K : Type*} [CommRing K] (a1 a2 a3 : K) (m : ℕ)
    (hm : 4 ≤ m) : ((X - C a1) * (X - C a2) * (X - C a3)).coeff m = 0 := by
  rw [qcoeff_prod3_X_sub_C]
  split_ifs with h1 h2 h3 h4
  · exact absurd h1 (by omega)
  · exact absurd h2 (by omega)
  · exact absurd h3 (by omega)
  · exact absurd h4 (by omega)
  · rfl

/-- Auxiliary: coefficients of `(X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)`, i.e. the
expansion `X⁴ − (a1+a2+a3+a4)X³ + (pair sums)X² − (triple sums)X + a1a2a3a4`. -/
theorem qcoeff_prod4_X_sub_C {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) (n : ℕ) :
    ((X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)).coeff n
      = if n = 4 then 1
        else if n = 3 then -(a1 + a2 + a3 + a4)
        else if n = 2 then a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4
        else if n = 1 then -(a1 * a2 * a3 + a1 * a2 * a4 + a1 * a3 * a4 + a2 * a3 * a4)
        else if n = 0 then a1 * a2 * a3 * a4 else 0 := by
  rcases n with _ | _ | _ | _ | _ | n
  · rw [qcoeff_mul_X_sub_C_zero, qcoeff_prod3_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod3_X_sub_C, qcoeff_prod3_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod3_X_sub_C, qcoeff_prod3_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod3_X_sub_C, qcoeff_prod3_X_sub_C]
    simp
    ring
  · rw [Polynomial.coeff_mul_X_sub_C, qcoeff_prod3_X_sub_C]
    have h5 : 4 ≤ 3 + 1 := by omega
    rw [qcoeff_prod3_X_sub_C_zero _ _ _ _ h5]
    simp
  · rw [Polynomial.coeff_mul_X_sub_C]
    have h4 : 4 ≤ n + 4 := by omega
    have h5 : 4 ≤ n + 4 + 1 := by omega
    rw [qcoeff_prod3_X_sub_C_zero _ _ _ _ h4, qcoeff_prod3_X_sub_C_zero _ _ _ _ h5]
    simp [show ¬ (n + 4 + 1 = 4) by omega, show ¬ (n + 4 + 1 = 3) by omega,
      show ¬ (n + 4 + 1 = 2) by omega]

-- FT cg8 (discussion): the partially symmetric elements.
/-- FT IV §4: the partially symmetric element `α = a1a2 + a3a4`. -/
def quarticAlpha {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) : K := a1 * a2 + a3 * a4

/-- FT IV §4: the partially symmetric element `β = a1a3 + a2a4`. -/
def quarticBeta {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) : K := a1 * a3 + a2 * a4

/-- FT IV §4: the partially symmetric element `γ = a1a4 + a2a3`. -/
def quarticGamma {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) : K := a1 * a4 + a2 * a3

/-- FT IV §4: the set `{α, β, γ}` of partially symmetric elements of the quartic. -/
def quarticResolventSet {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) : Set K :=
  insert (quarticAlpha a1 a2 a3 a4) {quarticBeta a1 a2 a3 a4, quarticGamma a1 a2 a3 a4}

-- FT cg8 (discussion): difference factorizations.
/-- FT: `α − β = (a1 − a4)(a2 − a3)`. -/
theorem quarticAlpha_sub_quarticBeta {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) :
    quarticAlpha a1 a2 a3 a4 - quarticBeta a1 a2 a3 a4 = (a1 - a4) * (a2 - a3) := by
  simp only [quarticAlpha, quarticBeta]
  ring

/-- FT: `α − γ = (a1 − a3)(a2 − a4)`. -/
theorem quarticAlpha_sub_quarticGamma {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) :
    quarticAlpha a1 a2 a3 a4 - quarticGamma a1 a2 a3 a4 = (a1 - a3) * (a2 - a4) := by
  simp only [quarticAlpha, quarticGamma]
  ring

/-- FT: `β − γ = (a1 − a2)(a3 − a4)`. -/
theorem quarticBeta_sub_quarticGamma {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) :
    quarticBeta a1 a2 a3 a4 - quarticGamma a1 a2 a3 a4 = (a1 - a2) * (a3 - a4) := by
  simp only [quarticBeta, quarticGamma]
  ring

-- FT cg8 (discussion): distinctness corollaries.
/-- FT: `α ≠ β` if `a1 ≠ a4` and `a2 ≠ a3`. -/
theorem quarticAlpha_ne_quarticBeta {K : Type*} [CommRing K] [IsDomain K] {a1 a2 a3 a4 : K}
    (h1 : a1 ≠ a4) (h2 : a2 ≠ a3) : quarticAlpha a1 a2 a3 a4 ≠ quarticBeta a1 a2 a3 a4 := by
  intro heq
  have h0 : quarticAlpha a1 a2 a3 a4 - quarticBeta a1 a2 a3 a4 = 0 := by
    rw [heq]; exact sub_self _
  have h : (a1 - a4) * (a2 - a3) = 0 := by
    rw [← quarticAlpha_sub_quarticBeta]; exact h0
  rcases mul_eq_zero.mp h with h' | h'
  · exact h1 (sub_eq_zero.mp h')
  · exact h2 (sub_eq_zero.mp h')

/-- FT: `α ≠ γ` if `a1 ≠ a3` and `a2 ≠ a4`. -/
theorem quarticAlpha_ne_quarticGamma {K : Type*} [CommRing K] [IsDomain K] {a1 a2 a3 a4 : K}
    (h1 : a1 ≠ a3) (h2 : a2 ≠ a4) : quarticAlpha a1 a2 a3 a4 ≠ quarticGamma a1 a2 a3 a4 := by
  intro heq
  have h0 : quarticAlpha a1 a2 a3 a4 - quarticGamma a1 a2 a3 a4 = 0 := by
    rw [heq]; exact sub_self _
  have h : (a1 - a3) * (a2 - a4) = 0 := by
    rw [← quarticAlpha_sub_quarticGamma]; exact h0
  rcases mul_eq_zero.mp h with h' | h'
  · exact h1 (sub_eq_zero.mp h')
  · exact h2 (sub_eq_zero.mp h')

/-- FT: `β ≠ γ` if `a1 ≠ a2` and `a3 ≠ a4`. -/
theorem quarticBeta_ne_quarticGamma {K : Type*} [CommRing K] [IsDomain K] {a1 a2 a3 a4 : K}
    (h1 : a1 ≠ a2) (h2 : a3 ≠ a4) : quarticBeta a1 a2 a3 a4 ≠ quarticGamma a1 a2 a3 a4 := by
  intro heq
  have h0 : quarticBeta a1 a2 a3 a4 - quarticGamma a1 a2 a3 a4 = 0 := by
    rw [heq]; exact sub_self _
  have h : (a1 - a2) * (a3 - a4) = 0 := by
    rw [← quarticBeta_sub_quarticGamma]; exact h0
  rcases mul_eq_zero.mp h with h' | h'
  · exact h1 (sub_eq_zero.mp h')
  · exact h2 (sub_eq_zero.mp h')

/-- `α + β + γ` is the second elementary symmetric sum `s₂` of the roots. -/
theorem quartic_psym_sum {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) :
    quarticAlpha a1 a2 a3 a4 + quarticBeta a1 a2 a3 a4 + quarticGamma a1 a2 a3 a4
      = a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4 := by
  simp only [quarticAlpha, quarticBeta, quarticGamma]
  ring

/-- `αβ + αγ + βγ = s₁s₃ − 4s₄` where `s₁, s₃, s₄` are the elementary symmetric sums. -/
theorem quartic_psym_pair {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) :
    quarticAlpha a1 a2 a3 a4 * quarticBeta a1 a2 a3 a4
      + quarticAlpha a1 a2 a3 a4 * quarticGamma a1 a2 a3 a4
      + quarticBeta a1 a2 a3 a4 * quarticGamma a1 a2 a3 a4
      = (a1 + a2 + a3 + a4) * (a1 * a2 * a3 + a1 * a2 * a4 + a1 * a3 * a4 + a2 * a3 * a4)
        - 4 * (a1 * a2 * a3 * a4) := by
  simp only [quarticAlpha, quarticBeta, quarticGamma]
  ring

/-- `αβγ = s₄s₁² − 4s₂s₄ + s₃²` where the `sᵢ` are the elementary symmetric sums. -/
theorem quartic_psym_prod {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) :
    quarticAlpha a1 a2 a3 a4 * quarticBeta a1 a2 a3 a4 * quarticGamma a1 a2 a3 a4
      = a1 * a2 * a3 * a4 * (a1 + a2 + a3 + a4) ^ 2
        - 4 * (a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4)
            * (a1 * a2 * a3 * a4)
        + (a1 * a2 * a3 + a1 * a2 * a4 + a1 * a3 * a4 + a2 * a3 * a4) ^ 2 := by
  simp only [quarticAlpha, quarticBeta, quarticGamma]
  ring

/-- FT (proof of cg8): expanding `f = ∏(X − aᵢ)` and comparing with
`X⁴ + bX³ + cX² + dX + e` yields the four Vieta identities: sum = −b, pair sums = c,
triple sums = −d, product = e. -/
theorem quartic_vieta {K : Type*} [CommRing K] (a1 a2 a3 a4 : K) (b c d e : K)
    (hf : (X : K[X])^4 + C b * X^3 + C c * X^2 + C d * X + C e
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    a1 + a2 + a3 + a4 = -b
      ∧ a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4 = c
      ∧ a1 * a2 * a3 + a1 * a2 * a4 + a1 * a3 * a4 + a2 * a3 * a4 = -d
      ∧ a1 * a2 * a3 * a4 = e := by
  have c3 : ((X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)).coeff 3
      = (X^4 + C b * X^3 + C c * X^2 + C d * X + C e).coeff 3 := by rw [hf]
  have c2 : ((X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)).coeff 2
      = (X^4 + C b * X^3 + C c * X^2 + C d * X + C e).coeff 2 := by rw [hf]
  have c1 : ((X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)).coeff 1
      = (X^4 + C b * X^3 + C c * X^2 + C d * X + C e).coeff 1 := by rw [hf]
  have c0 : ((X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)).coeff 0
      = (X^4 + C b * X^3 + C c * X^2 + C d * X + C e).coeff 0 := by rw [hf]
  rw [qcoeff_prod4_X_sub_C] at c3 c2 c1 c0
  simp at c3 c2 c1 c0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg Neg.neg c3
    simpa using h
  · exact c2
  · have h := congrArg Neg.neg c1
    simpa using h
  · exact c0

/-- Auxiliary: coefficients of the target resolvent cubic
`X³ − cX² + (bd − 4e)X − b²e + 4ce − d²`. -/
theorem coeff_resolvent_cubic_target {K : Type*} [CommRing K] (b c d e : K) (n : ℕ) :
    (X^3 - C c * X^2 + C (b * d - 4 * e) * X + C (-(b^2 * e) + 4 * c * e - d^2)).coeff n
      = if n = 3 then 1 else if n = 2 then -c
        else if n = 1 then b * d - 4 * e
        else if n = 0 then -(b^2 * e) + 4 * c * e - d^2 else 0 := by
  rcases n with _ | _ | _ | _ | n
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_neg (show ¬((0:ℕ) = 3) by decide), if_neg (show ¬((0:ℕ) = 2) by decide),
      if_neg (show ¬((1:ℕ) = 0) by decide), if_pos (show (0:ℕ) = 0 by decide)]
    simp
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_neg (show ¬((1:ℕ) = 3) by decide), if_neg (show ¬((1:ℕ) = 2) by decide),
      if_pos (show (1:ℕ) = 1 by decide), if_neg (show ¬((1:ℕ) = 0) by decide)]
    simp
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_neg (show ¬((2:ℕ) = 3) by decide), if_pos (show (2:ℕ) = 2 by decide),
      if_neg (show ¬((1:ℕ) = 2) by decide), if_neg (show ¬((2:ℕ) = 0) by decide)]
    simp
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_pos (show (3:ℕ) = 3 by decide), if_neg (show ¬((3:ℕ) = 2) by decide),
      if_neg (show ¬((1:ℕ) = 3) by decide), if_neg (show ¬((3:ℕ) = 0) by decide)]
    simp
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_neg (show ¬((n:ℕ) + 4 = 3) by omega), if_neg (show ¬((n:ℕ) + 4 = 2) by omega),
      if_neg (show ¬((n:ℕ) + 4 = 1) by omega), if_neg (show ¬((n:ℕ) + 4 = 0) by omega)]
    simp

/-- FT cg8 (first clause): the resolvent cubic of `f = X⁴ + bX³ + cX² + dX + e` split over
roots `a1, a2, a3, a4` is `g = (X − α)(X − β)(X − γ) = X³ − cX² + (bd − 4e)X − b²e + 4ce − d²`.
Proof: coefficient comparison via the Vieta identities for `f` and the symmetric identities
`α+β+γ = c`, `αβ+αγ+βγ = bd−4e`, `αβγ = b²e−4ce+d²`. -/
theorem quartic_resolvent_cubic {K : Type*} [CommRing K] [IsDomain K]
    (a1 a2 a3 a4 : K) (b c d e : K)
    (hf : (X : K[X])^4 + C b * X^3 + C c * X^2 + C d * X + C e
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    (X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
      * (X - C (quarticGamma a1 a2 a3 a4))
      = X^3 - C c * X^2 + C (b * d - 4 * e) * X + C (-(b^2 * e) + 4 * c * e - d^2) := by
  obtain ⟨h1, h2, h3, h4⟩ := quartic_vieta a1 a2 a3 a4 b c d e hf
  refine Polynomial.ext fun n => ?_
  rw [qcoeff_prod3_X_sub_C, coeff_resolvent_cubic_target]
  rcases n with _ | _ | _ | _ | n
  · simp only [if_neg (show ¬((0:ℕ) = 3) by decide), if_neg (show ¬((0:ℕ) = 2) by decide),
      if_neg (show ¬((0:ℕ) = 1) by decide), if_pos (show (0:ℕ) = 0 by decide)]
    rw [quartic_psym_prod, h1, h2, h3, h4]
    ring
  · simp only [if_neg (show ¬((1:ℕ) = 3) by decide), if_neg (show ¬((1:ℕ) = 2) by decide),
      if_pos (show (1:ℕ) = 1 by decide)]
    rw [quartic_psym_pair, h1, h3, h4]
    simp
  · simp only [if_neg (show ¬((2:ℕ) = 3) by decide), if_pos (show (2:ℕ) = 2 by decide)]
    rw [quartic_psym_sum, h2]
    simp
  · simp
  · simp only [if_neg (show ¬((n:ℕ) + 4 = 3) by omega), if_neg (show ¬((n:ℕ) + 4 = 2) by omega),
      if_neg (show ¬((n:ℕ) + 4 = 1) by omega), if_neg (show ¬((n:ℕ) + 4 = 0) by omega)]

/-- Auxiliary: the pairs `(i, j)` in `Fin 4 × Fin 4` with `i < j`, spelled out. -/
theorem fin4_filter_pairs :
    (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2))
      = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by
  ext p
  simp [Finset.mem_filter]
  fin_cases p <;> simp

/-- FT cg8 (∗): the product of the differences of the partially symmetric elements equals
the Vandermonde product `∏_{i<j} (aᵢ − aⱼ)` of the roots. Proof: substitute the three
difference factorizations and expand the filtered product over the six pairs. -/
theorem quartic_resolvent_vandermonde {K : Type*} [CommRing K] (a : Fin 4 → K) :
    (quarticAlpha (a 0) (a 1) (a 2) (a 3) - quarticBeta (a 0) (a 1) (a 2) (a 3))
      * (quarticAlpha (a 0) (a 1) (a 2) (a 3) - quarticGamma (a 0) (a 1) (a 2) (a 3))
      * (quarticBeta (a 0) (a 1) (a 2) (a 3) - quarticGamma (a 0) (a 1) (a 2) (a 3))
      = ∏ p ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2), (a p.1 - a p.2) := by
  rw [quarticAlpha_sub_quarticBeta, quarticAlpha_sub_quarticGamma,
    quarticBeta_sub_quarticGamma, fin4_filter_pairs]
  simp [Finset.prod_insert, Finset.prod_singleton]
  ring

/-- FT cg8 (second clause): the discriminants of `f` and of its resolvent cubic `g` are
equal: squaring the Vandermonde product gives the square of `(α−β)(α−γ)(β−γ)`. -/
theorem quartic_resolvent_discriminant {K : Type*} [CommRing K] (a : Fin 4 → K) :
    (∏ p ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2), (a p.1 - a p.2)) ^ 2
      = ((quarticAlpha (a 0) (a 1) (a 2) (a 3) - quarticBeta (a 0) (a 1) (a 2) (a 3))
          * (quarticAlpha (a 0) (a 1) (a 2) (a 3) - quarticGamma (a 0) (a 1) (a 2) (a 3))
          * (quarticBeta (a 0) (a 1) (a 2) (a 3)
              - quarticGamma (a 0) (a 1) (a 2) (a 3))) ^ 2 := by
  rw [quartic_resolvent_vandermonde a]

/-- The Vieta identities for a quartic `X⁴ + bX³ + cX² + dX + e` over `F` split in `E`:
sum = −b, pair sums = c, triple sums = −d, product = e (coefficients via `algebraMap`). -/
theorem quartic_vieta_algebraMap {F E : Type u} [Field F] [Field E] [Algebra F E]
    (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    a1 + a2 + a3 + a4 = -(algebraMap F E b)
      ∧ a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4 = algebraMap F E c
      ∧ a1 * a2 * a3 + a1 * a2 * a4 + a1 * a3 * a4 + a2 * a3 * a4 = -(algebraMap F E d)
      ∧ a1 * a2 * a3 * a4 = algebraMap F E e :=
  quartic_vieta a1 a2 a3 a4 _ _ _ _ hf

/-- Compatibility probe replicating the downstream use `rw [quartic_resolvent_cubic
(K := E) a1 a2 a3 a4 (algebraMap F E b) ... hf]` on a coefficient goal. -/
theorem quartic_resolvent_cubic_probe {F E : Type u} [Field F] [Field E] [Algebra F E]
    (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 1
      = algebraMap F E b * algebraMap F E d - 4 * algebraMap F E e := by
  rw [quartic_resolvent_cubic (K := E) a1 a2 a3 a4 (algebraMap F E b) (algebraMap F E c)
    (algebraMap F E d) (algebraMap F E e) hf]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
    if_neg (show ¬((1:ℕ) = 3) by decide), if_neg (show ¬((1:ℕ) = 2) by decide),
    if_neg (show ¬((1:ℕ) = 0) by decide)]
  simp only [if_pos (by trivial : (True : Prop))]
  ring
