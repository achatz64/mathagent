-- STAGING: FT ch. IV §4 quartic examples cg8a/cg9/cg10/cg11 (worker w17), received
-- verbatim except: dropped the blanket `set_option linter.unusedSimpArgs false` /
-- `set_option linter.unusedVariables false` (to be handled per-warning at integration).
-- Verified in-session under _v-suffixed names, byte-identical bodies; final names here.
-- Uses FT.quartic_resolvent_cubic / quarticAlpha/Beta/Gamma (ch4 block, in Target) and
-- FT.eisenstein_irreducible (ch1, in Target).
-- Pending in source (worker scope note): the classification-table downstream use
-- (D4/C4/V/S4 dichotomies) is NOT formalized.
-- Paste inside namespace FT.

open Polynomial

/-- FT cg8a-cg11 (auxiliary).  A polynomial whose `n`-th coefficient is nonzero has degree
exactly `n` if its degree is at most `n`: `natDegree ≤ n` from the hypothesis, and
`n ≤ natDegree` because coefficients above the degree vanish. -/
theorem natDegree_eq_of_coeff_ne_zero {K : Type*} [CommRing K] {p : K[X]} {n : ℕ}
    (h1 : p.natDegree ≤ n) (h2 : p.coeff n ≠ 0) : p.natDegree = n := by
  refine le_antisymm h1 (Nat.le_of_not_gt fun hlt => h2 ?_)
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt

/-- FT cg8a (auxiliary).  Coefficients of `X³ − uX − v`. -/
theorem coeff_cubic_X_neg_C {K : Type*} [CommRing K] (u v : K) (n : ℕ) :
    (X^3 - C u * X - C v : K[X]).coeff n
      = if n = 3 then 1 else if n = 1 then -u else if n = 0 then -v else 0 := by
  rcases n with _ | _ | _ | _ | n
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, if_neg (show ¬((n:ℕ)+4 = 3) by omega),
      if_neg (show ¬((n:ℕ)+4 = 1) by omega), if_neg (show ¬((n:ℕ)+4 = 0) by omega)]
    norm_num

/-- FT cg9 (auxiliary).  Coefficients of `X³ − uX² − vX + w`. -/
theorem coeff_cubic_neg_C_neg_C_C {K : Type*} [CommRing K] (u v w : K) (n : ℕ) :
    (X^3 - C u * X^2 - C v * X + C w : K[X]).coeff n
      = if n = 3 then 1 else if n = 2 then -u else if n = 1 then -v
        else if n = 0 then w else 0 := by
  rcases n with _ | _ | _ | _ | n
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_neg (show ¬((n:ℕ)+4 = 3) by omega), if_neg (show ¬((n:ℕ)+4 = 2) by omega),
      if_neg (show ¬((n:ℕ)+4 = 1) by omega), if_neg (show ¬((n:ℕ)+4 = 0) by omega)]
    norm_num

/-- FT cg10 (auxiliary).  Coefficients of `X³ + uX² − vX − w`. -/
theorem coeff_cubic_C_neg_C_neg_C {K : Type*} [CommRing K] (u v w : K) (n : ℕ) :
    (X^3 + C u * X^2 - C v * X - C w : K[X]).coeff n
      = if n = 3 then 1 else if n = 2 then u else if n = 1 then -v
        else if n = 0 then -w else 0 := by
  rcases n with _ | _ | _ | _ | n
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      if_neg (show ¬((n:ℕ)+4 = 3) by omega), if_neg (show ¬((n:ℕ)+4 = 2) by omega),
      if_neg (show ¬((n:ℕ)+4 = 1) by omega), if_neg (show ¬((n:ℕ)+4 = 0) by omega)]
    norm_num

/-- FT cg11 (auxiliary).  Coefficients of `X³ + uX`. -/
theorem coeff_cubic_C_X {K : Type*} [CommRing K] (u : K) (n : ℕ) :
    (X^3 + C u * X : K[X]).coeff n
      = if n = 3 then 1 else if n = 2 then 0 else if n = 1 then u
        else if n = 0 then 0 else 0 := by
  rcases n with _ | _ | _ | n
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, if_neg (show ¬((n:ℕ)+4 = 3) by omega),
      if_neg (show ¬((n:ℕ)+4 = 1) by omega)]
    norm_num

/-- FT cg10 (auxiliary).  The antidiagonal convolution sum as an explicit range sum. -/
theorem sum_antidiagonal_range {M : Type*} [AddCommMonoid M] (F : ℕ × ℕ → M) (n : ℕ) :
    ∑ x ∈ Finset.antidiagonal n, F x = ∑ i ∈ Finset.range (n + 1), F (i, n - i) := by
  rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  simp

/-- FT cg10 (auxiliary).  No integer squares to 6. -/
theorem not_sq_6 (u : ℤ) (h : u ^ 2 = 6) : False := by
  have h1 : u ∣ u ^ 2 := Dvd.intro u (pow_two u).symm
  rw [h] at h1
  obtain ⟨m, hm⟩ := h1
  have hmul : u.natAbs * m.natAbs = (6 : ℕ) := by rw [← Int.natAbs_mul, ← hm]; norm_num
  have hle : u.natAbs ≤ 6 := Nat.le_of_dvd (by norm_num) (Dvd.intro m.natAbs hmul)
  have h2 : (↑u.natAbs : ℤ) ^ 2 = 6 := by rw [Int.natAbs_sq, h]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, u.natAbs = k := ⟨u.natAbs, rfl⟩
  rw [hk] at hle h2
  interval_cases k
  all_goals norm_num at h2

/-- FT cg10 (auxiliary).  No integer squares to 14. -/
theorem not_sq_14 (u : ℤ) (h : u ^ 2 = 14) : False := by
  have h1 : u ∣ u ^ 2 := Dvd.intro u (pow_two u).symm
  rw [h] at h1
  obtain ⟨m, hm⟩ := h1
  have hmul : u.natAbs * m.natAbs = (14 : ℕ) := by rw [← Int.natAbs_mul, ← hm]; norm_num
  have hle : u.natAbs ≤ 14 := Nat.le_of_dvd (by norm_num) (Dvd.intro m.natAbs hmul)
  have h2 : (↑u.natAbs : ℤ) ^ 2 = 14 := by rw [Int.natAbs_sq, h]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, u.natAbs = k := ⟨u.natAbs, rfl⟩
  rw [hk] at hle h2
  interval_cases k
  all_goals norm_num at h2

/-- FT cg10 (auxiliary).  No integer squares to 21. -/
theorem not_sq_21 (u : ℤ) (h : u ^ 2 = 21) : False := by
  have h1 : u ∣ u ^ 2 := Dvd.intro u (pow_two u).symm
  rw [h] at h1
  obtain ⟨m, hm⟩ := h1
  have hmul : u.natAbs * m.natAbs = (21 : ℕ) := by rw [← Int.natAbs_mul, ← hm]; norm_num
  have hle : u.natAbs ≤ 21 := Nat.le_of_dvd (by norm_num) (Dvd.intro m.natAbs hmul)
  have h2 : (↑u.natAbs : ℤ) ^ 2 = 21 := by rw [Int.natAbs_sq, h]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, u.natAbs = k := ⟨u.natAbs, rfl⟩
  rw [hk] at hle h2
  interval_cases k
  all_goals norm_num at h2

/-- FT cg10 (auxiliary).  Evaluation of `X⁴ − 10X² + 4` at an integer. -/
theorem eval_f10 (r : ℤ) :
    eval r (X^4 - C 10 * X^2 + C 4 : ℤ[X]) = r ^ 4 - 10 * r ^ 2 + 4 := by
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C_mul,
    Polynomial.eval_C, Polynomial.eval_X_pow]

/-- FT cg10 (auxiliary).  The leading coefficient of `X⁴ − 10X² + 4` is 1. -/
theorem cg10_coeff4 : (X^4 - C 10 * X^2 + C 4 : ℤ[X]).coeff 4 = 1 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

/-- FT cg10 (auxiliary).  A polynomial of degree ≤ 1 is `aX + b`. -/
theorem rep_le_one {K : Type*} [CommRing K] {p : K[X]} (hp : p.natDegree ≤ 1) :
    p = Polynomial.C (p.coeff 1) * X + Polynomial.C (p.coeff 0) := by
  refine Polynomial.ext fun n => ?_
  rcases n with _ | _ | n
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]
    norm_num
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C, if_neg (show ¬((n:ℕ)+2 = 1) by omega),
      if_neg (show ¬((n:ℕ)+2 = 0) by omega)]
    norm_num

/-- FT cg10 (auxiliary).  A polynomial of degree ≤ 2 is `aX² + bX + c`. -/
theorem rep_le_two {K : Type*} [CommRing K] {p : K[X]} (hp : p.natDegree ≤ 2) :
    p = Polynomial.C (p.coeff 2) * X ^ 2 + Polynomial.C (p.coeff 1) * X
      + Polynomial.C (p.coeff 0) := by
  refine Polynomial.ext fun n => ?_
  rcases n with _ | _ | _ | n
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, if_neg (show ¬((n:ℕ)+3 = 2) by omega),
      if_neg (show ¬((n:ℕ)+3 = 1) by omega), if_neg (show ¬((n:ℕ)+3 = 0) by omega)]
    norm_num

/-- FT cg10 (auxiliary).  A polynomial of degree ≤ 3 is `aX³ + bX² + cX + d`. -/
theorem rep_le_three {K : Type*} [CommRing K] {p : K[X]} (hp : p.natDegree ≤ 3) :
    p = Polynomial.C (p.coeff 3) * X ^ 3 + Polynomial.C (p.coeff 2) * X ^ 2
      + Polynomial.C (p.coeff 1) * X + Polynomial.C (p.coeff 0) := by
  refine Polynomial.ext fun n => ?_
  rcases n with _ | _ | _ | _ | n
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, if_neg (show ¬((n:ℕ)+4 = 3) by omega),
      if_neg (show ¬((n:ℕ)+4 = 2) by omega), if_neg (show ¬((n:ℕ)+4 = 1) by omega),
      if_neg (show ¬((n:ℕ)+4 = 0) by omega)]
    norm_num

/-- FT cg10 (auxiliary).  No integer dividing 4 is a root of `X⁴ − 10X² + 4`. -/
theorem cg10_no_root_4 (n : ℤ) (hd : n ∣ 4) : n ^ 4 - 10 * n ^ 2 + 4 ≠ 0 := by
  obtain ⟨m, hm⟩ := hd
  have hmul : n.natAbs * m.natAbs = (4 : ℕ) := by rw [← Int.natAbs_mul, ← hm]; norm_num
  have hle : n.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) (Dvd.intro m.natAbs hmul)
  have h2 : (↑n.natAbs : ℤ) ^ 2 = n ^ 2 := Int.natAbs_sq n
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n.natAbs = k := ⟨n.natAbs, rfl⟩
  rw [hk] at hle h2
  rcases Int.natAbs_eq n with hn | hn
  · rw [hk] at hn; subst hn
    interval_cases k
    all_goals norm_num
  · rw [hk] at hn; subst hn
    interval_cases k
    all_goals norm_num

/-- FT cg10 (auxiliary).  `X⁴ − 10X² + 4` has degree 4 over ℤ. -/
theorem cg10_natDegree_4 :
    (X^4 - C 10 * X^2 + C 4 : ℤ[X]).natDegree = 4 := by
  have hX4 : ((X : ℤ[X])^4).natDegree = 4 := by rw [Polynomial.natDegree_X_pow]
  have hCX : (C 10 * X ^ 2 : ℤ[X]).natDegree ≤ 2 := by
    have h : (C 10 * X ^ 2 : ℤ[X]).natDegree
        ≤ (C 10 : ℤ[X]).natDegree + ((X : ℤ[X]) ^ 2).natDegree := Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow] at h
    omega
  have hsub : (X^4 - C 10 * X^2 : ℤ[X]).natDegree
      ≤ max ((X : ℤ[X])^4).natDegree ((C 10 * X ^ 2 : ℤ[X]).natDegree) :=
    Polynomial.natDegree_sub_le _ _
  have hd1 : (X^4 - C 10 * X^2 : ℤ[X]).natDegree ≤ 4 := by omega
  have hC4 : (C 4 : ℤ[X]).natDegree = 0 := Polynomial.natDegree_C _
  have hadd : (X^4 - C 10 * X^2 + C 4 : ℤ[X]).natDegree
      ≤ max (X^4 - C 10 * X^2 : ℤ[X]).natDegree (C 4 : ℤ[X]).natDegree :=
    Polynomial.natDegree_add_le _ _
  have hle : (X^4 - C 10 * X^2 + C 4 : ℤ[X]).natDegree ≤ 4 := by omega
  exact natDegree_eq_of_coeff_ne_zero hle (by
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num)

/-- FT cg10 (auxiliary).  If `(aX² + bX + c)(a'X² + b'X + c') = X⁴ − 10X² + 4` coefficientwise
with integer coefficients, we get a contradiction: `a = a' = ±1`, then either `b = 0` forces
`c' + c = ±10` with `cc' = 4`, impossible by a divisor check, or `c' = c` forces `c² = 4` and
then `b² = 2ac + 10 ∈ {6, 14}`, not a square. -/
theorem cg10_quad_elim (a b c a' b' c' : ℤ)
    (h1 : a * a' = 1) (h2 : a * b' + b * a' = 0) (h3 : a * c' + b * b' + c * a' = -10)
    (h4 : b * c' + c * b' = 0) (h5 : c * c' = 4) : False := by
  have hn1 : a.natAbs * a'.natAbs = 1 := by rw [← Int.natAbs_mul, h1]; norm_num
  have hna1 : a.natAbs = 1 := Nat.dvd_one.mp (Dvd.intro a'.natAbs hn1)
  rcases Int.natAbs_eq a with ha | ha
  · rw [hna1] at ha; subst ha
    have hpa : a' = 1 := by omega
    subst hpa
    have hb' : b' = -b := by omega
    subst hb'
    rw [mul_neg, mul_comm c b] at h4
    have hfac : b * (c' - c) = 0 := by
      rw [mul_sub]
      linarith
    rcases mul_eq_zero.mp hfac with hb0 | hcc
    · subst hb0
      have hsum : c' + c = -10 := by omega
      have hdvd : c ∣ (4 : ℤ) := Dvd.intro c' h5
      obtain ⟨mm, hmm⟩ := hdvd
      have hc4 : c.natAbs * mm.natAbs = (4 : ℕ) := by rw [← Int.natAbs_mul, ← hmm]; norm_num
      have hcle : c.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) (Dvd.intro mm.natAbs hc4)
      obtain ⟨k, hkk⟩ : ∃ k : ℕ, c.natAbs = k := ⟨c.natAbs, rfl⟩
      rw [hkk] at hcle
      rcases Int.natAbs_eq c with hc | hc
      · rw [hkk] at hc; subst hc
        interval_cases k
        all_goals omega
      · rw [hkk] at hc; subst hc
        interval_cases k
        all_goals omega
    · have hcc2 : c' = c := by omega
      rw [hcc2] at h3 h5
      have hcsq : c ^ 2 = 4 := by rw [pow_two]; exact h5
      rcases (mul_eq_zero.mp (show (c - 2) * (c + 2) = 0 by nlinarith [hcsq])) with hc | hc
      · have hc2 : c = 2 := by omega
        subst hc2
        have hb2 : b ^ 2 = 14 := by nlinarith [h3]
        exact not_sq_14 b hb2
      · have hc2 : c = -2 := by omega
        subst hc2
        have hb2 : b ^ 2 = 6 := by nlinarith [h3]
        exact not_sq_6 b hb2
  · rw [hna1] at ha; subst ha
    have hpa : a' = -1 := by omega
    subst hpa
    have hb' : b' = -b := by omega
    subst hb'
    rw [mul_neg, mul_comm c b] at h4
    have hfac : b * (c' - c) = 0 := by
      rw [mul_sub]
      linarith
    rcases mul_eq_zero.mp hfac with hb0 | hcc
    · subst hb0
      have hsum : c' + c = 10 := by omega
      have hdvd : c ∣ (4 : ℤ) := Dvd.intro c' h5
      obtain ⟨mm, hmm⟩ := hdvd
      have hc4 : c.natAbs * mm.natAbs = (4 : ℕ) := by rw [← Int.natAbs_mul, ← hmm]; norm_num
      have hcle : c.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) (Dvd.intro mm.natAbs hc4)
      obtain ⟨k, hkk⟩ : ∃ k : ℕ, c.natAbs = k := ⟨c.natAbs, rfl⟩
      rw [hkk] at hcle
      rcases Int.natAbs_eq c with hc | hc
      · rw [hkk] at hc; subst hc
        interval_cases k
        all_goals omega
      · rw [hkk] at hc; subst hc
        interval_cases k
        all_goals omega
    · have hcc2 : c' = c := by omega
      rw [hcc2] at h3 h5
      have hcsq : c ^ 2 = 4 := by rw [pow_two]; exact h5
      rcases (mul_eq_zero.mp (show (c - 2) * (c + 2) = 0 by nlinarith [hcsq])) with hc | hc
      · have hc2 : c = 2 := by omega
        subst hc2
        have hb2 : b ^ 2 = 6 := by nlinarith [h3]
        exact not_sq_6 b hb2
      · have hc2 : c = -2 := by omega
        subst hc2
        have hb2 : b ^ 2 = 14 := by nlinarith [h3]
        exact not_sq_14 b hb2

/-- FT cg10 (auxiliary).  Multiplying out `(s₂X² + s₁X + s₀)(t₂X² + t₁X + t₀)` and comparing
with `X⁴ − 10X² + 4` coefficient by coefficient gives the five relations fed to
`cg10_quad_elim`. -/
theorem coeff_quad_prod (s2 s1 s0 t2 t1 t0 : ℤ)
    (hst : (C s2 * X^2 + C s1 * X + C s0 : ℤ[X]) * (C t2 * X^2 + C t1 * X + C t0)
      = X^4 - C 10 * X^2 + C 4) :
    s2 * t2 = 1 ∧ s2 * t1 + s1 * t2 = 0 ∧ s2 * t0 + s1 * t1 + s0 * t2 = -10
      ∧ s1 * t0 + s0 * t1 = 0 ∧ s0 * t0 = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 := congrArg (fun p => p.coeff 4) hst
    rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero] at h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1
    norm_num at h1
    exact h1
  · have h1 := congrArg (fun p => p.coeff 3) hst
    rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1
    norm_num at h1
    linarith
  · have h1 := congrArg (fun p => p.coeff 2) hst
    rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1
    norm_num at h1
    linarith
  · have h1 := congrArg (fun p => p.coeff 1) hst
    rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero] at h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1
    norm_num at h1
    linarith
  · have h1 := congrArg (fun p => p.coeff 0) hst
    rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
      Finset.sum_range_zero] at h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1
    norm_num at h1
    exact h1

/-- FT cg10 (auxiliary).  If `X⁴ − 10X² + 4 = s * t` in ℤ[X] with `s, t` both nonzero and
non-units and `deg s ≤ 2`, we get a contradiction.  Degree 0: comparing leading coefficients
gives `s₀ · t₄ = 1`, so `s₀ = ±1` and `s` is a unit.  Degree 1: comparing leading coefficients
gives `s₁ t₃ = 1`, so `s₁ = ±1` and `s = ±X + s₀` has the integer root `∓s₀`, forcing
`X⁴ − 10X² + 4` to vanish at an integer dividing 4, contradicting `cg10_no_root_4`.
Degree 2: comparing all five coefficients and applying `cg10_quad_elim`. -/
theorem cg10_small_elim (s t : ℤ[X]) (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hsu : ¬IsUnit s)
    (htu : ¬IsUnit t) (hst : s * t = X^4 - C 10 * X^2 + C 4) (hsd : s.natDegree ≤ 2) : False := by
  have hfnd : (X^4 - C 10 * X^2 + C 4 : ℤ[X]).natDegree = 4 := cg10_natDegree_4
  have hdeg : (s * t).natDegree = s.natDegree + t.natDegree :=
    Polynomial.natDegree_mul hs0 ht0
  rw [hst, hfnd] at hdeg
  rcases Nat.lt_or_ge s.natDegree 1 with h0 | h1
  · have hrep : s = C 0 * X + C (s.coeff 0) := by
      have hr : s = C (s.coeff 1) * X + C (s.coeff 0) := rep_le_one (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt h0] at hr
      exact hr
    have h1c := congrArg (fun p => p.coeff 4) hst
    nth_rewrite 1 [hrep] at h1c
    rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero] at h1c
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1c
    norm_num at h1c
    have hn1 : (s.coeff 0).natAbs * (t.coeff 4).natAbs = 1 := by
      rw [← Int.natAbs_mul, h1c]; norm_num
    have hna : (s.coeff 0).natAbs = 1 := Nat.dvd_one.mp (Dvd.intro (t.coeff 4).natAbs hn1)
    have hIu : IsUnit (s.coeff 0) := by
      rw [Int.isUnit_iff]
      rcases Int.natAbs_eq (s.coeff 0) with hc | hc
      · rw [hna] at hc; exact Or.inl hc
      · rw [hna] at hc; exact Or.inr hc
    refine hsu ?_
    have hsC : s = C (s.coeff 0) := by
      nth_rewrite 1 [hrep]
      simp only [Polynomial.C_0, zero_mul, zero_add]
    rw [hsC]
    exact Polynomial.isUnit_C.mpr hIu
  · rcases Nat.lt_or_ge s.natDegree 2 with h1c | h2c
    · have hsdeq : s.natDegree = 1 := by omega
      have htdeq : t.natDegree = 3 := by omega
      have hrep : s = C (s.coeff 1) * X + C (s.coeff 0) := rep_le_one (by omega)
      have htrep : t = C (t.coeff 3) * X ^ 3 + C (t.coeff 2) * X ^ 2 + C (t.coeff 1) * X
        + C (t.coeff 0) := rep_le_three (by omega)
      rw [hrep, htrep] at hst
      have e4 : s.coeff 1 * t.coeff 3 = 1 := by
        have h1x := congrArg (fun p => p.coeff 4) hst
        rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_zero] at h1x
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1x
        norm_num at h1x
        exact h1x
      have e0 : s.coeff 0 * t.coeff 0 = 4 := by
        have h1x := congrArg (fun p => p.coeff 0) hst
        rw [Polynomial.coeff_mul, sum_antidiagonal_range, Finset.sum_range_succ,
          Finset.sum_range_zero] at h1x
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h1x
        norm_num at h1x
        exact h1x
      have hn1 : (s.coeff 1).natAbs * (t.coeff 3).natAbs = 1 := by
        rw [← Int.natAbs_mul, e4]; norm_num
      have hna : (s.coeff 1).natAbs = 1 := Nat.dvd_one.mp (Dvd.intro (t.coeff 3).natAbs hn1)
      rcases Int.natAbs_eq (s.coeff 1) with he1 | he1
      · rw [hna] at he1
        have hsval : eval (-s.coeff 0) (C (s.coeff 1) * X + C (s.coeff 0) : ℤ[X]) = 0 := by
          rw [he1]
          simp only [Polynomial.eval_add, Polynomial.eval_C_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          ring
        have hfval : eval (-s.coeff 0) (X^4 - C 10 * X^2 + C 4 : ℤ[X]) = 0 := by
          rw [← hst, Polynomial.eval_mul, hsval, zero_mul]
        have hcon : (-s.coeff 0) ^ 4 - 10 * (-s.coeff 0) ^ 2 + 4 = 0 :=
          (eval_f10 _).symm.trans hfval
        have hcon' : s.coeff 0 ^ 4 - 10 * s.coeff 0 ^ 2 + 4 = 0 := by
          rw [← hcon]; ring
        exact cg10_no_root_4 (s.coeff 0) (Dvd.intro (t.coeff 0) e0) hcon'
      · rw [hna] at he1
        have hsval : eval (s.coeff 0) (C (s.coeff 1) * X + C (s.coeff 0) : ℤ[X]) = 0 := by
          rw [he1]
          simp only [Polynomial.eval_add, Polynomial.eval_C_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          ring
        have hfval : eval (s.coeff 0) (X^4 - C 10 * X^2 + C 4 : ℤ[X]) = 0 := by
          rw [← hst, Polynomial.eval_mul, hsval, zero_mul]
        have hcon : s.coeff 0 ^ 4 - 10 * s.coeff 0 ^ 2 + 4 = 0 :=
          (eval_f10 _).symm.trans hfval
        exact cg10_no_root_4 (s.coeff 0) (Dvd.intro (t.coeff 0) e0) hcon
    · have hsdeq : s.natDegree = 2 := by omega
      have htdeq : t.natDegree = 2 := by omega
      have hrep : s = C (s.coeff 2) * X ^ 2 + C (s.coeff 1) * X + C (s.coeff 0) :=
        rep_le_two (by omega)
      have htrep : t = C (t.coeff 2) * X ^ 2 + C (t.coeff 1) * X + C (t.coeff 0) :=
        rep_le_two (by omega)
      rw [hrep, htrep] at hst
      obtain ⟨e4, e3, e2, e1, e0⟩ := coeff_quad_prod _ _ _ _ _ _ hst
      exact cg10_quad_elim _ _ _ _ _ _ e4 e3 e2 e1 e0

/-- FT cg10 (third clause).  `X⁴ − 10X² + 4` is irreducible in ℤ[X]: any factorization splits
its degree 4 into factors of degrees summing to 4, and the factor of degree ≤ 2 leads to a
contradiction via `cg10_small_elim`. -/
theorem cg10_irreducible_int : Irreducible (X^4 - C 10 * X^2 + C 4 : ℤ[X]) := by
  have hfnd : (X^4 - C 10 * X^2 + C 4 : ℤ[X]).natDegree = 4 := cg10_natDegree_4
  have hf0 : (X^4 - C 10 * X^2 + C 4 : ℤ[X]) ≠ 0 := by
    intro h
    have hc4 := cg10_coeff4
    rw [h] at hc4
    simp only [Polynomial.coeff_zero] at hc4
    norm_num at hc4
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨u, hu1, hu2⟩ := Polynomial.isUnit_iff.mp hu
    have hcu : (C u : ℤ[X]).coeff 4 = 1 := by
      rw [hu2]
      exact cg10_coeff4
    simp only [Polynomial.coeff_C] at hcu
    norm_num at hcu
  · intro g h hgh
    have hgh' : g * h = (X^4 - C 10 * X^2 + C 4 : ℤ[X]) := hgh.symm
    have hg0 : g ≠ 0 := fun hg => hf0 (by rw [hgh, hg, zero_mul])
    have hh0 : h ≠ 0 := fun hh => hf0 (by rw [hgh, hh, mul_zero])
    by_contra hboth
    obtain ⟨hgu, hhu⟩ := not_or.mp hboth
    have hsum4 : 4 = g.natDegree + h.natDegree := by
      have h1 := Polynomial.natDegree_mul hg0 hh0
      rw [hgh', hfnd] at h1
      exact h1
    rcases le_total g.natDegree h.natDegree with hgl | hgl
    · exact cg10_small_elim g h hg0 hh0 hgu hhu hgh' (by omega)
    · exact cg10_small_elim h g hh0 hg0 hhu hgu (by rw [mul_comm h g]; exact hgh')
        (by omega)

/-- FT cg10 (fourth clause).  `X⁴ − 10X² + 4` is irreducible over ℚ: the polynomial is
primitive and irreducible in ℤ[X], so Gauss's lemma
(`Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`) transfers irreducibility
along the map `Int.castRingHom ℚ`, which fixes the coefficients of `X⁴ − 10X² + 4`. -/
theorem cg10_irreducible : Irreducible (X^4 - C 10 * X^2 + C 4 : ℚ[X]) := by
  have hprim : (X^4 - C 10 * X^2 + C 4 : ℤ[X]).IsPrimitive :=
    Irreducible.isPrimitive cg10_irreducible_int (by
      rw [cg10_natDegree_4]; norm_num)
  have hres := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    cg10_irreducible_int
  have heq : Polynomial.map (Int.castRingHom ℚ) (X^4 - C 10 * X^2 + C 4 : ℤ[X])
      = (X^4 - C 10 * X^2 + C 4 : ℚ[X]) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X]
    norm_num
  rw [← heq]
  exact hres

/-- FT cg8a (first clause).  For `f = X⁴ − 4X + 2` with roots `a1, a2, a3, a4` the resolvent
cubic is `X³ − 8X − 16`. -/
theorem cg8a_resolvent_cubic {E : Type u} [Field E] [Algebra ℚ E] (a1 a2 a3 a4 : E)
    (hf : (X : E[X])^4 + C (algebraMap ℚ E 0) * X^3 + C (algebraMap ℚ E 0) * X^2
        + C (algebraMap ℚ E (-4)) * X + C (algebraMap ℚ E 2)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    (X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
      * (X - C (quarticGamma a1 a2 a3 a4))
      = X^3 - C (algebraMap ℚ E 8) * X - C (algebraMap ℚ E 16) := by
  refine (quartic_resolvent_cubic (K := E) a1 a2 a3 a4 (algebraMap ℚ E 0) (algebraMap ℚ E 0)
    (algebraMap ℚ E (-4)) (algebraMap ℚ E 2) hf).trans ?_
  norm_num
  try ring

/-- FT cg9 (first clause).  For `f = X⁴ + 4X² + 2` with roots `a1, a2, a3, a4` the resolvent
cubic is `X³ − 4X² − 8X + 32`, which factors as `(X − 4)(X² − 8)` (see
`cg9_resolvent_factorization`). -/
theorem cg9_resolvent_cubic {E : Type u} [Field E] [Algebra ℚ E] (a1 a2 a3 a4 : E)
    (hf : (X : E[X])^4 + C (algebraMap ℚ E 0) * X^3 + C (algebraMap ℚ E 4) * X^2
        + C (algebraMap ℚ E 0) * X + C (algebraMap ℚ E 2)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    (X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
      * (X - C (quarticGamma a1 a2 a3 a4))
      = X^3 - C (algebraMap ℚ E 4) * X^2 - C (algebraMap ℚ E 8) * X
        + C (algebraMap ℚ E 32) := by
  refine (quartic_resolvent_cubic (K := E) a1 a2 a3 a4 (algebraMap ℚ E 0) (algebraMap ℚ E 4)
    (algebraMap ℚ E 0) (algebraMap ℚ E 2) hf).trans ?_
  norm_num
  try ring

/-- FT cg9 (second clause).  The resolvent cubic `X³ − 4X² − 8X + 32` factors over ℚ as
`(X − 4)(X² − 8)`: expanding and regrouping the constant term `32 = 4 · 8`. -/
theorem cg9_resolvent_factorization {E : Type u} [Field E] [Algebra ℚ E] :
    (X - C (algebraMap ℚ E 4)) * (X^2 - C (algebraMap ℚ E 8))
      = X^3 - C (algebraMap ℚ E 4) * X^2 - C (algebraMap ℚ E 8) * X
        + C (algebraMap ℚ E 32) := by
  rw [show (algebraMap ℚ E 32) = (algebraMap ℚ E 4) * (algebraMap ℚ E 8) by norm_num,
    Polynomial.C_mul]
  ring

/-- FT cg10 (first clause).  For `f = X⁴ − 10X² + 4` with roots `a1, a2, a3, a4` the resolvent
cubic is `X³ + 10X² − 16X − 160`, which factors as `(X + 10)(X + 4)(X − 4)` (see
`cg10_resolvent_factorization`). -/
theorem cg10_resolvent_cubic {E : Type u} [Field E] [Algebra ℚ E] (a1 a2 a3 a4 : E)
    (hf : (X : E[X])^4 + C (algebraMap ℚ E 0) * X^3 + C (algebraMap ℚ E (-10)) * X^2
        + C (algebraMap ℚ E 0) * X + C (algebraMap ℚ E 4)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    (X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
      * (X - C (quarticGamma a1 a2 a3 a4))
      = X^3 + C (algebraMap ℚ E 10) * X^2 - C (algebraMap ℚ E 16) * X
        - C (algebraMap ℚ E 160) := by
  refine (quartic_resolvent_cubic (K := E) a1 a2 a3 a4 (algebraMap ℚ E 0) (algebraMap ℚ E (-10))
    (algebraMap ℚ E 0) (algebraMap ℚ E 4) hf).trans ?_
  norm_num
  try ring

/-- FT cg10 (second clause).  The resolvent cubic `X³ + 10X² − 16X − 160` factors over ℚ as
`(X + 10)(X + 4)(X − 4)`: expanding and regrouping `16 = 4 · 4`, `160 = 10 · 4 · 4`. -/
theorem cg10_resolvent_factorization {E : Type u} [Field E] [Algebra ℚ E] :
    (X + C (algebraMap ℚ E 10)) * (X + C (algebraMap ℚ E 4)) * (X - C (algebraMap ℚ E 4))
      = X^3 + C (algebraMap ℚ E 10) * X^2 - C (algebraMap ℚ E 16) * X
        - C (algebraMap ℚ E 160) := by
  rw [show (algebraMap ℚ E 160) = (algebraMap ℚ E 10) * (algebraMap ℚ E 4) * (algebraMap ℚ E 4)
      by norm_num,
    show (algebraMap ℚ E 16) = (algebraMap ℚ E 4) * (algebraMap ℚ E 4) by norm_num,
    Polynomial.C_mul, Polynomial.C_mul, Polynomial.C_mul]
  ring

/-- FT cg11 (first clause).  For `f = X⁴ − 2` with roots `a1, a2, a3, a4` the resolvent cubic
is `X³ + 8X`. -/
theorem cg11_resolvent_cubic {E : Type u} [Field E] [Algebra ℚ E] (a1 a2 a3 a4 : E)
    (hf : (X : E[X])^4 + C (algebraMap ℚ E 0) * X^3 + C (algebraMap ℚ E 0) * X^2
        + C (algebraMap ℚ E 0) * X + C (algebraMap ℚ E (-2))
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    (X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
      * (X - C (quarticGamma a1 a2 a3 a4)) = X^3 + C (algebraMap ℚ E 8) * X := by
  refine (quartic_resolvent_cubic (K := E) a1 a2 a3 a4 (algebraMap ℚ E 0) (algebraMap ℚ E 0)
    (algebraMap ℚ E 0) (algebraMap ℚ E (-2)) hf).trans ?_
  norm_num
  try ring

/-- FT cg8a (second clause).  `X⁴ − 4X + 2` is irreducible over ℚ by Eisenstein's criterion at
the prime 2. -/
theorem cg8a_irreducible : Irreducible (X^4 - C 4 * X + C 2 : ℚ[X]) := by
  have heq : Polynomial.map (algebraMap ℤ ℚ) (X^4 - C (4:ℤ) * X + C (2:ℤ))
      = (X^4 - C 4 * X + C 2 : ℚ[X]) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X]
    norm_num
  rw [← heq]
  have hX4 : ((X : ℤ[X])^4).natDegree = 4 := by rw [Polynomial.natDegree_X_pow]
  have hCX : (C (4:ℤ) * X : ℤ[X]).natDegree ≤ 1 := by
    have h : (C (4:ℤ) * X : ℤ[X]).natDegree
        ≤ (C (4:ℤ) : ℤ[X]).natDegree + (X : ℤ[X]).natDegree := Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at h
    omega
  have hsub : ((X : ℤ[X])^4 - C (4:ℤ) * X).natDegree
      ≤ max ((X : ℤ[X])^4).natDegree ((C (4:ℤ) * X : ℤ[X]).natDegree) :=
    Polynomial.natDegree_sub_le _ _
  have hd1 : ((X : ℤ[X])^4 - C (4:ℤ) * X).natDegree ≤ 4 := by omega
  have hC2 : (C (2:ℤ) : ℤ[X]).natDegree = 0 := Polynomial.natDegree_C _
  have hadd : ((X : ℤ[X])^4 - C (4:ℤ) * X + C (2:ℤ)).natDegree
      ≤ max ((X : ℤ[X])^4 - C (4:ℤ) * X).natDegree ((C (2:ℤ) : ℤ[X]).natDegree) :=
    Polynomial.natDegree_add_le _ _
  have hnd : ((X : ℤ[X])^4 - C (4:ℤ) * X + C (2:ℤ)).natDegree = 4 :=
    natDegree_eq_of_coeff_ne_zero (le_trans hadd (by omega))
      (by simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]; norm_num)
  refine eisenstein_irreducible (X^4 - C (4:ℤ) * X + C (2:ℤ)) 2 Nat.prime_two ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · intro i hi
    rw [hnd] at hi
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    interval_cases i
    all_goals norm_num
  · rw [hnd]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num

/-- FT cg9 (second clause).  `X⁴ + 4X² + 2` is irreducible over ℚ by Eisenstein's criterion at
the prime 2. -/
theorem cg9_irreducible : Irreducible (X^4 + C 4 * X^2 + C 2 : ℚ[X]) := by
  have heq : Polynomial.map (algebraMap ℤ ℚ) (X^4 + C (4:ℤ) * X^2 + C (2:ℤ))
      = (X^4 + C 4 * X^2 + C 2 : ℚ[X]) := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    norm_num
  rw [← heq]
  have hX4 : ((X : ℤ[X])^4).natDegree = 4 := by rw [Polynomial.natDegree_X_pow]
  have hCX : (C (4:ℤ) * X ^ 2 : ℤ[X]).natDegree ≤ 2 := by
    have h : (C (4:ℤ) * X ^ 2 : ℤ[X]).natDegree
        ≤ (C (4:ℤ) : ℤ[X]).natDegree + ((X : ℤ[X]) ^ 2).natDegree :=
      Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow] at h
    omega
  have hadd1 : ((X : ℤ[X])^4 + C (4:ℤ) * X^2).natDegree
      ≤ max ((X : ℤ[X])^4).natDegree ((C (4:ℤ) * X ^ 2 : ℤ[X]).natDegree) :=
    Polynomial.natDegree_add_le _ _
  have hd1 : ((X : ℤ[X])^4 + C (4:ℤ) * X^2).natDegree ≤ 4 := by omega
  have hC2 : (C (2:ℤ) : ℤ[X]).natDegree = 0 := Polynomial.natDegree_C _
  have hadd2 : ((X : ℤ[X])^4 + C (4:ℤ) * X^2 + C (2:ℤ)).natDegree
      ≤ max ((X : ℤ[X])^4 + C (4:ℤ) * X^2).natDegree ((C (2:ℤ) : ℤ[X]).natDegree) :=
    Polynomial.natDegree_add_le _ _
  have hnd : ((X : ℤ[X])^4 + C (4:ℤ) * X^2 + C (2:ℤ)).natDegree = 4 :=
    natDegree_eq_of_coeff_ne_zero (le_trans hadd2 (by omega))
      (by simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C]; norm_num)
  refine eisenstein_irreducible (X^4 + C (4:ℤ) * X^2 + C (2:ℤ)) 2 Nat.prime_two ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · intro i hi
    rw [hnd] at hi
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    interval_cases i
    all_goals norm_num
  · rw [hnd]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num

/-- FT cg11 (second clause).  `X⁴ − 2` is irreducible over ℚ by Eisenstein's criterion at the
prime 2. -/
theorem cg11_irreducible : Irreducible (X^4 - C 2 : ℚ[X]) := by
  have heq : Polynomial.map (algebraMap ℤ ℚ) (X^4 + C (-(2:ℤ)))
      = (X^4 - C 2 : ℚ[X]) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    norm_num
    ring
  rw [← heq]
  have hX4 : ((X : ℤ[X])^4).natDegree = 4 := by rw [Polynomial.natDegree_X_pow]
  have hC2 : (C (-(2:ℤ)) : ℤ[X]).natDegree = 0 := Polynomial.natDegree_C _
  have hadd : ((X : ℤ[X])^4 + C (-(2:ℤ))).natDegree
      ≤ max ((X : ℤ[X])^4).natDegree ((C (-(2:ℤ)) : ℤ[X]).natDegree) :=
    Polynomial.natDegree_add_le _ _
  have hnd : ((X : ℤ[X])^4 + C (-(2:ℤ))).natDegree = 4 :=
    natDegree_eq_of_coeff_ne_zero (le_trans hadd (by omega))
      (by simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C]; norm_num)
  refine eisenstein_irreducible (X^4 + C (-(2:ℤ))) 2 Nat.prime_two ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · intro i hi
    rw [hnd] at hi
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    interval_cases i
    all_goals norm_num
  · rw [hnd]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
