-- tmp/staging/ch4_w32_cg22.lean — worker w32 (cg22 complete), 46 declarations, ALL
-- REPL-verified in a single lineage; axiom batch: [propext, Classical.choice, Quot.sound]
-- for every declaration (worker re-proved 3 sorry-fallback insertions detected mid-run).
-- Fixes vs draft: added isMonicOfDegree_add_add_two; nested-rcases dispatcher;
-- not_dvd_quad_c1_2_c0_1 direct degree bound (whnf hang fix); irreducible_ZMod3 feeds
-- natDegree = 5 into omega; Equiv.Perm.swap_mul_self → Equiv.swap_mul_self (3×);
-- mul_le_mul_right' → mul_le_mul_left; orderOf tail completed per recorded case analysis;
-- commute_swap_of_cycle3_disjoint: unused hxy binder dropped (call sites updated).
namespace FT

open Polynomial

section FiniteFieldUtility

/-! ### Small utility lemmas -/

/-- FT cg22: coefficient-wise equality for polynomials of bounded degree. -/
theorem coeff_ext_of_natDegree_le {R : Type*} [CommRing R] {p q : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (h : ∀ i ≤ n, p.coeff i = q.coeff i) :
    p = q := by
  refine Polynomial.ext fun i => ?_
  rcases Nat.lt_or_ge i (n + 1) with hi | hi
  · exact h i (by omega)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- FT cg22: every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m : ZMod 2) := ⟨a.val, (ZMod.natCast_zmod_val a).symm⟩
  have hmod : (m : ZMod 2) = ((m % 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq m 2).symm
  obtain ⟨t, ht, he⟩ : ∃ t : ℕ, t < 2 ∧ m % 2 = t := ⟨m % 2, by omega, rfl⟩
  rw [hmod, he]
  rcases (show t = 0 ∨ t = 1 from by omega) with rfl | rfl
  exacts [Or.inl rfl, Or.inr rfl]

/-- FT cg22: every element of `ZMod 3` is `0`, `1` or `2`. -/
theorem zmod3_eq_zero_one_or_two (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m : ZMod 3) := ⟨a.val, (ZMod.natCast_zmod_val a).symm⟩
  have hmod : (m : ZMod 3) = ((m % 3 : ℕ) : ZMod 3) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq m 3).symm
  obtain ⟨t, ht, he⟩ : ∃ t : ℕ, t < 3 ∧ m % 3 = t := ⟨m % 3, by omega, rfl⟩
  rw [hmod, he]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 from by omega) with rfl | rfl | rfl
  exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]

/-- FT cg22: `C a * X + C b` has degree at most `1`. -/
theorem natDegree_C_mul_X_add_C_le {R : Type*} [Semiring R] (a b : R) :
    (C a * X + C b : R[X]).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans ?_
  refine max_le_iff.mpr ⟨?_, ?_⟩
  · exact (natDegree_C_mul_le a X).trans natDegree_X_le
  · simp [natDegree_C]

/-- FT cg22: `X ^ k + C a * X + C b` is monic of degree `k` (for `k ≥ 2`). -/
theorem isMonicOfDegree_X_pow_add_C_mul_X_add_C {R : Type*} [Semiring R] [Nontrivial R] (k : ℕ)
    (a b : R) (hk : 2 ≤ k) : IsMonicOfDegree (X ^ k + C a * X + C b : R[X]) k := by
  rw [add_assoc]
  exact (isMonicOfDegree_X_pow R k).add_right
    ((natDegree_C_mul_X_add_C_le a b).trans_lt (by omega))

/-- FT cg22: `X ^ 2 + C a * X + C b` is monic of degree `2` (special case used throughout
the mod-3 case bash). -/
theorem isMonicOfDegree_add_add_two {R : Type*} [Semiring R] [Nontrivial R] (a b : R) :
    IsMonicOfDegree (X ^ 2 + C a * X + C b : R[X]) 2 :=
  isMonicOfDegree_X_pow_add_C_mul_X_add_C 2 a b (by omega)

/-- FT cg22: `X ^ k - C a * X - C b` is monic of degree `k` (for `k ≥ 2`). -/
theorem isMonicOfDegree_X_pow_sub_C_mul_X_sub_C {R : Type*} [Ring R] [Nontrivial R] (k : ℕ)
    (a b : R) (hk : 2 ≤ k) : IsMonicOfDegree (X ^ k - C a * X - C b : R[X]) k := by
  have h1 : IsMonicOfDegree (X ^ k - C a * X) k :=
    (isMonicOfDegree_X_pow R k).sub
      (((natDegree_C_mul_le a X).trans natDegree_X_le).trans_lt (by omega))
  exact h1.sub ((natDegree_C b).trans_lt (by omega))

/-- FT cg22: `X ^ 3 + C a * X ^ 2 + C b * X + C c` is monic of degree `3`. -/
theorem isMonicOfDegree_X3_add3 {R : Type*} [Semiring R] [Nontrivial R] (a b c : R) :
    IsMonicOfDegree (X ^ 3 + C a * X ^ 2 + C b * X + C c : R[X]) 3 := by
  rw [add_assoc, add_assoc]
  refine (isMonicOfDegree_X_pow R 3).add_right ?_
  have hnd : (C a * X ^ 2 + (C b * X + C c : R[X])).natDegree ≤ 2 := by
    refine (natDegree_add_le _ _).trans (max_le_iff.mpr ⟨?_, ?_⟩)
    · exact (natDegree_C_mul_le a (X ^ 2 : R[X])).trans (natDegree_X_pow 2).le
    · exact (natDegree_C_mul_X_add_C_le b c).trans (by omega)
  exact hnd.trans_lt (by omega)

/-- FT cg22: in `ℤ[X]`, `X ^ 2 + C 1 * X + C 1` is monic of degree `2`. -/
theorem monic_Z_X2_add_X_add_1 : IsMonicOfDegree (X ^ 2 + C 1 * X + C 1 : ℤ[X]) 2 :=
  isMonicOfDegree_X_pow_add_C_mul_X_add_C 2 (1 : ℤ) (1 : ℤ) (by omega)

/-- FT cg22: in `ℤ[X]`, `X ^ 3 + C 1 * X ^ 2 + C 1` is monic of degree `3`. -/
theorem monic_Z_X3_add_X2_add_1 : IsMonicOfDegree (X ^ 3 + C 1 * X ^ 2 + C 1 : ℤ[X]) 3 := by
  rw [add_assoc]
  refine (isMonicOfDegree_X_pow ℤ 3).add_right ?_
  have h1 : (C 1 * X ^ 2 + C 1 : ℤ[X]).natDegree ≤ 2 := by
    refine (natDegree_add_le _ _).trans (max_le_iff.mpr ⟨?_, ?_⟩)
    · exact (natDegree_C_mul_le 1 (X ^ 2 : ℤ[X])).trans (natDegree_X_pow 2).le
    · simp [natDegree_C]
  exact h1.trans_lt (by omega)

/-- FT cg22: a polynomial with a nonzero coefficient is nonzero. -/
theorem ne_zero_of_coeff {R : Type*} [Semiring R] {p : R[X]} {i : ℕ} (h : p.coeff i ≠ 0) :
    p ≠ 0 := by
  intro hp
  rw [hp] at h
  exact h (by simp)

end FiniteFieldUtility

section ZMod2Computations

/-! ### The mod-2 factorization `X⁵ − X − 1 = (X² + X + 1)(X³ + X² + 1)` and
irreducibility of both factors -/

/-- FT cg22: over `ZMod 2`, `map` of `X ^ 5 - X - 1` is `X ^ 5 + C 1 * X + C 1`. -/
theorem map_X5_sub_X_sub_1_ZMod2 :
    map (Int.castRingHom (ZMod 2)) (X ^ 5 - C 1 * X - C 1 : ℤ[X])
      = X ^ 5 + C (1 : ZMod 2) * X + C 1 := by
  refine coeff_ext_of_natDegree_le (n := 5)
    (((Polynomial.Monic.natDegree_map
      (isMonicOfDegree_X_pow_sub_C_mul_X_sub_C 5 (1 : ℤ) (1 : ℤ) (by omega)).monic _).trans
      (isMonicOfDegree_X_pow_sub_C_mul_X_sub_C 5 (1 : ℤ) (1 : ℤ) (by omega)).natDegree_eq).le)
    (isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (1 : ZMod 2) (1 : ZMod 2) (by omega)).natDegree_eq.le
    fun i hi => ?_
  simp only [Polynomial.coeff_map, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
    Polynomial.coeff_add, RingHom.map_one, one_mul]
  interval_cases i <;> decide

/-- FT cg22: over `ZMod 2`, `map` of `X ^ 2 + X + 1` is `X ^ 2 + C 1 * X + C 1`. -/
theorem map_X2_add_X_add_1_ZMod2 :
    map (Int.castRingHom (ZMod 2)) (X ^ 2 + C 1 * X + C 1 : ℤ[X])
      = X ^ 2 + C (1 : ZMod 2) * X + C 1 := by
  refine coeff_ext_of_natDegree_le (n := 2)
    (((Polynomial.Monic.natDegree_map monic_Z_X2_add_X_add_1.monic _).trans
      monic_Z_X2_add_X_add_1.natDegree_eq).le)
    (isMonicOfDegree_X_pow_add_C_mul_X_add_C 2 (1 : ZMod 2) (1 : ZMod 2) (by omega)).natDegree_eq.le
    fun i hi => ?_
  simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
    RingHom.map_one, one_mul]
  interval_cases i <;> decide

/-- FT cg22: over `ZMod 2`, `map` of `X ^ 3 + X ^ 2 + 1` is
`X ^ 3 + C 1 * X ^ 2 + C 0 * X + C 1` (the `C 0 * X` term is the vanishing linear term). -/
theorem map_X3_add_X2_add_1_ZMod2 :
    map (Int.castRingHom (ZMod 2)) (X ^ 3 + C 1 * X ^ 2 + C 1 : ℤ[X])
      = X ^ 3 + C (1 : ZMod 2) * X ^ 2 + C 0 * X + C 1 := by
  refine coeff_ext_of_natDegree_le (n := 3)
    (((Polynomial.Monic.natDegree_map monic_Z_X3_add_X2_add_1.monic _).trans
      monic_Z_X3_add_X2_add_1.natDegree_eq).le)
    (isMonicOfDegree_X3_add3 (1 : ZMod 2) (0 : ZMod 2) (1 : ZMod 2)).natDegree_eq.le
    fun i hi => ?_
  simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
    RingHom.map_one, one_mul]
  interval_cases i <;> decide

/-- FT cg22: over `ZMod 2`, `(X² + X + 1)(X³ + X² + 1) = X⁵ + X + 1`. -/
theorem mod2_factorization_lit :
    (X ^ 2 + C (1 : ZMod 2) * X + C 1) * (X ^ 3 + C (1 : ZMod 2) * X ^ 2 + C 1)
      = X ^ 5 + C (1 : ZMod 2) * X + C 1 := by
  have key : (X ^ 2 + C (1 : ZMod 2) * X + C 1) * (X ^ 3 + C (1 : ZMod 2) * X ^ 2 + C 1)
      = X ^ 5 + X ^ 4 + X ^ 2 + (X ^ 4 + X ^ 3 + X) + (X ^ 3 + X ^ 2 + 1) := by
    simp only [C_1, mul_add, add_mul, one_mul, ← pow_add]
    ring_nf
  refine Polynomial.ext fun n => ?_
  rw [key]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, one_mul,
    Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | (n + 6) => simp

/-- **FT cg22** (mod-2 factorization). Over `ZMod 2`,
`X⁵ − X − 1 = (X² + X + 1)(X³ + X² + 1)`. -/
theorem mod2_factorization_X5_sub_X_sub_1 :
    map (Int.castRingHom (ZMod 2)) (X ^ 5 - C 1 * X - C 1 : ℤ[X])
      = (X ^ 2 + C 1 * X + C 1) * (X ^ 3 + C 1 * X ^ 2 + C 1) := by
  rw [map_X5_sub_X_sub_1_ZMod2]
  exact mod2_factorization_lit.symm

/-- FT cg22: over `ZMod 2`, `X ^ 2 + X + 1` has no root. -/
theorem eval_X2_add_X_add_1_ZMod2_ne (x : ZMod 2) :
    (X ^ 2 + C (1 : ZMod 2) * X + C 1 : (ZMod 2)[X]).eval x ≠ 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    simp only [Polynomial.eval_add, Polynomial.eval_X_pow, Polynomial.eval_C_mul, one_mul,
      Polynomial.eval_X, Polynomial.eval_C] <;>
    decide

/-- FT cg22: over `ZMod 2`, `X ^ 3 + X ^ 2 + 1` has no root. -/
theorem eval_X3_add_X2_add_1_ZMod2_ne (x : ZMod 2) :
    (X ^ 3 + C (1 : ZMod 2) * X ^ 2 + C 0 * X + C 1 : (ZMod 2)[X]).eval x ≠ 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    simp only [Polynomial.eval_add, Polynomial.eval_X_pow, Polynomial.eval_C_mul, one_mul,
      zero_mul, Polynomial.eval_X, Polynomial.eval_C] <;>
    decide

/-- FT cg22: `X² + X + 1` is irreducible over `ZMod 2` (degree 2, no roots). -/
theorem irreducible_X2_add_X_add_1_ZMod2 :
    Irreducible (X ^ 2 + C (1 : ZMod 2) * X + C 1 : (ZMod 2)[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [(isMonicOfDegree_X_pow_add_C_mul_X_add_C 2 (1 : ZMod 2) (1 : ZMod 2)
      (by omega)).natDegree_eq]
    simp
  · exact fun x hx => eval_X2_add_X_add_1_ZMod2_ne x (Polynomial.IsRoot.def.mp hx)

/-- FT cg22: `X³ + X² + 1` is irreducible over `ZMod 2` (degree 3, no roots). -/
theorem irreducible_X3_add_X2_add_1_ZMod2 :
    Irreducible (X ^ 3 + C (1 : ZMod 2) * X ^ 2 + C 0 * X + C 1 : (ZMod 2)[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [(isMonicOfDegree_X3_add3 (1 : ZMod 2) (0 : ZMod 2) (1 : ZMod 2)).natDegree_eq]
    simp
  · exact fun x hx => eval_X3_add_X2_add_1_ZMod2_ne x (Polynomial.IsRoot.def.mp hx)

/-- FT cg22: the quadratic factor of `X⁵ − X − 1` mod 2 is irreducible over `ZMod 2`. -/
theorem irreducible_map_X2_add_X_add_1_ZMod2 :
    Irreducible (map (Int.castRingHom (ZMod 2)) (X ^ 2 + C 1 * X + C 1 : ℤ[X])) := by
  rw [map_X2_add_X_add_1_ZMod2]
  exact irreducible_X2_add_X_add_1_ZMod2

/-- FT cg22: the cubic factor of `X⁵ − X − 1` mod 2 is irreducible over `ZMod 2`. -/
theorem irreducible_map_X3_add_X2_add_1_ZMod2 :
    Irreducible (map (Int.castRingHom (ZMod 2)) (X ^ 3 + C 1 * X ^ 2 + C 1 : ℤ[X])) := by
  rw [map_X3_add_X2_add_1_ZMod2]
  exact irreducible_X3_add_X2_add_1_ZMod2

end ZMod2Computations

section ZMod3Computations

/-! ### Irreducibility of `X⁵ − X − 1` over `ZMod 3`
(no roots in `ZMod 3`, and no monic quadratic divisor — a nine-case check
of explicit remainders). -/

/-- FT cg22: the quintic `X ^ 5 + C 2 * X + C 2` (=` X⁵ − X − 1` over `ZMod 3`)
has no root in `ZMod 3` (values `2, 2, 2` at `0, 1, 2`). -/
theorem eval_X5_add_2X_add_2_ZMod3_ne (x : ZMod 3) :
    (X ^ 5 + C (2 : ZMod 3) * X + C 2 : (ZMod 3)[X]).eval x ≠ 0 := by
  rcases zmod3_eq_zero_one_or_two x with rfl | rfl | rfl <;>
    simp only [Polynomial.eval_add, Polynomial.eval_X_pow, Polynomial.eval_C_mul,
      Polynomial.eval_X, Polynomial.eval_C] <;>
    decide

/-- FT cg22: divisibility contradiction: a monic quadratic `g` dividing
`X ^ 5 + C 2 * X + C 2` together with the congruence `f − r = g * h` (with `r ≠ 0`
of degree ≤ 1) is impossible, since then `g ∣ r` forces `r = 0` by degrees. -/
theorem quad_not_dvd_ZMod3 {g h r : (ZMod 3)[X]} (hg : IsMonicOfDegree g 2)
    (hnr : r ≠ 0) (hrd : r.natDegree ≤ 1)
    (hcong : X ^ 5 + C (2 : ZMod 3) * X + C 2 - r = g * h) :
    ¬ g ∣ (X ^ 5 + C (2 : ZMod 3) * X + C 2) := by
  intro hdvd
  have h1 : g ∣ (X ^ 5 + C (2 : ZMod 3) * X + C 2 - r) := ⟨h, hcong⟩
  have h2 : g ∣ (X ^ 5 + C (2 : ZMod 3) * X + C 2 - (X ^ 5 + C (2 : ZMod 3) * X + C 2 - r)) :=
    dvd_sub hdvd h1
  rw [sub_sub_cancel] at h2
  obtain ⟨k, hk⟩ := h2
  by_cases hk0 : k = 0
  · rw [hk0, mul_zero] at hk
    exact hnr hk
  · have h3 : r.natDegree = g.natDegree + k.natDegree := by
      rw [hk, Polynomial.natDegree_mul hg.monic.ne_zero hk0]
    rw [hg.natDegree_eq] at h3
    exact absurd hrd (by omega)

/-- FT cg22: quadratic-divisor case `c1 = 0`, `c0 = 0` (`g = X²`, quotient `X³`,
remainder `2X + 2`). -/
theorem not_dvd_quad_c1_0_c0_0 :
    ¬ ((X ^ 2 + C 0 * X + C 0 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 0 * X + C 0)
    (h := X ^ 3 + C 0 * X ^ 2 + C 0 * X + C 0) (r := C 2 * X + C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C] <;> decide))
    (natDegree_C_mul_X_add_C_le _ _) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (natDegree_C_mul_X_add_C_le _ _).trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (0 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (0 : ZMod 3) (0 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 0`, `c0 = 1` (`g = X² + 1`, quotient `X³ + 2X`,
remainder `2`). -/
theorem not_dvd_quad_c1_0_c0_1 :
    ¬ ((X ^ 2 + C 0 * X + C 1 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 0 * X + C 1)
    (h := X ^ 3 + C 0 * X ^ 2 + C 2 * X + C 0) (r := C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_C] <;> decide))
    ((Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (0 : ZMod 3) (1 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (0 : ZMod 3) (2 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 0`, `c0 = 2` (`g = X² + 2`, quotient `X³ + X`,
remainder `2`). -/
theorem not_dvd_quad_c1_0_c0_2 :
    ¬ ((X ^ 2 + C 0 * X + C 2 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 0 * X + C 2)
    (h := X ^ 3 + C 0 * X ^ 2 + C 1 * X + C 0) (r := C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_C] <;> decide))
    ((Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (0 : ZMod 3) (2 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (0 : ZMod 3) (1 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 1`, `c0 = 0` (`g = X² + X`, quotient
`X³ + 2X² + X + 2`, remainder `2`). -/
theorem not_dvd_quad_c1_1_c0_0 :
    ¬ ((X ^ 2 + C 1 * X + C 0 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 1 * X + C 0)
    (h := X ^ 3 + C 2 * X ^ 2 + C 1 * X + C 2) (r := C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_C] <;> decide))
    ((Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (1 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (2 : ZMod 3) (1 : ZMod 3) (2 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 1`, `c0 = 1` (`g = X² + X + 1`, quotient
`X³ + 2X² + 1`, remainder `X + 1`). -/
theorem not_dvd_quad_c1_1_c0_1 :
    ¬ ((X ^ 2 + C 1 * X + C 1 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 1 * X + C 1)
    (h := X ^ 3 + C 2 * X ^ 2 + C 0 * X + C 1) (r := C 1 * X + C 1)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C] <;> decide))
    (natDegree_C_mul_X_add_C_le _ _) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (natDegree_C_mul_X_add_C_le _ _).trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (1 : ZMod 3) (1 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (2 : ZMod 3) (0 : ZMod 3) (1 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 1`, `c0 = 2` (`g = X² + X + 2`, quotient
`X³ + 2X² + 2X`, remainder `X + 2`). -/
theorem not_dvd_quad_c1_1_c0_2 :
    ¬ ((X ^ 2 + C 1 * X + C 2 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 1 * X + C 2)
    (h := X ^ 3 + C 2 * X ^ 2 + C 2 * X + C 0) (r := C 1 * X + C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C] <;> decide))
    (natDegree_C_mul_X_add_C_le _ _) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (natDegree_C_mul_X_add_C_le _ _).trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (1 : ZMod 3) (2 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (2 : ZMod 3) (2 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 2`, `c0 = 0` (`g = X² + 2X`, quotient
`X³ + X² + X + 1`, remainder `2`). -/
theorem not_dvd_quad_c1_2_c0_0 :
    ¬ ((X ^ 2 + C 2 * X + C 0 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 2 * X + C 0)
    (h := X ^ 3 + C 1 * X ^ 2 + C 1 * X + C 1) (r := C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_C] <;> decide))
    ((Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (Polynomial.natDegree_C (2 : ZMod 3)).le.trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (2 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (1 : ZMod 3) (1 : ZMod 3) (1 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 2`, `c0 = 1` (`g = X² + 2X + 1`, quotient
`X³ + X² + 2`, remainder `X`). -/
theorem not_dvd_quad_c1_2_c0_1 :
    ¬ ((X ^ 2 + C 2 * X + C 1 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 2 * X + C 1)
    (h := X ^ 3 + C 1 * X ^ 2 + C 0 * X + C 2) (r := C 1 * X)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 1) (by simp only [Polynomial.coeff_C_mul, one_mul,
      Polynomial.coeff_X] <;> decide))
    ((Polynomial.natDegree_C_mul_le (1 : ZMod 3) X).trans natDegree_X_le) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · have h2 : ((C 1 * X : (ZMod 3)[X])).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le 1 X).trans natDegree_X_le
    exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, h2.trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (2 : ZMod 3) (1 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (1 : ZMod 3) (0 : ZMod 3) (2 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: quadratic-divisor case `c1 = 2`, `c0 = 2` (`g = X² + 2X + 2`, quotient
`X³ + X² + 2X`, remainder `X + 2`). -/
theorem not_dvd_quad_c1_2_c0_2 :
    ¬ ((X ^ 2 + C 2 * X + C 2 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  refine quad_not_dvd_ZMod3 (g := X ^ 2 + C 2 * X + C 2)
    (h := X ^ 3 + C 1 * X ^ 2 + C 2 * X + C 0) (r := C 1 * X + C 2)
    (isMonicOfDegree_add_add_two _ _)
    (ne_zero_of_coeff (i := 0) (by simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C] <;> decide))
    (natDegree_C_mul_X_add_C_le _ _) ?_
  refine coeff_ext_of_natDegree_le (n := 5) ?_ ?_ fun i hi => ?_
  · exact (natDegree_sub_le _ _).trans (max_le_iff.mpr
      ⟨(isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3)
        (by omega)).natDegree_eq.le, (natDegree_C_mul_X_add_C_le _ _).trans (by omega)⟩)
  · exact (natDegree_mul_le).trans (by
      have hg := (isMonicOfDegree_add_add_two (2 : ZMod 3) (2 : ZMod 3)).natDegree_eq.le
      have hh := (isMonicOfDegree_X3_add3 (1 : ZMod 3) (2 : ZMod 3) (0 : ZMod 3)).natDegree_eq.le
      omega)
  · interval_cases i <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] <;> decide

/-- FT cg22: no monic quadratic over `ZMod 3` divides `X⁵ − X − 1` (nine-case
remainder check). -/
theorem not_dvd_quad_X5_add_2X_add_2 (c1 c0 : ZMod 3) :
    ¬ ((X ^ 2 + C c1 * X + C c0 : (ZMod 3)[X]) ∣ X ^ 5 + C 2 * X + C 2) := by
  rcases zmod3_eq_zero_one_or_two c1 with rfl | rfl | rfl
  · rcases zmod3_eq_zero_one_or_two c0 with rfl | rfl | rfl
    exacts [not_dvd_quad_c1_0_c0_0, not_dvd_quad_c1_0_c0_1, not_dvd_quad_c1_0_c0_2]
  · rcases zmod3_eq_zero_one_or_two c0 with rfl | rfl | rfl
    exacts [not_dvd_quad_c1_1_c0_0, not_dvd_quad_c1_1_c0_1, not_dvd_quad_c1_1_c0_2]
  · rcases zmod3_eq_zero_one_or_two c0 with rfl | rfl | rfl
    exacts [not_dvd_quad_c1_2_c0_0, not_dvd_quad_c1_2_c0_1, not_dvd_quad_c1_2_c0_2]

/-- FT cg22: `X⁵ − X − 1` is irreducible over `ZMod 3`: no roots, and no quadratic
divisor (a reducible quintic without a linear factor has a factor of degree ≤ 2). -/
theorem irreducible_X5_add_2X_add_2_ZMod3 :
    Irreducible (X ^ 5 + C (2 : ZMod 3) * X + C 2 : (ZMod 3)[X]) := by
  classical
  have hf : IsMonicOfDegree (X ^ 5 + C (2 : ZMod 3) * X + C 2 : (ZMod 3)[X]) 5 :=
    isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3) (by omega)
  rw [Polynomial.irreducible_iff_lt_natDegree_lt hf.monic.ne_zero
    (Polynomial.not_isUnit_of_natDegree_pos _ (by rw [hf.natDegree_eq]; omega))]
  intro q hq hmem hdvd
  have hnd : q.natDegree = 1 ∨ q.natDegree = 2 := by
    have h3 := (Finset.mem_Ioc.mp hmem).1
    have h4 := (Finset.mem_Ioc.mp hmem).2
    have h5 : (X ^ 5 + C 2 * X + C 2 : (ZMod 3)[X]).natDegree = 5 := hf.natDegree_eq
    omega
  rcases hnd with h1 | h1
  · obtain ⟨a, rfl⟩ := Polynomial.isMonicOfDegree_one_iff.mp ⟨h1, hq⟩
    exact (eval_X5_add_2X_add_2_ZMod3_ne (-a)
      (by obtain ⟨k, hk⟩ := hdvd
          rw [hk, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
            Polynomial.eval_C, neg_add_cancel, zero_mul]))
  · obtain ⟨c1, c0, rfl⟩ := Polynomial.isMonicOfDegree_two_iff.mp ⟨h1, hq⟩
    exact not_dvd_quad_X5_add_2X_add_2 c1 c0 hdvd

/-- FT cg22: over `ZMod 3`, `map` of `X ^ 5 - X - 1` is `X ^ 5 + C 2 * X + C 2`. -/
theorem map_X5_sub_X_sub_1_ZMod3 :
    map (Int.castRingHom (ZMod 3)) (X ^ 5 - C 1 * X - C 1 : ℤ[X])
      = X ^ 5 + C (2 : ZMod 3) * X + C 2 := by
  refine coeff_ext_of_natDegree_le (n := 5)
    (((Polynomial.Monic.natDegree_map
      (isMonicOfDegree_X_pow_sub_C_mul_X_sub_C 5 (1 : ℤ) (1 : ℤ) (by omega)).monic _).trans
      (isMonicOfDegree_X_pow_sub_C_mul_X_sub_C 5 (1 : ℤ) (1 : ℤ) (by omega)).natDegree_eq).le)
    (isMonicOfDegree_X_pow_add_C_mul_X_add_C 5 (2 : ZMod 3) (2 : ZMod 3) (by omega)).natDegree_eq.le
    fun i hi => ?_
  simp only [Polynomial.coeff_map, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
    Polynomial.coeff_add, RingHom.map_one, one_mul]
  interval_cases i <;> decide

/-- FT cg22: `X⁵ − X − 1` is irreducible over `ZMod 3`. -/
theorem irreducible_map_X5_sub_X_sub_1_ZMod3 :
    Irreducible (map (Int.castRingHom (ZMod 3)) (X ^ 5 - C 1 * X - C 1 : ℤ[X])) := by
  rw [map_X5_sub_X_sub_1_ZMod3]
  exact irreducible_X5_add_2X_add_2_ZMod3

end ZMod3Computations

section GroupTheory

/-! ### The group-theoretic bridge (FT cg22 ⇒ cg21-style input).
`cycle type (2)(3)` is encoded as a product `τ * ρ` of a transposition `τ` and a
3-cycle `ρ` fixing the two swapped points (hence disjoint from, and commuting
with, `τ`); its cube is the transposition. -/

/-- FT cg22: a transposition `Equiv.swap x y` and a permutation `ρ` fixing both `x` and `y`
commute (their supports are disjoint). -/
theorem commute_swap_of_cycle3_disjoint {α : Type*} [DecidableEq α] {x y : α} {ρ : Equiv.Perm α}
    (hx : ρ x = x) (hy : ρ y = y) : Commute (Equiv.swap x y) ρ := by
  refine Equiv.Perm.Disjoint.commute fun z => ?_
  by_cases hzx : z = x
  · exact Or.inr (by rw [hzx]; exact hx)
  by_cases hzy : z = y
  · exact Or.inr (by rw [hzy]; exact hy)
  · exact Or.inl (Equiv.swap_apply_of_ne_of_ne hzx hzy)

/-- FT cg22: core cube computation: if `τ` is a swap, `ρ` has order `3` and they commute,
then `(τ * ρ)³ = τ` (the 3-cycle part cubes to `1`, the swap part survives). -/
theorem cube_of_commute_isSwap_cycle3 {α : Type*} [DecidableEq α] {τ ρ : Equiv.Perm α}
    (hτ : τ.IsSwap) (hρ3 : orderOf ρ = 3) (hcomm : Commute τ ρ) : (τ * ρ) ^ 3 = τ := by
  obtain ⟨x, y, hxy, rfl⟩ := hτ
  have hτ2 : (Equiv.swap x y) ^ 2 = 1 := by rw [pow_two, Equiv.swap_mul_self]
  have hτ3 : (Equiv.swap x y) ^ 3 = Equiv.swap x y := by rw [pow_succ, hτ2, one_mul]
  have hρ3p : ρ ^ 3 = 1 := by
    have hp := pow_orderOf_eq_one ρ
    rw [hρ3] at hp
    exact hp
  rw [Commute.mul_pow hcomm, hτ3, hρ3p, mul_one]

/-- FT cg22: a swap on distinct points has order `2`. -/
theorem orderOf_swap_eq_two {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    orderOf (Equiv.swap x y) = 2 := by
  have hτ2 : (Equiv.swap x y) ^ 2 = 1 := by rw [pow_two, Equiv.swap_mul_self]
  have hne1 : Equiv.swap x y ≠ 1 := by
    intro h1
    rw [Equiv.Perm.one_def] at h1
    exact hxy (Equiv.swap_eq_refl_iff.mp h1)
  have hne2 : orderOf (Equiv.swap x y) ≠ 1 := by
    intro hc
    rw [orderOf_eq_one_iff.mp hc] at hne1
    exact hne1 rfl
  have h1 : orderOf (Equiv.swap x y) ≤ 2 := orderOf_le_of_pow_eq_one (by omega) hτ2
  have h2 : orderOf (Equiv.swap x y) ≠ 0 := by
    intro h0
    exact orderOf_eq_zero_iff'.mp h0 2 (by omega) hτ2
  omega

/-- FT cg22: the product of a transposition and a disjoint 3-cycle has order `6`
(divides `6` and is not `1`, `2` or `3`; the order analysis is the `k = 0`, `k = 1`,
`k ≥ 2` case split on `6 = orderOf (τ * ρ) * k`). -/
theorem orderOf_swap_mul_cycle3_eq_six {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y)
    {ρ : Equiv.Perm α} (hx : ρ x = x) (hy : ρ y = y) (hρ3 : orderOf ρ = 3) :
    orderOf (Equiv.swap x y * ρ) = 6 := by
  set τ : Equiv.Perm α := Equiv.swap x y with hτdef
  have hcomm : Commute τ ρ := commute_swap_of_cycle3_disjoint hx hy
  have hτ2 : τ ^ 2 = 1 := by rw [hτdef, pow_two, Equiv.swap_mul_self]
  have hτne1 : τ ≠ 1 := by
    intro h1
    rw [hτdef, Equiv.Perm.one_def] at h1
    exact hxy (Equiv.swap_eq_refl_iff.mp h1)
  have hτo : orderOf τ = 2 := orderOf_swap_eq_two hxy
  have hρ3p : ρ ^ 3 = 1 := by
    have hp := pow_orderOf_eq_one ρ
    rw [hρ3] at hp
    exact hp
  have hτ6 : τ ^ 6 = 1 := by rw [show 6 = 2 * 3 from by omega, pow_mul, hτ2, one_pow]
  have hρ6 : ρ ^ 6 = 1 := by rw [show 6 = 3 * 2 from by omega, pow_mul, hρ3p, one_pow]
  have hg6 : (τ * ρ) ^ 6 = 1 := by rw [Commute.mul_pow hcomm 6, hτ6, hρ6, one_mul]
  have hdvd : orderOf (τ * ρ) ∣ 6 := orderOf_dvd_of_pow_eq_one hg6
  have ht0 : orderOf (τ * ρ) ≠ 0 := by
    intro h0
    exact orderOf_eq_zero_iff'.mp h0 6 (by omega) hg6
  have hne1 : orderOf (τ * ρ) ≠ 1 := by
    intro h1
    have heq : τ * ρ = 1 := orderOf_eq_one_iff.mp h1
    have hτe : τ = ρ⁻¹ := eq_inv_of_mul_eq_one_left heq
    have hro : orderOf ρ = 2 := by
      calc orderOf ρ = orderOf ρ⁻¹ := (orderOf_inv ρ).symm
        _ = orderOf τ := by rw [hτe.symm]
        _ = 2 := hτo
    omega
  have hne2 : orderOf (τ * ρ) ≠ 2 := by
    intro h2
    have hp2 : (τ * ρ) ^ 2 = 1 := by
      have hp := pow_orderOf_eq_one (τ * ρ)
      rw [h2] at hp
      exact hp
    rw [Commute.mul_pow hcomm 2, hτ2, one_mul] at hp2
    have hle : orderOf ρ ≤ 2 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hp2)
    omega
  have hne3 : orderOf (τ * ρ) ≠ 3 := by
    intro h3
    have hp3 : (τ * ρ) ^ 3 = 1 := by
      have hp := pow_orderOf_eq_one (τ * ρ)
      rw [h3] at hp
      exact hp
    rw [cube_of_commute_isSwap_cycle3 ⟨x, y, hxy, rfl⟩ hρ3 hcomm] at hp3
    exact hτne1 hp3
  obtain ⟨k, hk⟩ := hdvd
  by_cases hk0 : k = 0
  · rw [hk0, mul_zero] at hk
    omega
  rcases Nat.lt_or_ge k 2 with h5 | h5
  · have hk1 : k = 1 := by omega
    rw [hk1, mul_one] at hk
    omega
  · have h2t : 2 * orderOf (τ * ρ) ≤ k * orderOf (τ * ρ) :=
      mul_le_mul_left h5 (orderOf (τ * ρ))
    rw [mul_comm] at hk
    omega

/-- **FT cg22 bridge.** If `g` is the product of a transposition and a disjoint
3-cycle (cycle type `(2)(3)`), then `g³` is that transposition, and `g` has
order `6`. -/
theorem cube_of_swap_mul_cycle3_eq_swap {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y)
    {ρ : Equiv.Perm α} (hx : ρ x = x) (hy : ρ y = y) (hρ3 : orderOf ρ = 3) :
    (Equiv.swap x y * ρ) ^ 3 = Equiv.swap x y ∧ orderOf (Equiv.swap x y * ρ) = 6 :=
  ⟨cube_of_commute_isSwap_cycle3 ⟨x, y, hxy, rfl⟩ hρ3
      (commute_swap_of_cycle3_disjoint hx hy),
    orderOf_swap_mul_cycle3_eq_six hxy hx hy hρ3⟩

end GroupTheory

section CycleType23

/-- **FT `cg22` (a).** An element of cycle type `(2)(3)`, encoded as the product
`g = Equiv.swap x y * ρ` of a transposition and a 3-cycle `ρ` fixing the swapped points,
cubes to that transposition.

Proof idea: the swap and `ρ` have disjoint supports, hence commute
(`FT.commute_swap_of_cycle3_disjoint`); then `(swap * ρ)³ = swap³ * ρ³ = swap * 1 = swap`
(`FT.cube_of_commute_isSwap_cycle3`). -/
theorem isSwap_of_mem_of_cycleType23 {α : Type*} [DecidableEq α] {g : Equiv.Perm α}
    (h : ∃ x y : α, x ≠ y ∧ ∃ ρ : Equiv.Perm α, ρ x = x ∧ ρ y = y ∧ orderOf ρ = 3 ∧
      g = Equiv.swap x y * ρ) : (g ^ 3).IsSwap := by
  obtain ⟨x, y, hxy, ρ, hx, hy, hρ3, rfl⟩ := h
  rw [cube_of_commute_isSwap_cycle3 ⟨x, y, hxy, rfl⟩ hρ3
    (commute_swap_of_cycle3_disjoint hx hy)]
  exact ⟨x, y, hxy, rfl⟩

end CycleType23

section TopOfSwapPrime

/-- **FT `cg22` (b).** A subgroup of the symmetric group on a `p`-element type (`p` prime)
containing a `p`-cycle and a transposition is the full symmetric group.

Proof idea: the delivered FT `cg12` (`FT.closure_transposition_prime_cycle`) shows the closure
of the two generators is all of `Equiv.Perm α`; both lie in `H`, so the closure is contained
in `H`, whence `H = ⊤` (`le_antisymm`). -/
theorem top_of_swap_and_primeCycle {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Equiv.Perm α)} {p : ℕ} (hp : p.Prime) (hcard : Fintype.card α = p)
    (h5 : ∃ σ ∈ H, orderOf σ = p) (hsw : ∃ τ ∈ H, τ.IsSwap) : H = ⊤ := by
  obtain ⟨σ, hσH, hσ⟩ := h5
  obtain ⟨τ, hτH, hτ⟩ := hsw
  have hsub : Subgroup.closure ({σ, τ} : Set (Equiv.Perm α)) ≤ H := by
    rw [Subgroup.closure_le]
    intro π hπ
    rcases Set.mem_insert_iff.mp hπ with rfl | hπ
    · exact hσH
    · rw [Set.mem_singleton_iff] at hπ
      rw [hπ]
      exact hτH
  refine le_antisymm le_top ?_
  rw [← closure_transposition_prime_cycle hp hcard hσ hτ]
  exact hsub

end TopOfSwapPrime

section Cg22Assembly

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- **FT `cg22` (assembly helper).** If the roots of `f` in `E` admit an injective
enumeration `r : Fin 5 → E` whose range is the root set, then the root set is a 5-element
type.

Proof idea: `r` lifts to a bijection `Fin 5 ≃ ↥(f.rootSet E)` (injectivity from `hr`,
surjectivity from the range hypothesis), and bijective maps preserve `Fintype.card`
(`Fintype.card_of_bijective`). -/
theorem card_rootSet_eq_five_of_injective_enumeration {f : F[X]}
    (r : Fin 5 → E) (hr : Function.Injective r) (hrange : Set.range r = f.rootSet E) :
    Fintype.card ↥(f.rootSet E) = 5 := by
  classical
  have hmem : ∀ i, r i ∈ f.rootSet E := fun i => by rw [← hrange]; exact Set.mem_range_self i
  have hRbij : Function.Bijective (fun i : Fin 5 => (⟨r i, hmem i⟩ : ↥(f.rootSet E))) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hr (congrArg Subtype.val hab)
    · intro y
      obtain ⟨i, hi⟩ : (y : E) ∈ Set.range r := by rw [hrange]; exact y.2
      exact ⟨i, Subtype.ext hi⟩
  exact (Fintype.card_of_bijective hRbij).symm.trans (Fintype.card_fin 5)

end Cg22Assembly

section Cg22Main

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E] [FiniteDimensional F E]

/-- **FT `cg22` (assembly; the cg20 reduction and the cg21 cycle-type input are supplied as
hypotheses).** Let `E/F` be a finite Galois splitting-field-type extension in which a
polynomial `f ∈ F[X]` splits with exactly five roots generating `E`, and suppose the image
`H ⊆ Equiv.Perm ↥(f.rootSet E)` of the Galois group under its action on the root set
(`MulAction.toPermHom`) contains
* an element `φ σ` of order `5` (the 5-cycle, delivered by cg21 from the mod-3
  irreducibility of `X⁵ − X − 1` — for the concrete quintic the irreducibility over the base
  field and hence the transitivity producing this 5-cycle is **upstream cg20/cg21 business,
  not proved here**), and
* an element `φ g` of cycle type `(2)(3)` in the sense of
  `FT.isSwap_of_mem_of_cycleType23` (delivered by cg21 from the mod-2 factorization
  `X⁵ − X − 1 ≡ (X² + X + 1)(X³ + X² + 1)`).

Then the action on the roots is an isomorphism `Gal(E/F) ≅ S₅`, so
`Nat.card Gal(E/F) = 120 = 5!`.

Proof idea: `φ g = swap x y * ρ` with `ρ` a 3-cycle fixing `x, y`, so `(φ g)³ = swap x y`
(`FT.cube_of_commute_isSwap_cycle3`) lies in `H` together with `φ σ`; by
`FT.top_of_swap_and_primeCycle` (FT cg12) `H = ⊤`, i.e. `φ` is surjective, and `φ` is
injective by `FT.gal_inj_on_rootSet` (faithfulness of the action on a root-generated
extension). Hence `φ` is bijective and
`Nat.card Gal(E/F) = Fintype.card (Equiv.Perm ↥(f.rootSet E)) = 5! = 120`
(`Fintype.card_of_bijective`, `Fintype.card_perm`). -/
theorem natCard_gal_eq_120_of_cycleType23 {f : F[X]} [DecidableEq ↥(f.rootSet E)]
    (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤)
    (hcard : Fintype.card ↥(f.rootSet E) = 5)
    (h5 : ∃ σ : Gal(E/F), orderOf ((MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) σ) = 5)
    (h23 : ∃ g : Gal(E/F), ∃ x y : ↥(f.rootSet E), x ≠ y ∧ ∃ ρ : Equiv.Perm ↥(f.rootSet E),
      ρ x = x ∧ ρ y = y ∧ orderOf ρ = 3 ∧
      (MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) g = Equiv.swap x y * ρ) :
    Nat.card Gal(E/F) = 120 := by
  classical
  obtain ⟨g, x, y, hxy, ρ, hx, hy, hρ3, hg⟩ := h23
  obtain ⟨σ, hσ5⟩ := h5
  set φ : Gal(E/F) →* Equiv.Perm ↥(f.rootSet E) :=
    MulAction.toPermHom Gal(E/F) ↥(f.rootSet E) with hφdef
  have hswap : (Equiv.swap x y).IsSwap := ⟨x, y, hxy, rfl⟩
  have hcube : (φ g) ^ 3 = Equiv.swap x y := by
    rw [hg]
    exact cube_of_commute_isSwap_cycle3 ⟨x, y, hxy, rfl⟩ hρ3
      (commute_swap_of_cycle3_disjoint hx hy)
  have hswap_mem : Equiv.swap x y ∈ φ.range := by
    refine ⟨g ^ 3, ?_⟩
    rw [map_pow, hcube]
  have hσ_mem : φ σ ∈ φ.range := ⟨σ, rfl⟩
  have htop := top_of_swap_and_primeCycle (p := 5) (by norm_num) hcard
    ⟨φ σ, hσ_mem, hσ5⟩ ⟨Equiv.swap x y, hswap_mem, hswap⟩
  have hinj : Function.Injective ⇑φ := fun a b hab => gal_inj_on_rootSet hgen a b hab
  have hbij : Function.Bijective ⇑φ := ⟨hinj, MonoidHom.range_eq_top.mp htop⟩
  calc Nat.card Gal(E/F) = Fintype.card Gal(E/F) := Nat.card_eq_fintype_card
    _ = Fintype.card (Equiv.Perm ↥(f.rootSet E)) := Fintype.card_of_bijective hbij
    _ = (Fintype.card ↥(f.rootSet E)).factorial := Fintype.card_perm
    _ = (5 : ℕ).factorial := by rw [hcard]
    _ = 120 := by norm_num

end Cg22Main

end FT
