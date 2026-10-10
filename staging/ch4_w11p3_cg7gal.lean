-- STAGING: FT ch. IV quartic core, worker w11 deliverable PART 3 (Galois section, cg7,
-- plus cg8 coefficient statements), collected verbatim. REPL-verified by w11.
-- Depends on w11 parts 1–2 (lost, being re-derived): quarticAlpha/Beta/Gamma,
-- quarticResolventSet, quartic_resolvent_cubic, quartic_vieta.

section QuarticResolventGalois

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- A point `y` is a root of the split cubic `(X − u)(X − v)(X − w)` iff it is one of
`u, v, w`. -/
theorem eval_prod3_eq_zero_iff (u v w y : E) :
    ((X - C u) * (X - C v) * (X - C w)).eval y = 0 ↔ y = u ∨ y = v ∨ y = w := by
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    mul_eq_zero, sub_eq_zero]
  tauto

/-- FT `cg8`.  Coefficients of the resolvent cubic: the coefficient of `X^n` in
`(X − α)(X − β)(X − γ)` is `1`, `−c`, `bd − 4e`, `−b²e + 4ce − d²` for `n = 3, 2, 1, 0` and
`0` otherwise, where `b, c, d, e` are the quartic's coefficients. -/
theorem quartic_resolvent_coeff (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) (n : ℕ) :
    ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff n
      = if n = 3 then 1
        else if n = 2 then -(algebraMap F E c)
        else if n = 1 then algebraMap F E b * algebraMap F E d - 4 * algebraMap F E e
        else if n = 0 then -(algebraMap F E b^2 * algebraMap F E e)
            + 4 * algebraMap F E c * algebraMap F E e - algebraMap F E d^2
        else 0 := by
  rw [quartic_resolvent_cubic (K := E) a1 a2 a3 a4 (algebraMap F E b) (algebraMap F E c)
    (algebraMap F E d) (algebraMap F E e) hf]
  rcases n with _ | _ | _ | _ | n
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    norm_num
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    have h3 : ¬ (n + 1 + 1 + 1 + 1 = 3) := by omega
    have h2 : ¬ (n + 1 + 1 + 1 + 1 = 2) := by omega
    have h1 : ¬ (1 = n + 1 + 1 + 1 + 1) := by omega
    have h0 : ¬ (n + 1 + 1 + 1 + 1 = 0) := by omega
    simp only [if_neg h3, if_neg h2, if_neg h1, if_neg h0]
    norm_num

/-- FT `cg8` (discussion).  Every element of `Gal(E/F)` fixes the coefficients of the
resolvent cubic. -/
theorem quartic_resolvent_gal_coeff (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4))
    (σ : Gal(E/F)) (n : ℕ) :
    σ (((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff n)
      = ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff n := by
  have c3 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 3 = 1 := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 3]; norm_num
  have c2 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 2 = -(algebraMap F E c) := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 2]; norm_num
  have c1 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 1
        = algebraMap F E b * algebraMap F E d - 4 * algebraMap F E e := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 1]; norm_num
  have c0 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 0
        = -(algebraMap F E b^2 * algebraMap F E e) + 4 * algebraMap F E c * algebraMap F E e
          - algebraMap F E d^2 := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 0]; norm_num
  have cN : ∀ m, 4 ≤ m → ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff m = 0 := by
    intro m hm
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf m]
    split_ifs with h1 h2 h3 h4
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · exact absurd h3 (by omega)
    · exact absurd h4 (by omega)
    · rfl
  rcases n with _ | _ | _ | _ | m
  · rw [c0]
    simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat, AlgEquiv.commutes]
  · rw [c1]
    simp only [map_sub, map_mul, map_ofNat, AlgEquiv.commutes]
  · rw [c2]
    simp only [map_neg, AlgEquiv.commutes]
  · rw [c3]
    simp
  · rw [cN (m + 4) (by omega)]
    simp

/-- FT `cg7` (discussion).  Every element of `Gal(E/F)` permutes the set `{α, β, γ}` of
partially symmetric elements. -/
theorem quartic_resolvent_gal_permutes (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4))
    (σ : Gal(E/F)) :
    ∀ x ∈ quarticResolventSet a1 a2 a3 a4,
      (↑σ : E →ₐ[F] E) x ∈ quarticResolventSet a1 a2 a3 a4 := by
  have hcoef := quartic_resolvent_gal_coeff a1 a2 a3 a4 b c d e hf σ
  have htrans : ∀ x : E, σ (((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval x)
      = ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (σ x) := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, map_sum σ]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_mul, map_pow, hcoef i]
  intro x hx
  simp only [quarticResolventSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  have hrw : ∀ z : E, z = quarticAlpha a1 a2 a3 a4 ∨ z = quarticBeta a1 a2 a3 a4 ∨
      z = quarticGamma a1 a2 a3 a4 →
      ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval z = 0 := by
    rintro z (rfl | rfl | rfl) <;>
      simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hroot : ∀ z : E, ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval z = 0 →
      z = quarticAlpha a1 a2 a3 a4 ∨ z = quarticBeta a1 a2 a3 a4 ∨ z = quarticGamma a1 a2 a3 a4 :=
    fun z hz => (eval_prod3_eq_zero_iff _ _ _ _).mp hz
  rcases hx with rfl | rfl | rfl
  · have h1 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (quarticAlpha a1 a2 a3 a4) = 0 :=
      hrw _ (Or.inl rfl)
    have h2 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (σ (quarticAlpha a1 a2 a3 a4)) = 0 := by
      rw [← htrans (quarticAlpha a1 a2 a3 a4), h1, map_zero]
    exact hroot _ h2
  · have h1 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (quarticBeta a1 a2 a3 a4) = 0 :=
      hrw _ (Or.inr (Or.inl rfl))
    have h2 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (σ (quarticBeta a1 a2 a3 a4)) = 0 := by
      rw [← htrans (quarticBeta a1 a2 a3 a4), h1, map_zero]
    exact hroot _ h2
  · have h1 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (quarticGamma a1 a2 a3 a4) = 0 :=
      hrw _ (Or.inr (Or.inr rfl))
    have h2 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).eval (σ (quarticGamma a1 a2 a3 a4)) = 0 := by
      rw [← htrans (quarticGamma a1 a2 a3 a4), h1, map_zero]
    exact hroot _ h2

/-- FT `cg7` (discussion).  `Gal(E/F)` preserves the set `{α, β, γ}` setwise. -/
theorem quartic_resolvent_gal_image (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4))
    (σ : Gal(E/F)) :
    (↑σ : E →ₐ[F] E) '' quarticResolventSet a1 a2 a3 a4 = quarticResolventSet a1 a2 a3 a4 := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, hx, rfl⟩
    exact quartic_resolvent_gal_permutes a1 a2 a3 a4 b c d e hf σ x hx
  · intro y hy
    exact ⟨(↑(σ⁻¹ : Gal(E/F)) : E →ₐ[F] E) y,
      quartic_resolvent_gal_permutes a1 a2 a3 a4 b c d e hf σ⁻¹ y hy,
      AlgEquiv.apply_symm_apply σ y⟩

variable [IsGalois F E] [FiniteDimensional F E]

/-- FT `cg7` (discussion).  `Gal(E/F)` fixes the intermediate field `F[α, β, γ]` as a
whole. -/
theorem quartic_resolvent_gal_map_adjoin (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4))
    (σ : Gal(E/F)) :
    IntermediateField.map (↑σ : E →ₐ[F] E)
        (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))
      = IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4) := by
  rw [IntermediateField.adjoin_map F _ (↑σ : E →ₐ[F] E),
    quartic_resolvent_gal_image a1 a2 a3 a4 b c d e hf σ]

/-- FT `cg7`.  The subgroup `W` of `G_f = Gal(E/F)` fixing `F[α, β, γ]` pointwise is normal
in `Gal(E/F)`. -/
theorem quartic_resolvent_fixingSubgroup_normal (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup.Normal := by
  have hmap : ∀ σ : Gal(E/F), IntermediateField.map (↑σ : E →ₐ[F] E)
      (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))
      = IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4) := fun σ =>
    quartic_resolvent_gal_map_adjoin a1 a2 a3 a4 b c d e hf σ
  constructor
  · intro x hx g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ IntermediateField.map (↑g : E →ₐ[F] E)
        (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)) := by
      rw [hmap g]; exact hy
    obtain ⟨y', hy'm, hy'eq⟩ :=
      (IntermediateField.mem_map
        (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))).mp hy'
    have hgy : (g⁻¹ : Gal(E/F)) y = y' := by
      rw [← hy'eq]
      exact AlgEquiv.symm_apply_apply g y'
    have hfix : (x : Gal(E/F)) y' = y' :=
      ((IntermediateField.mem_fixingSubgroup_iff
        (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))) x).mp hx y' hy'm
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hgy, hfix]
    exact hy'eq

/-- FT `cg7` (first clause).  The fixed field of the subgroup `W` fixing `F[α, β, γ]`
pointwise is `F[α, β, γ]` itself. -/
theorem quartic_resolvent_fixedField (a1 a2 a3 a4 : E) :
    IntermediateField.fixedField
        (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup
      = IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4) :=
  FT.galCorr_fixedField_fixingSubgroup _

/-- FT `cg7` (second clause, Galois part).  `F[α, β, γ]` is Galois over `F`. -/
theorem quartic_resolvent_isGalois (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) :
    IsGalois F ↥(IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)) := by
  haveI : (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup.Normal :=
    quartic_resolvent_fixingSubgroup_normal a1 a2 a3 a4 b c d e hf
  have h := FT.galCorr_isGalois_fixedField_of_normal
    (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup
  rw [FT.galCorr_fixedField_fixingSubgroup
    (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))] at h
  exact h

/-- FT `cg7` (second clause, quotient part).  `Gal(F[α, β, γ]/F) ≅ G_f/W`. -/
noncomputable def quartic_resolvent_quotientEquiv (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4))
    [hN : (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup.Normal] :
    Gal(↥(IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))/F)
      ≃* Gal(E/F) ⧸ (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup := by
  have h := FT.galCorrQuotientEquiv
    (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4)).fixingSubgroup
  rw [FT.galCorr_fixedField_fixingSubgroup
    (IntermediateField.adjoin F (quarticResolventSet a1 a2 a3 a4))] at h
  exact h

/-- FT `cg8`/discussion.  The resolvent cubic has coefficients in `F`. -/
theorem quartic_resolvent_coeff_mem (a1 a2 a3 a4 : E) (b c d e : F)
    (hf : (X : E[X])^4 + C (algebraMap F E b) * X^3 + C (algebraMap F E c) * X^2
        + C (algebraMap F E d) * X + C (algebraMap F E e)
      = (X - C a1) * (X - C a2) * (X - C a3) * (X - C a4)) (n : ℕ) :
    ∃ z : F, ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff n = algebraMap F E z := by
  have hc0 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 0
      = -(algebraMap F E b^2 * algebraMap F E e) + 4 * algebraMap F E c * algebraMap F E e
        - algebraMap F E d^2 := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 0]; norm_num
  have hc1 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 1
      = algebraMap F E b * algebraMap F E d - 4 * algebraMap F E e := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 1]; norm_num
  have hc2 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 2 = -(algebraMap F E c) := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 2]; norm_num
  have hc3 : ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff 3 = 1 := by
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf 3]; norm_num
  have hcN : ∀ m, 4 ≤ m → ((X - C (quarticAlpha a1 a2 a3 a4)) * (X - C (quarticBeta a1 a2 a3 a4))
        * (X - C (quarticGamma a1 a2 a3 a4))).coeff m = 0 := by
    intro m hm
    rw [quartic_resolvent_coeff a1 a2 a3 a4 b c d e hf m]
    split_ifs with h1 h2 h3 h4
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · exact absurd h3 (by omega)
    · exact absurd h4 (by omega)
    · rfl
  have hz0 : algebraMap F E (-(b^2 * e) + 4 * c * e - d^2)
      = -(algebraMap F E b^2 * algebraMap F E e) + 4 * algebraMap F E c * algebraMap F E e
        - algebraMap F E d^2 := by
    simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat]
  have hz1 : algebraMap F E (b * d - 4 * e)
      = algebraMap F E b * algebraMap F E d - 4 * algebraMap F E e := by
    simp only [map_mul, map_sub, map_ofNat]
  rcases n with _ | _ | _ | _ | m
  · exact ⟨-(b^2 * e) + 4 * c * e - d^2, by rw [hc0, hz0]⟩
  · exact ⟨b * d - 4 * e, by rw [hc1, hz1]⟩
  · exact ⟨-c, by rw [hc2, map_neg (algebraMap F E)]⟩
  · exact ⟨1, by rw [hc3, map_one]⟩
  · exact ⟨0, by rw [hcN (m + 1 + 1 + 1 + 1) (by omega), map_zero]⟩

end QuarticResolventGalois
