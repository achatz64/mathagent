-- staging/ch4_w24_ftXT.lean — worker w24, delivered verbatim.
-- FT IV §8: Galois-invariance of the van der Waerden product f(X,T) (cg20/cg25 setup).
-- Notes: Theorem A (rename-invariance) skipped as instructed (not needed); strong Theorem C
-- delivered (monic degree m! descent). API notes: MvPolynomial.finset_sum_coeff gone
-- (own mvcoeff_finset_sum); Polynomial.finset_sum_coeff → finsetSum_coeff;
-- Polynomial.le_natDegree → le_natDegree_of_ne_zero; natDegree_le_of_coeff_eq_zero →
-- natDegree_le_iff_coeff_eq_zero.mpr. End-to-end verified (temp W-suffixes, stripped here);
-- axioms: propext, Classical.choice, Quot.sound only.
namespace FT

/-! ## FT IV §8: Galois-invariance of the van der Waerden product `f(X,T)` (cg20/cg25) -/

section DedekindThetaProduct

open Polynomial Equiv

variable {m : ℕ} {R : Type*} [CommRing R]

/-- Reindexing lemma: permuting the index set of the product over all root permutations
along the equiv `ρ ↦ τ.symm.trans ρ` (the involution `ρ ↦ ρ.symm` followed by
post-composition with `τ`) leaves the product unchanged. -/
theorem prod_perm_equiv {R : Type*} [CommRing R] (G : Equiv.Perm (Fin m) → Polynomial R)
    (τ : Equiv.Perm (Fin m)) :
    ∏ ρ : Equiv.Perm (Fin m), G (τ.symm.trans ρ) = ∏ ρ : Equiv.Perm (Fin m), G ρ := by
  refine Finset.prod_bij (fun ρ _ => τ.symm.trans ρ) (fun a _ => Finset.mem_univ _) ?_
    (fun b _ => ⟨τ.trans b, Finset.mem_univ _, ?_⟩) (fun a _ => rfl)
  · intro a₁ _ a₂ _ h
    have h2 : τ.trans (τ.symm.trans a₁) = τ.trans (τ.symm.trans a₂) := by rw [h]
    rw [← Equiv.trans_assoc, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans] at h2
    exact h2
  · rw [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]

/-- **FT IV §8 (van der Waerden/Dedekind setup, cg20/cg25):** the polynomial
`f(X,T) = ∏_{σ ∈ S_m} (X − σ_T θ)` in `Polynomial (MvPolynomial (Fin m) R)`, where
`θ = T₁α₁ + ⋯ + T_mα_m` is `dedekindTheta α` and the `T`-permutation `σ_T` acts on `θ`
as `dedekindTheta (α ∘ σ.symm)` (FT `dedekindTheta_rename`). -/
noncomputable def dedekindThetaProduct (α : Fin m → R) : Polynomial (MvPolynomial (Fin m) R) :=
  ∏ ρ : Equiv.Perm (Fin m), (Polynomial.X - Polynomial.C (dedekindTheta (α ∘ ρ.symm)))

/-- A ring endomorphism `σ : R →+* R` permuting the root list `α` (via `τ`) maps the
linear factor with index `ρ` to the factor with index `τ.symm.trans ρ`: the factors of
`f(X,T)` are permuted. -/
theorem map_dedekindTheta_factor (σ : R →+* R) (α : Fin m → R) (τ : Equiv.Perm (Fin m))
    (h : ∀ i, σ (α i) = α (τ i)) (ρ : Equiv.Perm (Fin m)) :
    MvPolynomial.map σ (dedekindTheta (α ∘ ρ.symm)) = dedekindTheta (α ∘ ⇑(τ.symm.trans ρ).symm) := by
  rw [map_dedekindTheta]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [Equiv.symm_trans, Equiv.symm_symm, Equiv.trans_apply]
  exact h _

/-- **FT IV §8, Galois-invariance of the factor set:** if the ring endomorphism `σ`
permutes the root list `α` (σ(αᵢ) = α_{τ(i)}), then `σ` fixes `f(X,T)`: it only
permutes the linear factors of the product. -/
theorem map_dedekindThetaProduct (σ : R →+* R) (α : Fin m → R) (τ : Equiv.Perm (Fin m))
    (h : ∀ i, σ (α i) = α (τ i)) :
    Polynomial.map (MvPolynomial.map σ) (dedekindThetaProduct α) = dedekindThetaProduct α := by
  unfold dedekindThetaProduct
  rw [Polynomial.map_prod]
  have hpt : ∀ ρ : Equiv.Perm (Fin m),
      Polynomial.map (MvPolynomial.map σ) (X - C (dedekindTheta (α ∘ ρ.symm))) =
      (X - C (dedekindTheta (α ∘ ⇑(τ.symm.trans ρ).symm))) := by
    intro ρ
    rw [Polynomial.map_sub, Polynomial.map_X (MvPolynomial.map σ),
      Polynomial.map_C (MvPolynomial.map σ), map_dedekindTheta_factor σ α τ h ρ]
  calc ∏ ρ : Equiv.Perm (Fin m),
        Polynomial.map (MvPolynomial.map σ) (X - C (dedekindTheta (α ∘ ρ.symm)))
      = ∏ ρ : Equiv.Perm (Fin m), (X - C (dedekindTheta (α ∘ ⇑(τ.symm.trans ρ).symm))) :=
        Finset.prod_congr rfl (fun ρ _ => hpt ρ)
    _ = ∏ ρ : Equiv.Perm (Fin m), (X - C (dedekindTheta (α ∘ ρ.symm))) :=
        prod_perm_equiv (fun ω => (X - C (dedekindTheta (α ∘ ω.symm)))) τ

/-- Coefficients are additive: the coefficient of a finite sum of multivariate
polynomials is the sum of the coefficients. -/
theorem mvcoeff_finset_sum {R σ : Type*} [CommSemiring R] [DecidableEq σ] {ι : Type*}
    (d : σ →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    MvPolynomial.coeff d (∑ a ∈ s, f a) = ∑ a ∈ s, MvPolynomial.coeff d (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, MvPolynomial.coeff_add, ih]

end DedekindThetaProduct

section DedekindThetaGalois

open Polynomial Equiv

variable {m : ℕ} {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
  [FiniteDimensional F E]

/-- A scalar of `E` fixed by every `F`-automorphism lies in the image of
`algebraMap F E`: the fixed field of Gal(E/F) is `F` (Artin, via
`IsGalois.fixedField_top` and `IntermediateField.mem_bot`). -/
theorem gal_fixed_mem_range (c : E) (hc : ∀ σ : E ≃ₐ[F] E, σ c = c) :
    c ∈ Set.range (algebraMap F E) := by
  have h1 : c ∈ IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro s _
    exact hc s
  rw [IsGalois.fixedField_top] at h1
  exact IntermediateField.mem_bot.mp h1

/-- A multivariate polynomial over `E` fixed coefficientwise by Gal(E/F) descends to
`F[T₁,…,T_m]`: pick `F`-preimages of the (finitely many) fixed monomial coefficients
and reassemble the polynomial as a sum of monomials. -/
theorem exists_mvPolynomialF_of_gal_fixed (c : MvPolynomial (Fin m) E)
    (hc : ∀ σ : E ≃ₐ[F] E, MvPolynomial.map (σ.toRingHom) c = c) :
    ∃ q : MvPolynomial (Fin m) F, MvPolynomial.map (algebraMap F E) q = c := by
  have hcoeff : ∀ d : Fin m →₀ ℕ, MvPolynomial.coeff d c ∈ Set.range (algebraMap F E) := by
    intro d
    refine gal_fixed_mem_range _ (fun σ => ?_)
    have h1 : MvPolynomial.coeff d (MvPolynomial.map (σ.toRingHom) c)
        = MvPolynomial.coeff d c := by rw [hc σ]
    rwa [MvPolynomial.coeff_map] at h1
  choose g hg using fun d => Set.mem_range.mp (hcoeff d)
  refine ⟨∑ d ∈ c.support, MvPolynomial.monomial d (g d), ?_⟩
  apply MvPolynomial.ext
  intro d
  rw [map_sum (MvPolynomial.map (algebraMap F E)),
    mvcoeff_finset_sum d c.support
      (fun d' => MvPolynomial.map (algebraMap F E) (MvPolynomial.monomial d' (g d')))]
  simp only [MvPolynomial.map_monomial, MvPolynomial.coeff_monomial]
  by_cases hd : d ∈ c.support
  · rw [Finset.sum_eq_single d (fun b _ hb => if_neg hb) (fun h => absurd hd h)]
    rw [if_pos rfl, hg d]
  · rw [Finset.sum_eq_zero (fun b hb => if_neg (fun h => hd (by rw [← h]; exact hb)))]
    have h0 : MvPolynomial.coeff d c = 0 := not_not.mp (MvPolynomial.mem_support_iff.not.mp hd)
    rw [h0]

omit [IsGalois F E] [FiniteDimensional F E] in
/-- **FT IV §8, Theorem B (ii):** when the root list `α` is Galois-stable (each
`σ ∈ Gal(E/F)` permutes it), every `X`-coefficient of `f(X,T) = dedekindThetaProduct α`
— itself an element of `E[T₁,…,T_m]` — is fixed by the Galois action on coefficients. -/
theorem dedekindThetaProduct_coeff_fixed (α : Fin m → E)
    (hstab : ∀ σ : E ≃ₐ[F] E, ∃ τ : Equiv.Perm (Fin m), ∀ i, σ (α i) = α (τ i))
    (σ : E ≃ₐ[F] E) (n : ℕ) :
    MvPolynomial.map (σ.toRingHom) ((dedekindThetaProduct α).coeff n)
      = (dedekindThetaProduct α).coeff n := by
  obtain ⟨τ, hτ⟩ := hstab σ
  rw [← Polynomial.coeff_map, map_dedekindThetaProduct σ.toRingHom α τ hτ]

/-- Every monomial coefficient (in the `T`-variables) of every `X`-coefficient of
`f(X,T)` lies in the image of `algebraMap F E`, i.e. is a Galois-invariant element
of `E` (hence of `F`, embedded in `E`). -/
theorem dedekindThetaProduct_monomialCoeff_mem_range (α : Fin m → E)
    (hstab : ∀ σ : E ≃ₐ[F] E, ∃ τ : Equiv.Perm (Fin m), ∀ i, σ (α i) = α (τ i))
    (n : ℕ) (d : Fin m →₀ ℕ) :
    MvPolynomial.coeff d ((dedekindThetaProduct α).coeff n) ∈ Set.range (algebraMap F E) := by
  refine gal_fixed_mem_range _ (fun σ => ?_)
  have h1 : MvPolynomial.coeff d
      (MvPolynomial.map (σ.toRingHom) ((dedekindThetaProduct α).coeff n))
      = MvPolynomial.coeff d ((dedekindThetaProduct α).coeff n) := by
    rw [dedekindThetaProduct_coeff_fixed α hstab σ n]
  rwa [MvPolynomial.coeff_map] at h1

/-- **FT IV §8, Theorem B (iii):** every `X`-coefficient of `f(X,T)` is the image of a
polynomial `q ∈ F[T₁,…,T_m]`, i.e. lies in the range of `MvPolynomial.map (algebraMap F E)`. -/
theorem exists_mvPolynomialF_dedekindThetaProduct_coeff (α : Fin m → E)
    (hstab : ∀ σ : E ≃ₐ[F] E, ∃ τ : Equiv.Perm (Fin m), ∀ i, σ (α i) = α (τ i))
    (n : ℕ) :
    ∃ q : MvPolynomial (Fin m) F,
      MvPolynomial.map (algebraMap F E) q = (dedekindThetaProduct α).coeff n := by
  refine exists_mvPolynomialF_of_gal_fixed _ (fun σ => ?_)
  exact dedekindThetaProduct_coeff_fixed α hstab σ n

/-- Each `X`-coefficient of `f(X,T)` belongs to the image of the coefficient embedding
`F[T₁,…,T_m] ↪ E[T₁,…,T_m]`. -/
theorem dedekindThetaProduct_coeff_in_map_range (α : Fin m → E)
    (hstab : ∀ σ : E ≃ₐ[F] E, ∃ τ : Equiv.Perm (Fin m), ∀ i, σ (α i) = α (τ i))
    (n : ℕ) :
    (dedekindThetaProduct α).coeff n ∈ Set.range (MvPolynomial.map (algebraMap F E)) := by
  obtain ⟨q, hq⟩ := exists_mvPolynomialF_dedekindThetaProduct_coeff α hstab n
  exact ⟨q, hq⟩

end DedekindThetaGalois

section DedekindThetaGalois2

open Polynomial Equiv

variable {m : ℕ} {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
  [FiniteDimensional F E]

/-- **FT IV §8, Theorem C:** `f(X,T) = ∏_{σ ∈ S_m} (X − σ_T θ)` is, for a Galois-stable
root list `α`, the image of a **monic** polynomial `q ∈ (F[T₁,…,T_m])[X]` of degree
`m!` (the number of permutations of `Fin m`): the coefficients of `f(X,T)` are fixed
by Gal(E/F) (coefficientwise invariance), hence descend to `F[T₁,…,T_m]`, and the
product of the `m!` monic linear factors is monic of degree `m!`. -/
theorem exists_dedekindThetaProduct_descended (α : Fin m → E)
    (hstab : ∀ σ : E ≃ₐ[F] E, ∃ τ : Equiv.Perm (Fin m), ∀ i, σ (α i) = α (τ i)) :
    ∃ q : Polynomial (MvPolynomial (Fin m) F), q.Monic ∧ q.natDegree = m.factorial ∧
      Polynomial.map (MvPolynomial.map (algebraMap F E)) q = dedekindThetaProduct α := by
  have hchoice : ∀ n : ℕ, ∃ q : MvPolynomial (Fin m) F,
      MvPolynomial.map (algebraMap F E) q = (dedekindThetaProduct α).coeff n :=
    fun n => exists_mvPolynomialF_dedekindThetaProduct_coeff α hstab n
  choose g hg using hchoice
  have hmonic : (dedekindThetaProduct α).Monic := by
    show (dedekindThetaProduct α).leadingCoeff = 1
    unfold dedekindThetaProduct
    rw [Polynomial.leadingCoeff_prod]
    exact Finset.prod_eq_one (fun ρ _ => Polynomial.Monic.leadingCoeff (Polynomial.monic_X_sub_C _))
  have hdeg : (dedekindThetaProduct α).natDegree = m.factorial := by
    unfold dedekindThetaProduct
    rw [Polynomial.natDegree_prod (Finset.univ : Finset (Equiv.Perm (Fin m)))
      (fun ρ => (X - C (dedekindTheta (α ∘ ρ.symm))))
      (fun ρ _ => sub_ne_zero_of_ne (Polynomial.X_ne_C _))]
    simp only [Polynomial.natDegree_X_sub_C]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp
  have hc1 : (dedekindThetaProduct α).coeff (dedekindThetaProduct α).natDegree = 1 :=
    Polynomial.Monic.leadingCoeff hmonic
  have hQcoeff : ∀ n : ℕ, (∑ k ∈ (dedekindThetaProduct α).support,
      Polynomial.monomial k (g k)).coeff n
      = if n ∈ (dedekindThetaProduct α).support then g n else 0 := by
    intro n
    rw [Polynomial.finsetSum_coeff _ _ n]
    simp only [Polynomial.coeff_monomial]
    by_cases hn : n ∈ (dedekindThetaProduct α).support
    · rw [Finset.sum_eq_single n (fun b _ hb => if_neg hb) (fun h => absurd hn h)]
      simp [hn]
    · rw [Finset.sum_eq_zero (fun b hb => if_neg (fun h => hn (by rw [← h]; exact hb)))]
      simp [hn]
  have hmap : Polynomial.map (MvPolynomial.map (algebraMap F E))
      (∑ k ∈ (dedekindThetaProduct α).support, Polynomial.monomial k (g k))
      = dedekindThetaProduct α := by
    refine Polynomial.ext (fun n => ?_)
    rw [Polynomial.coeff_map, hQcoeff n]
    by_cases hn : n ∈ (dedekindThetaProduct α).support
    · rw [if_pos hn, hg n]
    · rw [if_neg hn, map_zero]
      have : (dedekindThetaProduct α).coeff n = 0 :=
        not_not.mp (Polynomial.mem_support_iff.not.mp hn)
      rw [this]
  have hinj : Function.Injective
      (MvPolynomial.map (algebraMap F E) :
        MvPolynomial (Fin m) F → MvPolynomial (Fin m) E) :=
    MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective F E)
  have hQN : (∑ k ∈ (dedekindThetaProduct α).support, Polynomial.monomial k (g k)).coeff
      (dedekindThetaProduct α).natDegree = 1 := by
    have hmem : (dedekindThetaProduct α).natDegree ∈ (dedekindThetaProduct α).support := by
      rw [Polynomial.mem_support_iff, hc1]
      simp
    rw [hQcoeff _, if_pos hmem]
    have htop : MvPolynomial.map (algebraMap F E)
        (g (dedekindThetaProduct α).natDegree) = 1 := by
      rw [hg _, hc1]
    exact hinj (by rw [htop, map_one])
  have hQdeg : (∑ k ∈ (dedekindThetaProduct α).support,
      Polynomial.monomial k (g k)).natDegree = (dedekindThetaProduct α).natDegree := by
    refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero ?_)
    · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun n hn => ?_)
      rw [hQcoeff n, if_neg (fun hmem => absurd
        (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hmem))
        (not_le.mpr hn))]
    · rw [hQN]; simp
  refine ⟨∑ k ∈ (dedekindThetaProduct α).support, Polynomial.monomial k (g k), ?_, ?_, hmap⟩
  · show (∑ k ∈ (dedekindThetaProduct α).support,
      Polynomial.monomial k (g k)).coeff
      ((∑ k ∈ (dedekindThetaProduct α).support, Polynomial.monomial k (g k)).natDegree) = 1
    rw [hQdeg]
    exact hQN
  · rw [hQdeg, hdeg]

end DedekindThetaGalois2

end FT
