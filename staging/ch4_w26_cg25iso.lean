-- staging/ch4_w26_cg25iso.lean — worker w26 (cg25 isomorphism σ ↦ σ_α), namespace FT.Cg25.
-- ALL declarations below were REPL-verified (zero errors, no sorry) before the worker's
-- REPL-DOWN; the final #print axioms batch could not be re-run by the worker — main to
-- re-verify from a fresh root after integration.
-- Approach: K = F(T₁,…,T_m) = FractionRing (MvPolynomial (Fin m) F);
-- f₁ = minpoly K (dedekindThetaFrac α) (the FT "!!" remark identifies the factor f₁ with
-- this minimal polynomial); G = tstabPoly f₁ (σ_T-fixing subgroup of S_m);
-- G_f = Gf F α = {σ | ∃ τ : E ≃ₐ[F] E, τ ∘ α = α ∘ σ} — both Subgroups of Equiv.Perm (Fin m),
-- so FT's "σ ↦ σ_α is an isomorphism" = the subgroup equality tstabPoly f₁ = Gf F α
-- (+ separate injectivity of σ ↦ σ_α given distinct roots: injective_alphaComp).
-- PENDING ENDGAME (drafted, NOT verified; every API #check-verified) — see the report
-- transcript / ledger: (1) isInvariant_coef; (2) finrank_fracFrac; (3) counting
-- roots_minpoly_eq_orbit; (4) mem_Gf_of_mem_tstabPoly; (5) main subgroup equality.

namespace FT.Cg25

open MvPolynomial Equiv Polynomial

section Aux
variable {A B : Type*} [Field A] [Field B] [Algebra A B] {m : ℕ}

/-- FT IV §8 (cg25 machinery): the T-permutation lifts compose according to the permutation
product: the lift of `σ * τ` is `τ_T` followed by `σ_T`. -/
theorem renameEquiv_perm_mul (σ τ : Equiv.Perm (Fin m)) (p : MvPolynomial (Fin m) B) :
    MvPolynomial.renameEquiv B (σ * τ) p
      = MvPolynomial.renameEquiv B σ (MvPolynomial.renameEquiv B τ p) := by
  have h : MvPolynomial.renameEquiv B (σ * τ)
      = (MvPolynomial.renameEquiv B τ).trans (MvPolynomial.renameEquiv B σ) := by
    show MvPolynomial.renameEquiv B (Equiv.trans τ σ) = _
    rw [← MvPolynomial.renameEquiv_trans]
  rw [h]
  rfl

/-- FT IV §8 (cg25 machinery): the T-permutation automorphisms compose according to the
permutation product. -/
theorem sigmaTFrac_mul_apply (σ τ : Equiv.Perm (Fin m))
    (z : FractionRing (MvPolynomial (Fin m) B)) :
    FT.sigmaTFrac (σ * τ) z = FT.sigmaTFrac σ (FT.sigmaTFrac τ z) := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) B) z
  simp only [map_div₀, FT.sigmaTFrac_algebraMap]
  rw [renameEquiv_perm_mul, renameEquiv_perm_mul]

/-- FT IV §8 (cg25 machinery): the identity permutation acts trivially on A(T₁,…,T_m). -/
theorem sigmaTFrac_one_apply (z : FractionRing (MvPolynomial (Fin m) B)) :
    FT.sigmaTFrac (1 : Equiv.Perm (Fin m)) z = z := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) B) z
  simp only [map_div₀, FT.sigmaTFrac_algebraMap]
  rw [show (1 : Equiv.Perm (Fin m)) = Equiv.refl _ from rfl, MvPolynomial.renameEquiv_refl]
  rfl

/-- FT IV §8 (cg25 machinery): σ_T acts on polynomials over A(T₁,…,T_m) by permuting the
indeterminates in the coefficients. -/
theorem sigmaTFrac_map_mul (σ τ : Equiv.Perm (Fin m))
    (p : Polynomial (FractionRing (MvPolynomial (Fin m) B))) :
    Polynomial.map (FT.sigmaTFrac (σ * τ)).toRingHom p
      = Polynomial.map (FT.sigmaTFrac σ).toRingHom
          (Polynomial.map (FT.sigmaTFrac τ).toRingHom p) := by
  ext i
  simp only [Polynomial.coeff_map]
  exact sigmaTFrac_mul_apply σ τ _

/-- FT IV §8 (cg25 machinery): the identity permutation fixes polynomials over
A(T₁,…,T_m). -/
theorem sigmaTFrac_map_one (p : Polynomial (FractionRing (MvPolynomial (Fin m) B))) :
    Polynomial.map (FT.sigmaTFrac (1 : Equiv.Perm (Fin m))).toRingHom p = p := by
  ext i
  simp only [Polynomial.coeff_map]
  exact sigmaTFrac_one_apply _

/-- FT IV §8 (cg25 machinery): `σ * σ.symm = 1` in `S_m`. -/
theorem perm_mul_symm_right (σ : Equiv.Perm (Fin m)) : σ * σ.symm = 1 :=
  Equiv.ext fun i => by
    rw [show ((σ * σ.symm : Equiv.Perm (Fin m)) i) = σ (σ.symm i) from rfl]
    exact Equiv.apply_symm_apply σ i

/-- FT IV §8 (cg25 machinery): `σ.symm * σ = 1` in `S_m`. -/
theorem perm_symm_mul_left (σ : Equiv.Perm (Fin m)) : σ.symm * σ = 1 :=
  Equiv.ext fun i => by
    rw [show ((σ.symm * σ : Equiv.Perm (Fin m)) i) = σ.symm (σ i) from rfl]
    exact Equiv.symm_apply_apply σ i

/-- FT IV §8 (cg25): the T-permutation stabilizer is closed under products. -/
theorem tstab_mul_mem {p : Polynomial (FractionRing (MvPolynomial (Fin m) A))}
    {σ τ : Equiv.Perm (Fin m)}
    (hσ : Polynomial.map (FT.sigmaTFrac σ).toRingHom p = p)
    (hτ : Polynomial.map (FT.sigmaTFrac τ).toRingHom p = p) :
    Polynomial.map (FT.sigmaTFrac (σ * τ)).toRingHom p = p := by
  rw [sigmaTFrac_map_mul, hτ, hσ]

/-- FT IV §8 (cg25): the T-permutation stabilizer is closed under inverses. -/
theorem tstab_inv_mem {p : Polynomial (FractionRing (MvPolynomial (Fin m) A))}
    {σ : Equiv.Perm (Fin m)}
    (hσ : Polynomial.map (FT.sigmaTFrac σ).toRingHom p = p) :
    Polynomial.map (FT.sigmaTFrac σ.symm).toRingHom p = p := by
  have h1 : Polynomial.map (FT.sigmaTFrac σ.symm).toRingHom
      (Polynomial.map (FT.sigmaTFrac σ).toRingHom p) = p := by
    rw [← sigmaTFrac_map_mul, perm_symm_mul_left, sigmaTFrac_map_one]
  rwa [hσ] at h1

/-- FT IV §8 (cg25): for a polynomial `p ∈ A(T₁,…,T_m)[X]`, the subgroup of `S_m` of
permutations σ whose T-permutation σ_T fixes `p`. For `p = f₁`, the minimal polynomial of
θ = ∑ Tᵢαᵢ over F(T₁,…,T_m) (i.e. the irreducible factor of f(X,T) containing X − θ, per
the FT "!!" remark ~4433), this is FT's group G. -/
noncomputable def tstabPoly (p : Polynomial (FractionRing (MvPolynomial (Fin m) A))) :
    Subgroup (Equiv.Perm (Fin m)) where
  carrier := {σ | Polynomial.map (FT.sigmaTFrac σ).toRingHom p = p}
  mul_mem' := by
    intro σ τ hσ hτ
    exact tstab_mul_mem hσ hτ
  one_mem' := sigmaTFrac_map_one p
  inv_mem' := by
    intro σ hσ
    exact tstab_inv_mem hσ

/-- Membership in `FT.Cg25.tstabPoly` is being fixed by the lifted T-permutation. -/
theorem mem_tstabPoly (p : Polynomial (FractionRing (MvPolynomial (Fin m) A)))
    (σ : Equiv.Perm (Fin m)) :
    σ ∈ tstabPoly p ↔ Polynomial.map (FT.sigmaTFrac σ).toRingHom p = p := Iff.rfl

/-- FT IV §8 (cg25): the subgroup `G_f ⊆ S_m` of permutations σ of the roots α₁,…,α_m
that are realized by F-automorphisms τ of E with τ(αᵢ) = α_{σ i}. -/
def Gf (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {m : ℕ} (α : Fin m → E) :
    Subgroup (Equiv.Perm (Fin m)) where
  carrier := {σ | ∃ τ : E ≃ₐ[F] E, ∀ i, τ (α i) = α (σ i)}
  mul_mem' := by
    intro σ τ hσ hτ
    obtain ⟨τ₁, hτ₁⟩ := hσ
    obtain ⟨τ₂, hτ₂⟩ := hτ
    exact ⟨τ₁ * τ₂, fun i => by
      rw [show ((τ₁ * τ₂ : E ≃ₐ[F] E) (α i)) = τ₁ (τ₂ (α i)) from rfl, hτ₂ i, hτ₁ (τ i)]
      rfl⟩
  one_mem' := ⟨AlgEquiv.refl, fun i => rfl⟩
  inv_mem' := by
    intro σ hσ
    obtain ⟨τ, hτ⟩ := hσ
    refine ⟨τ.symm, fun i => ?_⟩
    have h1 : τ (α (σ.symm i)) = α i := by
      rw [hτ (σ.symm i), Equiv.apply_symm_apply]
    calc τ.symm (α i) = τ.symm (τ (α (σ.symm i))) := by rw [h1.symm]
      _ = α (σ.symm i) := τ.symm_apply_apply _

/-- Membership in `FT.Cg25.Gf F α` is being realized by an F-automorphism of E. -/
theorem mem_Gf (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {m : ℕ}
    (α : Fin m → E) (σ : Equiv.Perm (Fin m)) :
    σ ∈ Gf F α ↔ ∃ τ : E ≃ₐ[F] E, ∀ i, τ (α i) = α (σ i) := Iff.rfl

/-- FT IV §8 (cg25): the label map σ ↦ σ_α is injective provided the roots are pairwise
distinct (in FT, f is separable). -/
theorem injective_alphaComp {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}
    {α : Fin m → E} (hα : Function.Injective α) :
    Function.Injective (fun σ : Equiv.Perm (Fin m) => α ∘ σ) := by
  intro σ τ h
  have h1 : ∀ i, α (σ i) = α (τ i) := fun i => congrFun h i
  exact Equiv.ext fun i => hα (h1 i)

end Aux

section Easy
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}

/-- FT IV §8 cg25 (easy half of the factor criterion, FT ~4445): if σ_α ∈ G_f is realized
by τ ∈ Gal(E/F), then θ and σ_αθ have the same minimal polynomial over F(T) (minimal
polynomials are invariant under F(T)-algebra equivalences, `FT.minpoly_permRoot`), and
eq12 (σ_αθ = σ_T⁻¹θ, `FT.sigmaTFrac_dedekindThetaFrac`) then forces σ_T to fix f₁ =
minpoly θ over F(T). -/
theorem mem_tstabPoly_of_mem_Gf (α : Fin m → E)
    (hint : IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
    {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ Gf F α) :
    σ ∈ tstabPoly (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α)) := by
  obtain ⟨τ, hτ⟩ := hσ
  have h1 := FT.minpoly_permRoot σ α τ hτ
  have h2 : FT.sigmaTFrac σ.symm (FT.dedekindThetaFrac α) = FT.dedekindThetaFrac (α ∘ σ) :=
    FT.sigmaTFrac_dedekindThetaFrac σ.symm α
  have h3 : minpoly (FractionRing (MvPolynomial (Fin m) F))
      (FT.sigmaTFrac σ.symm (FT.dedekindThetaFrac α))
      = minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α) := by
    rw [h2]
    exact h1
  have h4 := (FT.sigmaT_minpoly_iff σ.symm α hint).mpr h3
  have h5 : Polynomial.map (sigmaTFrac σ).toRingHom
      (Polynomial.map (sigmaTFrac σ.symm).toRingHom
        (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α)))
      = minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α) := by
    rw [← sigmaTFrac_map_mul, perm_mul_symm_right, sigmaTFrac_map_one]
  rw [h4] at h5
  exact h5

end Easy

section Coef
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}

/-- FT IV §8 (cg25 machinery): `g₁ * g₂` acts on polynomials over E[T₁,…,T_m] as g₂ then
g₁. -/
theorem mapAlgEquiv_mul_apply (g₁ g₂ : E ≃ₐ[F] E) (p : MvPolynomial (Fin m) E) :
    MvPolynomial.map (g₁ * g₂).toRingHom p
      = MvPolynomial.map g₁.toRingHom (MvPolynomial.map g₂.toRingHom p) := by
  ext d
  simp only [MvPolynomial.coeff_map]
  rfl

/-- FT IV §8 (cg25 machinery): the identity coefficient automorphism fixes polynomials. -/
theorem mapAlgEquiv_one (p : MvPolynomial (Fin m) E) :
    MvPolynomial.map (1 : E ≃ₐ[F] E).toRingHom p = p := by
  rw [show ((1 : E ≃ₐ[F] E).toRingHom = RingHom.id E) from rfl]
  exact MvPolynomial.map_id p

/-- FT IV §8 (cg25 machinery): extended coefficient automorphisms compose by application
order. -/
theorem sigmaCoefFrac_mul_apply (g₁ g₂ : E ≃ₐ[F] E)
    (z : FractionRing (MvPolynomial (Fin m) E)) :
    FT.sigmaCoefFrac (g₁ * g₂) z = FT.sigmaCoefFrac g₁ (FT.sigmaCoefFrac g₂ z) := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) E) z
  simp only [map_div₀, FT.sigmaCoefFrac_algebraMap]
  rw [mapAlgEquiv_mul_apply, mapAlgEquiv_mul_apply]

/-- FT IV §8 (cg25 machinery): the identity coefficient automorphism acts trivially on
E(T₁,…,T_m). -/
theorem sigmaCoefFrac_one_apply (z : FractionRing (MvPolynomial (Fin m) E)) :
    FT.sigmaCoefFrac (1 : E ≃ₐ[F] E) z = z := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) E) z
  have h : ∀ r : MvPolynomial (Fin m) E, MvPolynomial.map (1 : E ≃ₐ[F] E).toRingHom r = r :=
    fun r => mapAlgEquiv_one r
  simp only [map_div₀, FT.sigmaCoefFrac_algebraMap]
  rw [h, h]

/-- FT IV §8 (cg25 machinery): Gal(E/F) acts on E(T₁,…,T_m) by coefficient automorphisms
(fixing the indeterminates). -/
@[implicit_reducible]
noncomputable def coefMulSemiringAction : MulSemiringAction Gal(E/F)
    (FractionRing (MvPolynomial (Fin m) E)) where
  smul g z := FT.sigmaCoefFrac g z
  mul_smul g₁ g₂ z := sigmaCoefFrac_mul_apply g₁ g₂ z
  one_smul z := sigmaCoefFrac_one_apply z
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _
  smul_one _ := map_one _
  smul_mul _ _ _ := map_mul _ _ _

/-- FT IV §8 (cg25 machinery): F-automorphisms of E acting identically on E(T₁,…,T_m) (via
the coefficient extension) coincide; they are determined by the constants. -/
theorem coef_inj {g₁ g₂ : E ≃ₐ[F] E}
    (h : ∀ z : FractionRing (MvPolynomial (Fin m) E),
      FT.sigmaCoefFrac g₁ z = FT.sigmaCoefFrac g₂ z) : g₁ = g₂ := by
  have h2 : ∀ a : E, g₁ a = g₂ a := by
    intro a
    have app : FT.sigmaCoefFrac g₁ (FT.CGD.constFrac m a)
        = FT.sigmaCoefFrac g₂ (FT.CGD.constFrac m a) := h _
    have e1 : FT.sigmaCoefFrac g₁ (FT.CGD.constFrac m a) = FT.CGD.constFrac m (g₁ a) := by
      show FT.sigmaCoefFrac g₁ (algebraMap (MvPolynomial (Fin m) E)
          (FractionRing (MvPolynomial (Fin m) E)) (MvPolynomial.C a))
        = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
            (MvPolynomial.C (g₁ a))
      rw [FT.sigmaCoefFrac_algebraMap, MvPolynomial.map_C,
        show ((g₁ : E ≃ₐ[F] E).toRingHom a = g₁ a) from rfl]
    have e2 : FT.sigmaCoefFrac g₂ (FT.CGD.constFrac m a) = FT.CGD.constFrac m (g₂ a) := by
      show FT.sigmaCoefFrac g₂ (algebraMap (MvPolynomial (Fin m) E)
          (FractionRing (MvPolynomial (Fin m) E)) (MvPolynomial.C a))
        = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
            (MvPolynomial.C (g₂ a))
      rw [FT.sigmaCoefFrac_algebraMap, MvPolynomial.map_C,
        show ((g₂ : E ≃ₐ[F] E).toRingHom a = g₂ a) from rfl]
    rw [e1, e2] at app
    exact MvPolynomial.C_injective (Fin m) E
      (IsFractionRing.injective (MvPolynomial (Fin m) E)
        (FractionRing (MvPolynomial (Fin m) E)) app)
  exact AlgEquiv.ext h2

/-- FT IV §8 (cg25 machinery): coefficient automorphisms commute with the
F(T₁,…,T_m)-scalars of E(T₁,…,T_m). -/
theorem coef_smul_comm (g : E ≃ₐ[F] E) (k : FractionRing (MvPolynomial (Fin m) F))
    (z : FractionRing (MvPolynomial (Fin m) E)) :
    FT.sigmaCoefFrac g (k • z) = k • FT.sigmaCoefFrac g z := by
  calc FT.sigmaCoefFrac g (k • z)
      = FT.sigmaCoefFrac g (algebraMap (FractionRing (MvPolynomial (Fin m) F))
          (FractionRing (MvPolynomial (Fin m) E)) k * z) := by rw [Algebra.smul_def]
    _ = FT.sigmaCoefFrac g (algebraMap (FractionRing (MvPolynomial (Fin m) F))
          (FractionRing (MvPolynomial (Fin m) E)) k) * FT.sigmaCoefFrac g z := map_mul _ _ _
    _ = algebraMap (FractionRing (MvPolynomial (Fin m) F))
          (FractionRing (MvPolynomial (Fin m) E)) k * FT.sigmaCoefFrac g z :=
          congrArg (fun w : FractionRing (MvPolynomial (Fin m) E) =>
            w * FT.sigmaCoefFrac g z) ((FT.sigmaCoefFrac g).commutes' k)
    _ = k • FT.sigmaCoefFrac g z := (Algebra.smul_def k _).symm

end Coef

end FT.Cg25
