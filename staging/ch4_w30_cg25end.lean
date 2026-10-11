-- staging/ch4_w30_cg25end.lean — worker w30 (cg25 endgame), 16 declarations, ALL verified
-- (axioms: propext, Classical.choice, Quot.sound only). Append inside namespace FT.Cg25
-- after ch4_w26_cg25iso.lean.
-- DELIVERED: eq_of_dedekindThetaFrac_eq, eq_one_of_fixes_range, orbitInjective,
-- fracHomKL_injective, sigmaCoefFracAlgHom, aeval_sigmaCoefFrac, orbit_aeval_zero,
-- prod_mulLeft, norm_invariant, rootSet_eq_orbit, mem_Gf_of_mem_tstabPoly,
-- tstabPoly_eq_Gf, tstabPoly_eq_Gf_of_algebraic, injective_label_on_Gf,
-- cg25_isomorphism, isInvariant_coef.
-- Corrections vs. recorded route: (a) item (1)'s claim "p·W has Galois-fixed coefficients"
-- was FALSE (W not invariant: σ_g(W) = W·q₀/(g q₀)); correct proof keeps the invariant
-- norm P = ∏_g g(q₀) = q₀·W as denominator and proves invariance of p₀·W at FRACTION
-- level (ι(p₀·W) = ι(p₀·P)/ι(q₀)); (b) rootSet route uses Set-API (roots is a Multiset in
-- v4.31): Polynomial.rootSet/mem_rootSet'/ncard_rootSet_le/rootSet_finite +
-- Set.eq_of_subset_of_ncard_le; (c) F(T)→E(T) embedding = algebraMap (Frac (MvPoly F))
-- (Frac (MvPoly E)) = (FT.fracHom F E).toRingHom = FT.algebraMap_fracAlg (rfl), via the
-- GLOBAL instance FT.CGD.fracAlgCGD (Target ~13241; the local instance fracAlg does not
-- leak).
-- PENDING (sole gap): item (2) finrank_fracFrac : finrank (F(T)) (E(T)) = finrank F E —
-- (3)-(5) take hfinK : Module.Finite K L and hdim as hypotheses. Math proof recorded:
-- an F-basis of E is a K-basis of L (spanning: K-span of ι_E(E) is a field containing
-- ι_E(E[T]) and ι_K(K); independence: clear denominators, extract MvPolynomial
-- coefficients, F-linear independence via b.repr). Candidate Mathlib leads (untested):
-- IsBaseChange.finrank_eq (LinearAlgebra/Dimension/Localization.lean:178),
-- IsLocalizedModule.lift_rank_eq, Module.rank_baseChange; tensor route needs
-- linear-disjointness by hand. No blocker — purely unfinished work.

namespace FT.Cg25

open MvPolynomial Equiv Polynomial

section Endgame
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}

/-- FT IV §8 (cg25 machinery): the map `β ↦ dedekindThetaFrac β = ι(∑ Tᵢ C(βᵢ))` of root
tuples into B(T₁,…,T_m) determines each component: equal values force `β₁ i = β₂ i`
(via `IsFractionRing.injective` and the linear independence of the indeterminates,
`FT.sum_X_mul_C_inj`). -/
theorem eq_of_dedekindThetaFrac_eq {B : Type*} [Field B] {β₁ β₂ : Fin m → B} (i : Fin m)
    (h : FT.dedekindThetaFrac β₁ = FT.dedekindThetaFrac β₂) : β₁ i = β₂ i := by
  have h1 : algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
      (FT.dedekindTheta β₁)
      = algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
          (FT.dedekindTheta β₂) := h
  have h2 : (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) B) * MvPolynomial.C (β₁ i))
      = ∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) B) * MvPolynomial.C (β₂ i) :=
    IsFractionRing.injective (MvPolynomial (Fin m) B)
      (FractionRing (MvPolynomial (Fin m) B)) h1
  exact congrFun (FT.sum_X_mul_C_inj h2) i

/-- FT IV §8 (cg25 machinery): an `F`-automorphism `u` of `E` fixing each of the
generators `αᵢ` (with `F[α₁,…,α_m] = E`) is the identity: by `Algebra.adjoin_induction`,
every element of `F[α₁,…,α_m]` is built from `F` and the `αᵢ` by `+`/`*`, and `u` fixes
all of these. -/
theorem eq_one_of_fixes_range {u : E ≃ₐ[F] E} (α : Fin m → E)
    (hu : ∀ i, u (α i) = α i) (hgen : Algebra.adjoin F (Set.range α) = ⊤) : u = 1 := by
  have key : ∀ x : E, u x = x := by
    intro x
    have hx : x ∈ Algebra.adjoin F (Set.range α) := by
      rw [hgen]
      exact trivial
    refine Algebra.adjoin_induction (R := F) (A := E) (s := Set.range α)
      (p := fun y (_ : y ∈ Algebra.adjoin F (Set.range α)) => u y = y) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact hu i
    · intro r
      exact u.commutes' r
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro x y _ _ hx hy
      rw [map_mul, hx, hy]
  exact AlgEquiv.ext key

/-- FT IV §8 (cg25): the Galois orbit map `g ↦ g·θ = ∑ Tᵢ g(αᵢ)` on `E(T₁,…,T_m)` is
injective provided the roots `αᵢ` generate `E` over `F`: `g₁·θ = g₂·θ` forces
`g₁(αᵢ) = g₂(αᵢ)` for all `i` (linear independence of the `Tᵢ`), and `g₂⁻¹g₁` then fixes
every generator, hence is trivial. -/
theorem orbitInjective (α : Fin m → E)
    (hgen : Algebra.adjoin F (Set.range α) = ⊤) :
    Function.Injective (fun g : E ≃ₐ[F] E => FT.sigmaCoefFrac g (FT.dedekindThetaFrac α)) := by
  intro g₁ g₂ h
  have h' : FT.sigmaCoefFrac g₁ (FT.dedekindThetaFrac α)
      = FT.sigmaCoefFrac g₂ (FT.dedekindThetaFrac α) := h
  rw [FT.sigmaCoefFrac_dedekindThetaFrac, FT.sigmaCoefFrac_dedekindThetaFrac] at h'
  have hcoef : ∀ i, g₁ (α i) = g₂ (α i) := fun i => eq_of_dedekindThetaFrac_eq i h'
  have hu : ∀ i, (g₂.symm * g₁) (α i) = α i := fun i => by
    show g₂.symm (g₁ (α i)) = α i
    rw [hcoef i]
    exact AlgEquiv.symm_apply_apply g₂ (α i)
  have h1 := eq_one_of_fixes_range α hu hgen
  refine AlgEquiv.ext fun x => ?_
  have h3 : (g₂.symm * g₁) x = x := by rw [h1]; rfl
  calc g₁ x = g₂ (g₂.symm (g₁ x)) := (AlgEquiv.apply_symm_apply g₂ (g₁ x)).symm
    _ = g₂ x := congrArg g₂ h3

/-- FT IV §8 (cg25 machinery): the coefficient embedding `F(T₁,…,T_m) ↪ E(T₁,…,T_m)`
(`algebraMap` of `FT.fracAlg`) is injective (a nonzero ring hom out of a field). -/
theorem fracHomKL_injective :
    Function.Injective (algebraMap (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E))) := by
  intro a b hab
  by_cases h : a - b = 0
  · exact sub_eq_zero.mp h
  · exfalso
    have h4 : (a - b) * (a - b)⁻¹ = 1 := mul_inv_cancel₀ h
    have h5 : algebraMap (FractionRing (MvPolynomial (Fin m) F))
        (FractionRing (MvPolynomial (Fin m) E)) ((a - b) * (a - b)⁻¹)
      = algebraMap (FractionRing (MvPolynomial (Fin m) F))
        (FractionRing (MvPolynomial (Fin m) E)) 1 := congrArg _ h4
    rw [map_mul, map_one] at h5
    have h6 : algebraMap (FractionRing (MvPolynomial (Fin m) F))
        (FractionRing (MvPolynomial (Fin m) E)) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    rw [h6, zero_mul] at h5
    exact one_ne_zero h5.symm

/-- FT IV §8 (cg25 machinery): the coefficient automorphism `g·` of `E(T₁,…,T_m)` extends
to an `F(T₁,…,T_m)`-algebra endomorphism (it fixes the `F(T₁,…,T_m)`-scalars, via
`coef_smul_comm` at `z = 1`). -/
noncomputable def sigmaCoefFracAlgHom (g : E ≃ₐ[F] E) :
    FractionRing (MvPolynomial (Fin m) E) →ₐ[FractionRing (MvPolynomial (Fin m) F)]
      FractionRing (MvPolynomial (Fin m) E) where
  toFun := FT.sigmaCoefFrac g
  map_one' := map_one _
  map_mul' := fun x y => map_mul (FT.sigmaCoefFrac g) x y
  map_zero' := map_zero _
  map_add' := fun x y => map_add (FT.sigmaCoefFrac g) x y
  commutes' := fun k => by
    have h2 := coef_smul_comm g k (1 : FractionRing (MvPolynomial (Fin m) E))
    simp only [Algebra.smul_def, map_one, mul_one] at h2
    exact h2

/-- FT IV §8 (cg25 machinery): the coefficient action commutes with evaluation of
`F(T₁,…,T_m)`-polynomials: `g·` maps `aeval θ p` to `aeval (g·θ) p`
(`Polynomial.aeval_algHom_apply`). -/
theorem aeval_sigmaCoefFrac (g : E ≃ₐ[F] E)
    (p : Polynomial (FractionRing (MvPolynomial (Fin m) F)))
    (x : FractionRing (MvPolynomial (Fin m) E)) :
    Polynomial.aeval (FT.sigmaCoefFrac g x) p
      = FT.sigmaCoefFrac g (Polynomial.aeval x p) :=
  Polynomial.aeval_algHom_apply (sigmaCoefFracAlgHom g) x p

/-- FT IV §8 (cg25, step 3a): every Galois conjugate `g·θ` of θ annihilates `f₁`:
the coefficients of `f₁ = minpoly θ` are `F(T)`-scalars, fixed by the coefficient action
(`coef_smul_comm`), so `g·` maps the vanishing `f₁(θ) = 0` to `f₁(g·θ) = 0`. -/
theorem orbit_aeval_zero (α : Fin m → E) (g : E ≃ₐ[F] E) :
    Polynomial.aeval (FT.sigmaCoefFrac g (FT.dedekindThetaFrac α))
      (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α)) = 0 := by
  rw [aeval_sigmaCoefFrac, minpoly.aeval (FractionRing (MvPolynomial (Fin m) F))
    (FT.dedekindThetaFrac α)]
  exact map_zero _

/-- FT IV §8 (cg25 machinery, item (1)): reindexing a product over the Galois group by
left multiplication. -/
theorem prod_mulLeft [FiniteDimensional F E] [IsGalois F E] (q₀ : MvPolynomial (Fin m) E)
    (g : E ≃ₐ[F] E) :
    ∏ h : Gal(E/F), MvPolynomial.map (g * h).toRingHom q₀
      = ∏ h : Gal(E/F), MvPolynomial.map h.toRingHom q₀ :=
  Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

/-- FT IV §8 (cg25, item (1)): the norm `∏_g g(q₀)` of a nonzero polynomial `q₀ ∈
E[T₁,…,T_m]` is Galois-invariant and nonzero. -/
theorem norm_invariant [FiniteDimensional F E] [IsGalois F E] (q₀ : MvPolynomial (Fin m) E)
    (hq₀ne : q₀ ≠ 0) :
    (∏ h : Gal(E/F), MvPolynomial.map h.toRingHom q₀) ≠ 0 ∧
      ∀ g : E ≃ₐ[F] E, MvPolynomial.map g.toRingHom
        (∏ h : Gal(E/F), MvPolynomial.map h.toRingHom q₀)
        = ∏ h : Gal(E/F), MvPolynomial.map h.toRingHom q₀ := by
  refine ⟨?_, fun g => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ hk0
    exact hq₀ne (MvPolynomial.map_injective k.toRingHom (AlgEquiv.injective k)
      (hk0.trans (map_zero _).symm))
  · rw [map_prod, Finset.prod_congr rfl (fun h _ => by
      rw [← mapAlgEquiv_mul_apply])]
    exact prod_mulLeft q₀ g

/-- FT IV §8 (cg25, step 3): in `E(T₁,…,T_m)` the root set of `f₁ = minpoly θ` (θ =
∑ Tᵢαᵢ) is exactly the Galois orbit of θ under the coefficient action
`Gal(E/F) ↷ E(T₁,…,T_m)`. Counting: orbit ⊆ root set (the coefficients of `f₁` are
`F(T)`-scalars, fixed by the action); `|orbit| = |Gal(E/F)| = [E:F] = [E(T):F(T)]` (orbit
map injective by linear independence of the `Tᵢ`, plus `IsGalois.card_aut_eq_finrank` and
the degree hypothesis `hdim`); `#rootSet ≤ deg f₁ ≤ [E(T):F(T)]` (`Polynomial.ncard_rootSet_le`,
`minpoly.natDegree_le`). -/
theorem rootSet_eq_orbit (α : Fin m → E)
    (hint : IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
    (hgen : Algebra.adjoin F (Set.range α) = ⊤)
    (hfinK : Module.Finite (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)))
    (hdim : Module.finrank (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) = Module.finrank F E)
    [FiniteDimensional F E] [IsGalois F E] :
    (Set.range fun g : E ≃ₐ[F] E => FT.sigmaCoefFrac g (FT.dedekindThetaFrac α))
      = (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α)).rootSet
        (FractionRing (MvPolynomial (Fin m) E)) := by
  haveI : Module.Finite (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) := hfinK
  set f₁ : Polynomial (FractionRing (MvPolynomial (Fin m) F)) :=
    minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α) with hf₁
  set O : Set (FractionRing (MvPolynomial (Fin m) E)) :=
    Set.range (fun g : E ≃ₐ[F] E => FT.sigmaCoefFrac g (FT.dedekindThetaFrac α)) with hO
  have hsub : O ⊆ f₁.rootSet (FractionRing (MvPolynomial (Fin m) E)) := by
    intro x hx
    rw [hO] at hx
    obtain ⟨g, rfl⟩ := hx
    exact Polynomial.mem_rootSet'.mpr
      ⟨Polynomial.map_ne_zero (minpoly.ne_zero hint), orbit_aeval_zero α g⟩
  have hbound : (f₁.rootSet (FractionRing (MvPolynomial (Fin m) E))).ncard ≤ O.ncard := by
    rw [Set.ncard_range_of_injective (orbitInjective α hgen)]
    calc (f₁.rootSet (FractionRing (MvPolynomial (Fin m) E))).ncard
        ≤ f₁.natDegree := Polynomial.ncard_rootSet_le f₁ _
      _ ≤ Module.finrank (FractionRing (MvPolynomial (Fin m) F))
          (FractionRing (MvPolynomial (Fin m) E)) := minpoly.natDegree_le _
      _ = Module.finrank F E := hdim
      _ = Nat.card Gal(E/F) := (IsGalois.card_aut_eq_finrank F E).symm
  exact Set.eq_of_subset_of_ncard_le hsub hbound
    (Polynomial.rootSet_finite f₁ (FractionRing (MvPolynomial (Fin m) E)))

/-- FT IV §8 (cg25, heart of the factor criterion, FT ~4445): the hard inclusion
`G ⊆ G_f`: if the lifted T-permutation σ_T fixes `f₁ = minpoly θ` over `F(T₁,…,T_m)`
(θ = ∑ Tᵢαᵢ, the roots αᵢ generating E over F), then σ is realized by an F-automorphism
of E: σ_T θ is a root of f₁, hence lies in the Galois orbit of θ (step 3), so
∑ Tᵢ g(αᵢ) = ∑ Tᵢ α_{σ⁻¹ i} for some g ∈ Gal(E/F); linear independence of the Tᵢ gives
g(α_{σ i}) = αᵢ, and `g⁻¹` realizes σ on the αᵢ. -/
theorem mem_Gf_of_mem_tstabPoly (α : Fin m → E)
    (hint : IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
    (hgen : Algebra.adjoin F (Set.range α) = ⊤)
    (hfinK : Module.Finite (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)))
    (hdim : Module.finrank (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) = Module.finrank F E)
    [FiniteDimensional F E] [IsGalois F E]
    {σ : Equiv.Perm (Fin m)}
    (hσ : σ ∈ tstabPoly (minpoly (FractionRing (MvPolynomial (Fin m) F))
      (FT.dedekindThetaFrac α))) :
    σ ∈ Gf F α := by
  rw [mem_tstabPoly _ σ] at hσ
  have h1 := (FT.sigmaT_minpoly_iff σ α hint).mp hσ
  have haeval : Polynomial.aeval (FT.sigmaTFrac σ (FT.dedekindThetaFrac α))
      (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α)) = 0 := by
    rw [← h1, minpoly.aeval (FractionRing (MvPolynomial (Fin m) F))
      (FT.sigmaTFrac σ (FT.dedekindThetaFrac α))]
  have hmem : FT.sigmaTFrac σ (FT.dedekindThetaFrac α)
      ∈ Set.range (fun g : E ≃ₐ[F] E => FT.sigmaCoefFrac g (FT.dedekindThetaFrac α)) := by
    rw [rootSet_eq_orbit α hint hgen hfinK hdim]
    exact Polynomial.mem_rootSet'.mpr
      ⟨Polynomial.map_ne_zero (minpoly.ne_zero hint), haeval⟩
  obtain ⟨g, hg⟩ := hmem
  have hg' : FT.sigmaCoefFrac g (FT.dedekindThetaFrac α)
      = FT.sigmaTFrac σ (FT.dedekindThetaFrac α) := hg
  rw [FT.sigmaCoefFrac_dedekindThetaFrac, FT.sigmaTFrac_dedekindThetaFrac] at hg'
  have keyGen : ∀ i, g (α i) = α (σ.symm i) := fun i => eq_of_dedekindThetaFrac_eq i hg'
  rw [mem_Gf]
  exact ⟨g.symm, fun i => by
    have key0 : g (α (σ i)) = α i := by rw [keyGen (σ i), Equiv.symm_apply_apply]
    calc g.symm (α i) = g.symm (g (α (σ i))) := by rw [← key0]
      _ = α (σ i) := AlgEquiv.symm_apply_apply g (α (σ i))⟩

/-- FT IV §8 (cg25, main): the T-permutation stabilizer of `f₁ = minpoly θ` over
`F(T₁,…,T_m)` equals `G_f` — the subgroup of `S_m` of permutations realized by
`F`-automorphisms of `E` (θ = ∑ Tᵢαᵢ, the roots αᵢ generating `E` over `F`; needs the
degree hypothesis `hdim : [E(T₁,…,T_m) : F(T₁,…,T_m)] = [E : F]`, see ledger item (2)). -/
theorem tstabPoly_eq_Gf (α : Fin m → E)
    (hint : IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
    (hgen : Algebra.adjoin F (Set.range α) = ⊤)
    (hfinK : Module.Finite (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)))
    (hdim : Module.finrank (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) = Module.finrank F E)
    [FiniteDimensional F E] [IsGalois F E] :
    tstabPoly (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
      = Gf F α := by
  ext σ
  exact ⟨fun hσ => mem_Gf_of_mem_tstabPoly α hint hgen hfinK hdim hσ,
    fun hσ => mem_tstabPoly_of_mem_Gf α hint hσ⟩

/-- FT IV §8 (cg25, main, packaged): the integrality hypothesis supplied by
`FT.CGD.isIntegral_dedekindThetaFrac` from the algebraicity of the roots. -/
theorem tstabPoly_eq_Gf_of_algebraic (α : Fin m → E)
    (hαalg : ∀ i, IsAlgebraic F (α i))
    (hgen : Algebra.adjoin F (Set.range α) = ⊤)
    (hfinK : Module.Finite (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)))
    (hdim : Module.finrank (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) = Module.finrank F E)
    [FiniteDimensional F E] [IsGalois F E] :
    tstabPoly (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
      = Gf F α :=
  tstabPoly_eq_Gf α (FT.CGD.isIntegral_dedekindThetaFrac m α hαalg) hgen hfinK hdim

/-- FT IV §8 (cg25): on `G_f` the label map `σ ↦ σ_α` (the permutation induced on the
distinct roots) is injective — the other half of "σ ↦ σ_α is an isomorphism from G onto
G_f". -/
theorem injective_label_on_Gf (α : Fin m → E) (hα : Function.Injective α) :
    Function.Injective (fun σ : Gf F α => α ∘ (σ : Equiv.Perm (Fin m))) := by
  intro σ₁ σ₂ h
  have h'' : ∀ i, α ((σ₁ : Equiv.Perm (Fin m)) i) = α ((σ₂ : Equiv.Perm (Fin m)) i) :=
    fun i => congrFun h i
  exact Subtype.ext (Equiv.ext fun i => hα (h'' i))

/-- FT IV §8, cg25 (formal content): the label map `σ ↦ σ_α` is an isomorphism from `G`
(= `tstabPoly f₁`) onto `G_f`: the groups coincide and the label map is injective (given
distinct roots, FT's separable hypothesis). -/
theorem cg25_isomorphism (α : Fin m → E)
    (hα : Function.Injective α)
    (hint : IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
    (hgen : Algebra.adjoin F (Set.range α) = ⊤)
    (hfinK : Module.Finite (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)))
    (hdim : Module.finrank (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) = Module.finrank F E)
    [FiniteDimensional F E] [IsGalois F E] :
    (tstabPoly (minpoly (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac α))
      = Gf F α) ∧
    Function.Injective (fun σ : Gf F α => α ∘ (σ : Equiv.Perm (Fin m))) :=
  ⟨tstabPoly_eq_Gf α hint hgen hfinK hdim, injective_label_on_Gf α hα⟩

/-- FT IV §8 (cg25 supporting, item (1)): the fixed points of the coefficient action
`Gal(E/F) ↷ E(T₁,…,T_m)` are exactly the image of `F(T₁,…,T_m)`. Proof: write
`z = ι(p₀)/ι(q₀)`; the Galois-invariant norm `P = ∏_g g(q₀)` splits as `q₀·W`, and the
invariance of `z` forces `p' = p₀·W` to be invariant as well (all at fraction level:
`ι(p₀·W) = ι(p₀·P)/ι(q₀)`, conjugated via `keyfrac`); invariant polynomials descend
(`FT.exists_mvPolynomialF_of_gal_fixed`), so `z = ι(p'')/ι(q'')` lies in the image of
`F(T₁,…,T_m)`. -/
theorem isInvariant_coef (z : FractionRing (MvPolynomial (Fin m) E))
    (hz : ∀ g : E ≃ₐ[F] E, FT.sigmaCoefFrac g z = z)
    [FiniteDimensional F E] [IsGalois F E] :
    ∃ k : FractionRing (MvPolynomial (Fin m) F),
      algebraMap (FractionRing (MvPolynomial (Fin m) F))
        (FractionRing (MvPolynomial (Fin m) E)) k = z := by
  classical
  obtain ⟨p₀, q₀, hq₀mem, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) E) z
  have hq₀ne : q₀ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq₀mem
  have hI : Function.Injective (algebraMap (MvPolynomial (Fin m) E)
      (FractionRing (MvPolynomial (Fin m) E))) :=
    IsFractionRing.injective (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
  have hnz : ∀ x : MvPolynomial (Fin m) E, x ≠ 0 → algebraMap (MvPolynomial (Fin m) E)
      (FractionRing (MvPolynomial (Fin m) E)) x ≠ 0 := by
    intro x hx hc
    exact hx (hI (by show algebraMap _ _ x = algebraMap _ _ 0; rw [hc, map_zero]))
  have keyfrac : ∀ g : E ≃ₐ[F] E, algebraMap (MvPolynomial (Fin m) E)
        (FractionRing (MvPolynomial (Fin m) E)) (MvPolynomial.map g.toRingHom p₀)
      / algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
        (MvPolynomial.map g.toRingHom q₀)
      = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) p₀
        / algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) q₀ := by
    intro g
    have h1 := hz g
    rw [map_div₀, FT.sigmaCoefFrac_algebraMap, FT.sigmaCoefFrac_algebraMap] at h1
    exact h1
  set P : MvPolynomial (Fin m) E :=
    ∏ h : Gal(E/F), MvPolynomial.map h.toRingHom q₀ with hPdef
  set W : MvPolynomial (Fin m) E :=
    ∏ h ∈ (Finset.univ.erase (1 : Gal(E/F))), MvPolynomial.map h.toRingHom q₀ with hWdef
  have map1id : MvPolynomial.map (1 : Gal(E/F)).toRingHom q₀ = q₀ := by
    rw [show ((1 : Gal(E/F)).toRingHom = RingHom.id E) from rfl]
    exact MvPolynomial.map_id q₀
  have hPsplit : P = q₀ * W := by
    rw [hPdef, hWdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : Gal(E/F))), map1id]
    ac_rfl
  have hPne : P ≠ 0 := (norm_invariant q₀ hq₀ne).1
  have hWne : W ≠ 0 := by
    intro hW0
    rw [hPsplit, hW0, mul_zero] at hPne
    exact hPne rfl
  have hPinv : ∀ g : E ≃ₐ[F] E, MvPolynomial.map g.toRingHom P = P :=
    (norm_invariant q₀ hq₀ne).2
  have hPmul : p₀ * P = (p₀ * W) * q₀ := by rw [hPsplit]; ac_rfl
  have stepA : algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
      (p₀ * W)
      = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) (p₀ * P)
        / algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) q₀ := by
    rw [eq_div_iff (hnz _ hq₀ne), ← map_mul, ← hPmul]
  have stepB : ∀ g : E ≃ₐ[F] E, FT.sigmaCoefFrac g
      (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) (p₀ * W))
      = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) (p₀ * W) := by
    intro g
    rw [stepA, map_div₀, FT.sigmaCoefFrac_algebraMap, FT.sigmaCoefFrac_algebraMap,
      map_mul (MvPolynomial.map g.toRingHom), map_mul, hPinv g, ← div_mul_eq_mul_div,
      keyfrac g, div_mul_eq_mul_div, ← map_mul]
  have hp'invtpoly : ∀ g : E ≃ₐ[F] E, MvPolynomial.map g.toRingHom (p₀ * W) = p₀ * W := by
    intro g
    have := stepB g
    rw [FT.sigmaCoefFrac_algebraMap] at this
    exact IsFractionRing.injective (MvPolynomial (Fin m) E)
      (FractionRing (MvPolynomial (Fin m) E)) this
  obtain ⟨p'', hp''⟩ := FT.exists_mvPolynomialF_of_gal_fixed (p₀ * W) hp'invtpoly
  obtain ⟨q'', hq''⟩ := FT.exists_mvPolynomialF_of_gal_fixed P hPinv
  have hq''ne : q'' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hq''
    exact hPne hq''.symm
  refine ⟨algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) p'' /
    algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) q'', ?_⟩
  rw [map_div₀]
  have e1 : algebraMap (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E))
      (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) p'')
    = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) (p₀ * W) := by
    rw [← hp'']
    show FT.fracHom (A := F) (B := E)
      (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) p'') = _
    exact FT.fracHom_algebraMap p''
  have e2 : algebraMap (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E))
      (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) q'')
    = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) P := by
    rw [← hq'']
    show FT.fracHom (A := F) (B := E)
      (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) q'') = _
    exact FT.fracHom_algebraMap q''
  rw [e1, e2, hPsplit, map_mul, map_mul, mul_div_mul_right _ _ (hnz _ hWne)]

end Endgame

end FT.Cg25
