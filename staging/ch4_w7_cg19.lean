-- STAGING: FT ch. IV §7 first half (orbit factorization, cg19/cg19m, finite-field prose),
-- worker w7 deliverable, collected verbatim. REPL-verified by w7 (0 errors/warnings,
-- axioms clean). Intended for namespace FT; uses ch3 FT.orbit_eq_rootSet_minpoly,
-- FT.minpoly_eq_prod_orbit.

namespace FT

/-! ## FT chapter IV §7, first half: orbit factorization (FT `cg19`, `cg19m`) -/

section Cg19

open Polynomial
open scoped Classical

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Fintype Gal(E/F)]

/-- The finset of the distinct roots of `f` in `E` (Milne's `α₁, …, αₘ ∈ F_f`). -/
noncomputable def cg19Roots (f : F[X]) (E : Type*) [CommRing E] [IsDomain E] [Algebra F E]
    [DecidableEq E] : Finset E :=
  (f.map (algebraMap F E)).roots.toFinset

omit [Fintype Gal(E/F)] in
/-- Membership in `FT.cg19Roots` is membership in the root set `f.rootSet E`. -/
theorem cg19_mem_cg19Roots_iff (f : F[X]) (β : E) :
    β ∈ cg19Roots f E ↔ β ∈ f.rootSet E := by
  simp only [cg19Roots, Polynomial.rootSet_def, Polynomial.aroots_def, Finset.mem_coe,
    Multiset.mem_toFinset]

omit [Fintype Gal(E/F)] in
/-- FT `cg19` (proof step). The Galois group `Gal(E/F)` permutes the roots of `f` in `E`. -/
theorem cg19_smul_mem_rootSet (f : F[X]) (hα : α ∈ f.rootSet E) (σ : Gal(E/F)) :
    σ α ∈ f.rootSet E := by
  obtain ⟨hf, h0⟩ := Polynomial.mem_rootSet.mp hα
  refine (Polynomial.mem_rootSet_of_ne hf).mpr ?_
  rw [show σ α = (σ : E →ₐ[F] E) α from rfl, Polynomial.aeval_algHom_apply, h0, map_zero]

omit [Fintype Gal(E/F)] in
/-- FT `cg19` (proof step). The orbit finset of a root `α` of `f` is contained in the root
set of `f` in `E`. -/
theorem cg19_orbitFinset_subset_rootSet (f : F[X]) (hα : α ∈ f.rootSet E) :
    ((Finset.univ.image fun σ : Gal(E/F) => σ α) : Set E) ⊆ f.rootSet E := by
  rw [Finset.coe_image, Set.image_subset_iff]
  exact fun σ _ => cg19_smul_mem_rootSet f hα σ

omit [Fintype Gal(E/F)] in
/-- FT `cg19` (proof step). A root `α` of the monic polynomial `f` is integral over `F`. -/
theorem cg19_isIntegral_of_mem_rootSet (f : F[X]) (hm : f.Monic) (hα : α ∈ f.rootSet E) :
    IsIntegral F α := by
  obtain ⟨_, h0⟩ := Polynomial.mem_rootSet.mp hα
  exact ⟨f, hm, by rwa [← Polynomial.aeval_def]⟩

omit [Fintype Gal(E/F)] in
/-- FT `cg19` (proof step). For a root `α` of `f`, the minimal polynomial `minpoly F α`
divides `f` in `F[X]`. -/
theorem cg19_minpoly_dvd_of_mem_rootSet (f : F[X]) (hα : α ∈ f.rootSet E) :
    minpoly F α ∣ f := by
  obtain ⟨_, h0⟩ := Polynomial.mem_rootSet.mp hα
  exact minpoly.dvd F α h0

/-- FT `cg19` (proof step). The orbit product over the orbit finset of `α` is fixed by every
`σ ∈ Gal(E/F)`. -/
theorem cg19_orbitFinset_prod_map_eq_self (α : E) (σ : Gal(E/F)) :
    ((Finset.univ.image fun τ : Gal(E/F) => τ α).prod fun β => X - C β).map (σ : E →+* E)
      = (Finset.univ.image fun τ : Gal(E/F) => τ α).prod fun β => X - C β := by
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  refine Finset.prod_bij (fun β _ => σ β) ?_ ?_ ?_ ?_
  · rintro β hβ
    obtain ⟨τ, _, hτ⟩ := Finset.mem_image.mp hβ
    refine Finset.mem_image.mpr ⟨σ * τ, Finset.mem_univ _, ?_⟩
    rw [← hτ, AlgEquiv.mul_apply]
  · rintro β _ γ _ h
    exact σ.injective h
  · rintro b hb
    obtain ⟨τ, _, hτ⟩ := Finset.mem_image.mp hb
    refine ⟨(σ⁻¹ * τ) α, Finset.mem_image.mpr ⟨σ⁻¹ * τ, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [← hτ, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ σ⁻¹ (τ α), mul_inv_cancel]
    rfl
  · intro β _; rfl

/-- FT `cg19` (proof step). The orbit of `α` under `G = Gal(E/F)` is the image finset. -/
theorem cg19_orbitSet_eq_orbitFinset (α : E) :
    MulAction.orbit Gal(E/F) α
      = ((Finset.univ.image fun τ : Gal(E/F) => τ α : Finset E) : Set E) := by
  rw [show MulAction.orbit Gal(E/F) α = Set.range (fun τ : Gal(E/F) => τ • α) from rfl,
    ← Fintype.coe_image_univ]
  rfl

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Fintype Gal(E/F)] [IsGalois F E]

/-- FT `cg19` (proof step). The elements of the root finset having the same minimal
polynomial as `α` form exactly the orbit finset of `α` under `Gal(E/F)`. -/
theorem cg19_rootFinset_filter_eq_orbitFinset (f : F[X]) (hm : f.Monic) (hα : α ∈ cg19Roots f E) :
    (cg19Roots f E).filter (fun β => minpoly F β = minpoly F α)
      = (Finset.univ.image fun σ : Gal(E/F) => σ α) := by
  have hintα : IsIntegral F α := cg19_isIntegral_of_mem_rootSet f hm
    ((cg19_mem_cg19Roots_iff f α).mp hα)
  ext β
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨_, hminpoly⟩ := h
    have hmin : minpoly F α ≠ 0 := minpoly.ne_zero hintα
    have hb : β ∈ (minpoly F α).rootSet E := by
      rw [Polynomial.mem_rootSet_of_ne hmin, ← hminpoly, minpoly.aeval F β]
    obtain ⟨σ, _, hσ⟩ :=
      (Set.mem_image _ _ _).mp ((FT.orbit_eq_rootSet_minpoly α hintα).symm.subset hb)
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨cg19_smul_mem_rootSet f ((cg19_mem_cg19Roots_iff f α).mp hα) σ,
      minpoly.algEquiv_eq σ α⟩

/-- FT `cg19` (proof step). The minimal polynomial of a root `α` of `f`, mapped into `E[X]`,
is the product of `X − β` over the fiber of the minimal-polynomial map on the root finset. -/
theorem cg19_minpoly_map_eq_prod_filter (f : F[X]) (hm : f.Monic) (hα : α ∈ cg19Roots f E) :
    (minpoly F α).map (algebraMap F E)
      = ((cg19Roots f E).filter (fun β => minpoly F β = minpoly F α)).prod fun β => X - C β := by
  rw [cg19_rootFinset_filter_eq_orbitFinset f hm hα]
  exact FT.minpoly_eq_prod_orbit α
    (cg19_isIntegral_of_mem_rootSet f hm ((cg19_mem_cg19Roots_iff f α).mp hα))

omit [Fintype Gal(E/F)] [IsGalois F E] in
/-- **FT `cg19m`** (orbit factorization, explicit product in `E[X]`). -/
theorem cg19m (f : F[X]) (hm : f.Monic) (hsep : f.Separable)
    (hspl : (f.map (algebraMap F E)).Splits) :
    f.map (algebraMap F E)
      = ((cg19Roots f E).image (fun α => minpoly F α)).prod fun g =>
          ((cg19Roots f E).filter (fun β => minpoly F β = g)).prod fun β => X - C β := by
  have hnodup : (f.map (algebraMap F E)).roots.Nodup :=
    Polynomial.nodup_roots ((Polynomial.separable_map (algebraMap F E)).mpr hsep)
  have h1 : f.map (algebraMap F E) = (cg19Roots f E).prod fun β => X - C β := by
    rw [hspl.eq_prod_roots_of_monic (Polynomial.Monic.map (algebraMap F E) hm)]
    rw [Finset.prod_eq_multiset_prod, cg19Roots, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
  have hbU : cg19Roots f E =
      ((cg19Roots f E).image (fun α => minpoly F α)).biUnion
        (fun g => (cg19Roots f E).filter (fun β => minpoly F β = g)) := by
    ext β
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨minpoly F β, ⟨β, h, rfl⟩, ⟨h, rfl⟩⟩
    · rintro ⟨g, -, ⟨h, rfl⟩⟩
      exact h
  have hdisj : Set.PairwiseDisjoint
      (↑((cg19Roots f E).image (fun α => minpoly F α)))
      (fun g : F[X] => (cg19Roots f E).filter (fun β => minpoly F β = g)) := by
    rintro g - g' - h
    exact Finset.disjoint_left.mpr fun β h1 h2 => h
      (by rw [← (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2])
  rw [h1]
  conv_lhs => rw [hbU]
  rw [Finset.prod_biUnion hdisj]

/-- FT `cg19` (degrees). Degree of `minpoly F α` = cardinality of the orbit finset. -/
theorem cg19_natDegree_eq_card_orbitFinset (α : E) (hint : IsIntegral F α) :
    (minpoly F α).natDegree = (Finset.univ.image fun σ : Gal(E/F) => σ α).card := by
  rw [← Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective F E) (minpoly F α),
    FT.minpoly_eq_prod_orbit α hint]
  rw [Polynomial.natDegree_prod _ (fun β => X - C β)
      (fun β _ => by intro h; rw [sub_eq_zero] at h; exact Polynomial.X_ne_C β h)]
  simp [Finset.sum_const, smul_eq_mul]

/-- FT `cg19` (degrees). The degree of the irreducible factor `minpoly F α` of `f` equals
the cardinality of its fiber in the root finset. -/
theorem cg19_factor_natDegree_eq_card_filter (f : F[X]) (hm : f.Monic) (hα : α ∈ cg19Roots f E) :
    (minpoly F α).natDegree =
      ((cg19Roots f E).filter (fun β => minpoly F β = minpoly F α)).card := by
  rw [cg19_rootFinset_filter_eq_orbitFinset f hm hα]
  exact cg19_natDegree_eq_card_orbitFinset α
    (cg19_isIntegral_of_mem_rootSet f hm ((cg19_mem_cg19Roots_iff f α).mp hα))

/-- **FT `cg19`** (factorization into irreducible factors, in `F[X]`). -/
theorem cg19_factorization (f : F[X]) (hm : f.Monic) (hsep : f.Separable)
    (hspl : (f.map (algebraMap F E)).Splits) :
    f = ((cg19Roots f E).image (fun α => minpoly F α)).prod (fun g => g) := by
  have hE := cg19m f hm hsep hspl
  have hkey : ∀ g ∈ (cg19Roots f E).image (fun α => minpoly F α),
      ((cg19Roots f E).filter (fun β => minpoly F β = g)).prod (fun β => X - C β)
        = g.map (algebraMap F E) := by
    rintro g hg
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hg
    rw [cg19_minpoly_map_eq_prod_filter f hm hα]
  rw [Finset.prod_congr rfl hkey, ← Polynomial.map_prod] at hE
  exact Polynomial.map_injective (algebraMap F E) (FaithfulSMul.algebraMap_injective F E) hE

/-- FT `cg19` (degrees of the distinct irreducible factors): `deg f = m₁ + ⋯ + m_r`. -/
theorem cg19_natDegree_eq_sum_degrees (f : F[X]) (hm : f.Monic) (hsep : f.Separable)
    (hspl : (f.map (algebraMap F E)).Splits) :
    f.natDegree = ∑ g ∈ (cg19Roots f E).image (fun α => minpoly F α), g.natDegree := by
  conv_lhs => rw [cg19_factorization f hm hsep hspl]
  exact Polynomial.natDegree_prod _ (fun g => g) (fun g hg => by
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hg
    exact minpoly.ne_zero
      (cg19_isIntegral_of_mem_rootSet f hm ((cg19_mem_cg19Roots_iff f α).mp hα)))

/-- **FT `cg19`**: orbit factorization with irreducibility and degree = fiber size. -/
theorem cg19 (f : F[X]) (hm : f.Monic) (hsep : f.Separable)
    (hspl : (f.map (algebraMap F E)).Splits) :
    f = ((cg19Roots f E).image (fun α => minpoly F α)).prod (fun g => g)
      ∧ ∀ g ∈ (cg19Roots f E).image (fun α => minpoly F α),
          Irreducible g ∧ g.natDegree =
            ((cg19Roots f E).filter (fun β => minpoly F β = g)).card := by
  refine ⟨cg19_factorization f hm hsep hspl, fun g hg => ?_⟩
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hg
  exact ⟨minpoly.irreducible
    (cg19_isIntegral_of_mem_rootSet f hm ((cg19_mem_cg19Roots_iff f α).mp hα)),
    cg19_factor_natDegree_eq_card_filter f hm hα⟩

end Cg19

/-! ### FT §7 prose (finite fields): `G_f` cyclic, generated by the Frobenius -/

section Cg19F

open Polynomial
open scoped Classical

variable {F E : Type u} [Field F] [Fintype F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [IsGalois F E]

/-- **FT §7 prose (finite fields).** `G_f = Gal(E/F)` is cyclic, generated by the Frobenius
automorphism. -/
theorem cg19F_gal_eq_zpowers_frobenius :
    (Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic F E) : Subgroup Gal(E/F)) = ⊤ := by
  haveI : Finite E := Module.finite_of_finite F
  have hcard : Nat.card Gal(E/F) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  have hord : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic F E) = Module.finrank F E :=
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, hord, ← hcard]

/-- **FT §7 prose (finite fields).** The orbit of `α` under `G_f = ⟨σ⟩` is the set of
Frobenius powers. -/
theorem cg19F_orbit_eq_range_pow (α : E) :
    MulAction.orbit Gal(E/F) α
      = Set.range fun k : ℕ => (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ k) α := by
  haveI : Finite E := Module.finite_of_finite F
  ext x
  rw [MulAction.mem_orbit_iff, Set.mem_range]
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F E).2 τ
    subst hn
    exact ⟨_, hτ⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, rfl⟩

/-- **FT §7 prose (finite fields).** The length of the Frobenius cycle through a root `α` of
`f` is the degree of the irreducible factor `minpoly F α` of `f`. -/
theorem cg19F_card_cycle_eq_natDegree (f : F[X]) (hm : f.Monic) (hα : α ∈ f.rootSet E) :
    (Set.range fun k : ℕ => (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ k) α).ncard
      = (minpoly F α).natDegree := by
  haveI : Finite E := Module.finite_of_finite F
  have hint : IsIntegral F α := cg19_isIntegral_of_mem_rootSet f hm hα
  rw [← cg19F_orbit_eq_range_pow α,
    congrArg Set.ncard (cg19_orbitSet_eq_orbitFinset α), Set.ncard_coe_finset,
    ← cg19_natDegree_eq_card_orbitFinset α hint]

end Cg19F

end FT
