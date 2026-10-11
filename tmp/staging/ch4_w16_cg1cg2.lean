-- STAGING: FT ch. IV §1 discriminant/sign (cg1, cg2), re-derivation worker w16 deliverable,
-- received verbatim. All 20 public declarations + 2 private helpers verified from a fresh
-- REPL root (gen 8), axioms exactly [propext, Classical.choice, Quot.sound].
-- Paste inside namespace FT.

section Vandermonde

variable {R : Type*} [CommRing R] {n : ℕ}

/-- FT ch. IV §1 (`cg1`): the Vandermonde product `∏_{i<j} (r i - r j)`, indexed `∏ j, ∏ i ∈ Iio j`. -/
def vandermondeProd (r : Fin n → R) : R :=
  ∏ j : Fin n, ∏ i ∈ Finset.Iio j, (r i - r j)

/-- FT cg1 (a): `vandermondeProd (r ∘ σ) = sign σ · vandermondeProd r` (each inversion of `σ`
flips one factor), via Mathlib's inversion-parity lemma `Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod`. -/
theorem vandermondeProd_perm (r : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    vandermondeProd (r ∘ σ) = ↑↑(Equiv.Perm.sign σ) * vandermondeProd r :=
  @Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod n R _ σ (fun i j => r i - r j)
    (fun _ _ => (neg_sub _ _).symm)

/-- FT cg1 (b): `Δ²` is unchanged by any relabeling (`sign σ = ±1` squares to `1`). -/
theorem vandermondeProd_sq_perm (r : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    vandermondeProd (r ∘ σ) ^ 2 = vandermondeProd r ^ 2 := by
  rw [vandermondeProd_perm, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

end Vandermonde

section Transport

variable {F E : Type u} [Field F] [Field E] [Algebra F E] {n : ℕ}

/-- FT ch. IV §1: `Δ(f)` for a root enumeration `r : Fin n → E`; `ftDelta r ^ 2 = D(f)`. -/
abbrev ftDelta (r : Fin n → E) : E := vandermondeProd r

/-- FT cg1: `ftDelta r` is the Vandermonde product of the enumeration. -/
theorem ftDelta_eq_vandermondeProd (r : Fin n → E) : ftDelta r = vandermondeProd r := rfl

/-- FT IV §1: the permutation `σ̂` of `Fin n` induced by `σ : E ≃ₐ[F] E` on roots enumerated by
injective `r` (with `σ (r i)` again in the range of `r`); characterized in `ftRootsEquiv_apply`. -/
noncomputable def ftRootsEquiv (r : Fin n → E) (hri : Function.Injective r) (σ : E ≃ₐ[F] E)
    (hσ : ∀ i, σ (r i) ∈ Set.range r) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => (Set.mem_range.mp (hσ i)).choose)
    ⟨fun i i' hij => by
      have h1 := congrArg r hij
      rw [Exists.choose_spec (Set.mem_range.mp (hσ i)),
        Exists.choose_spec (Set.mem_range.mp (hσ i'))] at h1
      exact hri (Equiv.injective σ.toEquiv h1),
      fun j => by
        have hinj : Function.Injective (fun i => (Set.mem_range.mp (hσ i)).choose) :=
          fun i i' hij => by
            have h1 := congrArg r hij
            rw [Exists.choose_spec (Set.mem_range.mp (hσ i)),
              Exists.choose_spec (Set.mem_range.mp (hσ i'))] at h1
            exact hri (Equiv.injective σ.toEquiv h1)
        exact (Finite.injective_iff_surjective (f := fun i => (Set.mem_range.mp (hσ i)).choose)).mp
          hinj j⟩

/-- FT IV §1: defining property of `σ̂`: `r (σ̂ i) = σ (r i)`. -/
theorem ftRootsEquiv_apply (r : Fin n → E) (hri : Function.Injective r) (σ : E ≃ₐ[F] E)
    (hσ : ∀ i, σ (r i) ∈ Set.range r) (i : Fin n) :
    r (ftRootsEquiv r hri σ hσ i) = σ (r i) :=
  Exists.choose_spec (Set.mem_range.mp (hσ i))

/-- Helper: `(±1 : ℤˣ)` squared, embedded in a commutative ring, is `1`. -/
private theorem priv_sign_sq {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (↑↑(Equiv.Perm.sign σ) : R) ^ 2 = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- FT cg1 (a): `σ • Δ = sign(σ̂) · Δ` (`σ` moves into the product and replaces `r i` by
`r (σ̂ i)`, then `vandermondeProd_perm`). -/
theorem ftDelta_gal_smul' (r : Fin n → E) (hri : Function.Injective r) (σ : E ≃ₐ[F] E)
    (hσ : ∀ i, σ (r i) ∈ Set.range r) :
    σ • ftDelta r = ↑↑(Equiv.Perm.sign (ftRootsEquiv r hri σ hσ)) * ftDelta r := by
  have h1 : σ.toAlgHom (vandermondeProd r) = vandermondeProd (r ∘ (ftRootsEquiv r hri σ hσ)) := by
    simp only [vandermondeProd, map_prod σ.toAlgHom, map_sub, ftRootsEquiv_apply r hri σ hσ,
      Function.comp_apply]
    rfl
  show σ.toAlgHom (ftDelta r) = _
  rw [h1, vandermondeProd_perm]

/-- FT cg1 (b): `σ • Δ² = Δ²` (`σ • Δ² = (σ • Δ)²` and `sign(σ̂)² = 1`). -/
theorem ftDelta_sq_gal_smul' (r : Fin n → E) (hri : Function.Injective r) (σ : E ≃ₐ[F] E)
    (hσ : ∀ i, σ (r i) ∈ Set.range r) :
    σ • ftDelta r ^ 2 = ftDelta r ^ 2 := by
  have hsmul : ∀ y : E, σ • y = σ.toAlgHom y := fun y => rfl
  have hsm : σ.toAlgHom (ftDelta r) = ↑↑(Equiv.Perm.sign (ftRootsEquiv r hri σ hσ)) * ftDelta r :=
    ftDelta_gal_smul' r hri σ hσ
  rw [hsmul, map_pow σ.toAlgHom (ftDelta r) 2, hsm, mul_pow, priv_sign_sq, one_mul]

/-- FT IV §1: the sign of `σ̂` is independent of the enumeration (relabeling by `π` conjugates
`σ̂` to `π σ̂ π⁻¹`, same signature). -/
theorem ftRootsEquiv_sign_congr (r : Fin n → E) (hri : Function.Injective r)
    (π : Equiv.Perm (Fin n)) (σ : E ≃ₐ[F] E) (hσ : ∀ i, σ (r i) ∈ Set.range r)
    (hσ' : ∀ i, σ (r (π i)) ∈ Set.range (r ∘ π)) :
    Equiv.Perm.sign (ftRootsEquiv (r ∘ π) (hri.comp π.injective) σ hσ') =
      Equiv.Perm.sign (ftRootsEquiv r hri σ hσ) := by
  have hpt : ∀ i, π ((ftRootsEquiv (r ∘ π) (hri.comp π.injective) σ hσ') i)
      = (ftRootsEquiv r hri σ hσ) (π i) := by
    intro i
    have h1 := ftRootsEquiv_apply (r ∘ π) (hri.comp π.injective) σ hσ' i
    have h2 := ftRootsEquiv_apply r hri σ hσ (π i)
    rw [Function.comp_apply, Function.comp_apply] at h1
    rw [← h1] at h2
    exact hri h2.symm
  have hcong : ftRootsEquiv (r ∘ π) (hri.comp π.injective) σ hσ'
      = (π.trans (ftRootsEquiv r hri σ hσ)).trans π.symm :=
    Equiv.ext fun i => by
      simp only [Equiv.trans_apply]
      rw [← hpt i, Equiv.symm_apply_apply]
  rw [hcong, Equiv.Perm.sign_trans_trans_symm]

end Transport

section Splitting

variable {F E : Type u} [Field F] [Field E] [Algebra F E] {n : ℕ} {r : Fin n → E}

/-- Helper: `σ : E →ₐ[F] E` commutes with evaluation of `f ∈ F[X]`:
`eval (σ x) (f.map (algebraMap F E)) = σ (eval x (f.map (algebraMap F E)))` — via
`eval_map`, `aeval_def` and `aeval_algHom_apply`. -/
private theorem priv_eval_gal (f : Polynomial F) (σ : E →ₐ[F] E) (x : E) :
    (f.map (algebraMap F E)).eval (σ x) = σ ((f.map (algebraMap F E)).eval x) := by
  rw [Polynomial.eval_map (algebraMap F E) (σ x), Polynomial.eval_map (algebraMap F E) x,
    ← Polynomial.aeval_def, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
    Polynomial.aeval_def, ← Polynomial.eval_map]

/-- FT IV §1: if `r : Fin n → E` enumerates the roots of `f` (injectively, with range the root
set of `f.map (algebraMap F E)` in `E`), then every `σ : Gal(E/F)` permutes the enumerated
roots.  Proof: `σ` commutes with evaluation (`priv_eval_gal`), hence maps roots to roots. -/
theorem gal_apply_mem_range (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E)
    (σ : Gal(E/F)) (i : Fin n) : σ (r i) ∈ Set.range r := by
  have hp0 : (f.map (algebraMap F E)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap F E))).mpr hf
  have hmem : r i ∈ (f.map (algebraMap F E)).rootSet E := by
    rw [← hr]; exact ⟨i, rfl⟩
  obtain ⟨-, h0⟩ := Polynomial.mem_rootSet.mp hmem
  have h0' : (f.map (algebraMap F E)).eval (r i) = 0 := h0
  have h1 : (f.map (algebraMap F E)).eval (σ.toAlgHom (r i)) = 0 := by
    rw [priv_eval_gal f σ.toAlgHom (r i), h0']
    exact map_zero σ.toAlgHom
  have hroot' : σ (r i) ∈ (f.map (algebraMap F E)).rootSet E :=
    Polynomial.mem_rootSet.mpr ⟨hp0, h1⟩
  rw [hr]
  exact hroot'

/-- FT cg2 (a): `D(f) = Δ²` lies in the fixed field of the full Galois group: every
`σ : Gal(E/F)` permutes the enumerated roots, and `ftDelta_sq_gal_smul'` shows `σ` fixes `Δ²`. -/
theorem ftDiscr_mem_fixedField_top (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E)
    (hri : Function.Injective r) :
    ftDelta r ^ 2 ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  exact ftDelta_sq_gal_smul' r hri σ (fun i => gal_apply_mem_range f hf hr σ i)

/-- FT cg2 (a): the discriminant `D(f) = Δ(f)²` is an element of the base field `F` (encoded
as `∃ a : F, algebraMap F E a = D(f)`; equivalently `D(f) ∈ (algebraMap F E).fieldRange`):
it lies in `fixedField ⊤ = ⊥` (`IsGalois.fixedField_top`, `IntermediateField.mem_bot`). -/
theorem ftDiscr_mem_algebraMap (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E)
    (hri : Function.Injective r) [IsGalois F E] [FiniteDimensional F E] :
    ∃ a : F, algebraMap F E a = ftDelta r ^ 2 := by
  have h1 : ftDelta r ^ 2 ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) :=
    ftDiscr_mem_fixedField_top f hf hr hri
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at h1
  exact h1

/-- Characteristic `≠ 2` of `F` gives `(2 : E) ≠ 0`: `2 = 1 + 1` maps along `algebraMap F E`,
which is injective (`RingHom.injective`, `F` a field). -/
theorem two_ne_zero_algebraMap (h2 : (2 : F) ≠ 0) : (2 : E) ≠ 0 := by
  have h' : algebraMap F E (2 : F) = (2 : E) := by
    rw [← one_add_one_eq_two, map_add, map_one, one_add_one_eq_two]
  intro h
  apply h2
  have h0 : algebraMap F E (2 : F) = 0 := by rw [h', h]
  exact (RingHom.injective (algebraMap F E)) (h0.trans (map_zero _).symm)

/-- Helper for FT cg2 (b): if `σ : Gal(E/F)` fixes `Δ = ftDelta r`, `char F ≠ 2` and
`Δ ≠ 0`, then the induced permutation `σ̂` is even (`sign σ̂ = 1`).  Proof:
`ftDelta_gal_smul'` gives `σ • Δ = sign(σ̂) · Δ`; if `sign(σ̂) = -1` then `Δ + Δ = 0`, so
`(1 + 1) · Δ = 0` in the field `E`, contradicting `2 ≠ 0` and `Δ ≠ 0`. -/
theorem sign_eq_one_of_gal_fix (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E) (hri : Function.Injective r)
    (hΔ : ftDelta r ≠ 0) (h2 : (2 : E) ≠ 0) (σ : Gal(E/F))
    (hfix : σ.toAlgHom (ftDelta r) = ftDelta r) :
    Equiv.Perm.sign (ftRootsEquiv r hri σ (fun i => gal_apply_mem_range f hf hr σ i)) = 1 := by
  have hsm : σ.toAlgHom (ftDelta r) = ↑↑(Equiv.Perm.sign (ftRootsEquiv r hri σ
      (fun i => gal_apply_mem_range f hf hr σ i))) * ftDelta r :=
    ftDelta_gal_smul' r hri σ (fun i => gal_apply_mem_range f hf hr σ i)
  have hsm2 : ↑↑(Equiv.Perm.sign (ftRootsEquiv r hri σ
      (fun i => gal_apply_mem_range f hf hr σ i))) * ftDelta r = ftDelta r :=
    hsm.symm.trans hfix
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ftRootsEquiv r hri σ
      (fun i => gal_apply_mem_range f hf hr σ i))) with hu | hu
  · exact hu
  · exfalso
    rw [hu, Units.coe_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul,
      neg_eq_iff_add_eq_zero] at hsm2
    have h2Δ : (2 : E) * ftDelta r = 0 := by rw [two_mul]; exact hsm2
    rcases mul_eq_zero.mp h2Δ with h' | h'
    · exact h2 h'
    · exact hΔ h'

/-- FT cg2 (b): for `char F ≠ 2` and `Δ = ftDelta r ≠ 0`, an element `σ` of `Gal(E/F)` fixes
`F[Δ] = IntermediateField.adjoin F {Δ}` pointwise iff the induced permutation `σ̂` is even
(`sign σ̂ = 1`); i.e. the fixing subgroup of `F[Δ]` is exactly the "even part" of the Galois
group.  Proof (⇐): `sign σ̂ = 1` gives `σ • Δ = Δ`; the fixed-point set of `σ` is the
intermediate field `fixedField (stabilizer σ Δ) ∋ Δ`, containing `F[Δ]` (`adjoin_le_iff`),
and `fixingSubgroup` is antitone with `fixingSubgroup (fixedField (stabilizer …)) ∋ σ`.
Proof (⇒): `σ` fixes `Δ ∈ F[Δ]`, and `sign(σ̂) · Δ = σ • Δ = Δ` forces `sign σ̂ = 1` unless
`char = 2` or `Δ = 0` (`sign_eq_one_of_gal_fix`). -/
theorem gal_mem_fixingSubgroup_adjoin_singleton (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E) (hri : Function.Injective r)
    (hΔ : ftDelta r ≠ 0) (h2 : (2 : E) ≠ 0) [FiniteDimensional F E] (σ : Gal(E/F)) :
    σ ∈ (IntermediateField.adjoin F ({ftDelta r} : Set E)).fixingSubgroup ↔
      Equiv.Perm.sign (ftRootsEquiv r hri σ (fun i => gal_apply_mem_range f hf hr σ i)) = 1 := by
  constructor
  · intro hmem
    exact sign_eq_one_of_gal_fix f hf hr hri hΔ h2 σ
      ((IntermediateField.mem_fixingSubgroup_iff _ σ).mp hmem (ftDelta r)
        (IntermediateField.subset_adjoin F _ (Set.mem_singleton _)))
  · intro hsign
    have hsm := ftDelta_gal_smul' r hri σ (fun i => gal_apply_mem_range f hf hr σ i)
    rw [hsign] at hsm
    simp only [Units.val_one, Int.cast_one, one_mul] at hsm
    have hΔfix : σ.toAlgHom (ftDelta r) = ftDelta r := hsm
    have hmemΔ : ftDelta r ∈
        IntermediateField.fixedField (MulAction.stabilizer Gal(E/F) (ftDelta r)) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact MulAction.mem_stabilizer_iff.mp hτ
    have hsub : IntermediateField.adjoin F ({ftDelta r} : Set E) ≤
        IntermediateField.fixedField (MulAction.stabilizer Gal(E/F) (ftDelta r)) :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmemΔ)
    have hstab : MulAction.stabilizer Gal(E/F) (ftDelta r) ≤
        (IntermediateField.adjoin F ({ftDelta r} : Set E)).fixingSubgroup := by
      have h1 : (IntermediateField.fixedField
            (MulAction.stabilizer Gal(E/F) (ftDelta r))).fixingSubgroup
          = MulAction.stabilizer Gal(E/F) (ftDelta r) :=
        IntermediateField.fixingSubgroup_fixedField _
      have h2 : (IntermediateField.fixedField
            (MulAction.stabilizer Gal(E/F) (ftDelta r))).fixingSubgroup ≤
          (IntermediateField.adjoin F ({ftDelta r} : Set E)).fixingSubgroup :=
        IntermediateField.fixingSubgroup_antitone hsub
      rw [h1] at h2
      exact h2
    exact hstab (MulAction.mem_stabilizer_iff.mpr hΔfix)

/-- FT cg2 (b): under `char F ≠ 2` and `Δ = ftDelta r ≠ 0`, the whole Galois group acts
through even permutations iff `Δ ∈ F`.
Proof (⇒): every `σ` fixes `Δ` (since `σ • Δ = sign(σ̂) · Δ = Δ`), so `Δ ∈ fixedField ⊤ = ⊥`
(`IsGalois.fixedField_top`, `IntermediateField.mem_bot`).  (⇐): `Δ = algebraMap F E a` is
fixed by every `σ ∈ Gal(E/F)` (which fixes `F` pointwise), so `sign σ̂ = 1` by
`sign_eq_one_of_gal_fix`. -/
theorem gal_even_iff_delta_mem (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E) (hri : Function.Injective r)
    (hΔ : ftDelta r ≠ 0) (h2 : (2 : E) ≠ 0) [IsGalois F E] [FiniteDimensional F E] :
    (∀ σ : Gal(E/F),
        Equiv.Perm.sign (ftRootsEquiv r hri σ (fun i => gal_apply_mem_range f hf hr σ i)) = 1) ↔
      ∃ a : F, algebraMap F E a = ftDelta r := by
  constructor
  · intro hall
    have hfix : ftDelta r ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ _
      have hsm := ftDelta_gal_smul' r hri τ (fun i => gal_apply_mem_range f hf hr τ i)
      rw [hall τ] at hsm
      simp only [Units.val_one, Int.cast_one, one_mul] at hsm
      exact hsm
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hfix
    exact hfix
  · rintro ⟨a, ha⟩ σ
    exact sign_eq_one_of_gal_fix f hf hr hri hΔ h2 σ (by rw [← ha, AlgHom.map_algebraMap])

/-- FT cg2 (b): `Δ ∈ F` iff the discriminant `Δ²` is a square in `F` (i.e. `Δ² = t²` for some
`t ∈ F`) — both directions hold in a field without any hypothesis on the characteristic:
if `Δ² = t²` then `(Δ - t)(Δ + t) = Δ² - t² = 0` in the field `E`, so `Δ = t` or `Δ = -t`. -/
theorem delta_mem_iff_square {Δ : E} :
    (∃ a : F, algebraMap F E a = Δ) ↔ ∃ t : F, algebraMap F E t ^ 2 = Δ ^ 2 := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]⟩
  · rintro ⟨t, ht⟩
    have h1 : (Δ - algebraMap F E t) * (Δ + algebraMap F E t) = 0 := by
      have hsq : (Δ - algebraMap F E t) * (Δ + algebraMap F E t) = Δ ^ 2 - (algebraMap F E t) ^ 2 := by
        ring
      rw [hsq, ← ht, sub_self]
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact ⟨t, (sub_eq_zero.mp h').symm⟩
    · refine ⟨-t, ?_⟩
      rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]
      exact h'

/-- FT cg2 (b): `G_f ⊆ A_n` — encoded as every `σ : Gal(E/F)` fixing `F[Δ]` pointwise —
iff `Δ ∈ F` (under `char F ≠ 2`, `Δ ≠ 0`); combines `gal_mem_fixingSubgroup_adjoin_singleton`
pointwise with `gal_even_iff_delta_mem`. -/
theorem gal_top_le_fixingSubgroup_iff_delta_mem (f : Polynomial F) (hf : f ≠ 0)
    (hr : Set.range r = (f.map (algebraMap F E)).rootSet E) (hri : Function.Injective r)
    (hΔ : ftDelta r ≠ 0) (h2 : (2 : E) ≠ 0) [IsGalois F E] [FiniteDimensional F E] :
    (∀ σ : Gal(E/F), σ ∈ (IntermediateField.adjoin F ({ftDelta r} : Set E)).fixingSubgroup) ↔
      ∃ a : F, algebraMap F E a = ftDelta r := by
  constructor
  · intro hall
    exact (gal_even_iff_delta_mem f hf hr hri hΔ h2).mp (fun σ =>
      (gal_mem_fixingSubgroup_adjoin_singleton f hf hr hri hΔ h2 σ).mp (hall σ))
  · rintro ⟨a, ha⟩ σ
    exact (gal_mem_fixingSubgroup_adjoin_singleton f hf hr hri hΔ h2 σ).mpr
      ((gal_even_iff_delta_mem f hf hr hri hΔ h2).mpr ⟨a, ha⟩ σ)

/-- FT IV §1 packaging: a separable polynomial `f` of degree `n` whose image splits in `E`
admits an injective enumeration `r : Fin n → E` of its roots in `E` (range of `r` = root set
of `f.map (algebraMap F E)`), to which the discriminant results apply.
Proof: the root finset `(f.map (algebraMap F E)).roots.toFinset` has `n` elements
(`Multiset.toFinset_card_of_nodup` with `nodup_roots` from separability, and
`Splits.natDegree_eq_card_roots` with `natDegree_map`), and `Fintype.equivFinOfCardEq`
transports the indexing; the root finset is the root set since `rootSet p E` is by definition
the finset of `p.aroots E = (p.map (algebraMap E E)).roots = p.roots`. -/
theorem exists_rootEnumeration (f : Polynomial F) (hf : f.Separable)
    (hspl : (f.map (algebraMap F E)).Splits) (hdeg : f.natDegree = n) :
    ∃ r : Fin n → E, Function.Injective r ∧
      Set.range r = (f.map (algebraMap F E)).rootSet E := by
  classical
  have hp0' : (f.map (algebraMap F E)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap F E))).mpr hf.ne_zero
  have hsep' : (f.map (algebraMap F E)).Separable :=
    (Polynomial.separable_map (algebraMap F E)).mpr hf
  have hnd : (f.map (algebraMap F E)).roots.Nodup := Polynomial.nodup_roots hsep'
  have hcard : (f.map (algebraMap F E)).roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← hspl.natDegree_eq_card_roots,
      Polynomial.natDegree_map (algebraMap F E), hdeg]
  have hcard' : Fintype.card ↥((f.map (algebraMap F E)).roots.toFinset) = n := by
    rw [Fintype.card_coe]; exact hcard
  have hbridge : ((f.map (algebraMap F E)).roots.toFinset : Set E) =
      (f.map (algebraMap F E)).rootSet E := by
    rw [Polynomial.rootSet, Polynomial.aroots_def, Algebra.algebraMap_self, Polynomial.map_id]
  refine ⟨Subtype.val ∘ ⇑(Fintype.equivFinOfCardEq hcard').symm, ?_, ?_⟩
  · exact Subtype.coe_injective.comp (Fintype.equivFinOfCardEq hcard').symm.injective
  · rw [← hbridge, Set.range_comp, Set.range_eq_univ.mpr
      (Fintype.equivFinOfCardEq hcard').symm.surjective, Set.image_univ, Subtype.range_coe]

end Splitting
