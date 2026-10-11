-- staging/ch4_w20_cg3.lean — worker w20 (cg3: conjugation / sign of D(f) / A_n non-inclusion).
-- Delivered verbatim. UNVERIFIED-at-delivery pieces (REPL outage): final line of
-- vandermondeProd_ne_zero; full not_forall_sign_eq_one_of_s_odd — verify in fresh REPL
-- before integration. Core block (star_algebraMap_rat, sign_involutive_perm_of_card,
-- star_vandermondeDelta_eq_neg_one_pow_mul, (a), (b)) verified pre-outage, zero errors.
/-! ## FT chapter IV §1 (`cg3`): conjugation, the sign of the discriminant, and `A_n` -/

/-- Helper for FT `cg3`: complex conjugation fixes rational scalars in `ℂ`.  Proof: `conjQ`
is a `ℚ`-algebra homomorphism, hence fixes images along `algebraMap ℚ ℂ`. -/
theorem star_algebraMap_rat (a : ℚ) : star (algebraMap ℚ ℂ a) = algebraMap ℚ ℂ a := by
  rw [← conjQ_apply, AlgHom.map_algebraMap]

/-- FT IV §1 helper: the Vandermonde product of an injectively enumerated family in a field
is nonzero (each factor `r i - r j` with `i < j` is nonzero since `r` is injective). -/
theorem vandermondeProd_ne_zero {F : Type*} [Field F] {n : ℕ} (r : Fin n → F)
    (hri : Function.Injective r) : vandermondeProd r ≠ 0 := by
  intro hc
  rw [vandermondeProd, Finset.prod_eq_zero_iff] at hc
  obtain ⟨j, -, hJ⟩ := hc
  rw [Finset.prod_eq_zero_iff] at hJ
  obtain ⟨i, hi, hI⟩ := hJ
  exact absurd (hri (sub_eq_zero.mp hI)) (Finset.mem_Iio.mp hi).ne

/-- Helper for FT `cg3` (Milne's "more direct" argument): the sign of an involution `π` of
`Fin n` whose support has exactly `2s` elements is `(-1)^s`.  Proof: strong induction on a
finset `S` containing the support of `π`: if `i` is a non-fixed point and `j = π i`, then
`π = swap i j * ρ` where `ρ := swap i j * π` is again an involution whose support is the
support of `π` minus `{i, j}`, and `Equiv.Perm.sign_mul` together with
`Equiv.Perm.sign_swap` reduce the sign of `π` to `-1 * sign ρ`. -/
theorem sign_involutive_perm_of_card {n s : ℕ} (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i)
    (hcard : (Finset.univ.filter (fun i => π i ≠ i)).card = 2 * s) :
    (Equiv.Perm.sign π : ℤ) = (-1 : ℤ) ^ s := by
  classical
  have key : ∀ (S : Finset (Fin n)), ∀ (ρ : Equiv.Perm (Fin n)), (∀ i, ρ (ρ i) = i) →
      (∀ i, ρ i ≠ i → i ∈ S) → ∀ t : ℕ,
      (Finset.univ.filter (fun i => ρ i ≠ i)).card = 2 * t →
      (Equiv.Perm.sign ρ : ℤ) = (-1 : ℤ) ^ t := by
    intro S
    refine Finset.strongInductionOn (p := fun S => ∀ (ρ : Equiv.Perm (Fin n)),
      (∀ i, ρ (ρ i) = i) → (∀ i, ρ i ≠ i → i ∈ S) → ∀ t : ℕ,
      (Finset.univ.filter (fun i => ρ i ≠ i)).card = 2 * t →
      (Equiv.Perm.sign ρ : ℤ) = (-1 : ℤ) ^ t) S ?_
    intro S IH ρ hρ hsub t ht
    by_cases hsup : ∃ i, ρ i ≠ i
    · obtain ⟨i, hi⟩ := hsup
      have hj : ρ (ρ i) = i := hρ i
      have hij : i ≠ ρ i := fun hc => hi hc.symm
      have hρinj : Function.Injective ρ := Equiv.injective ρ
      set ρ₁ : Equiv.Perm (Fin n) := Equiv.swap i (ρ i) * ρ with hρ₁def
      -- `ρ = swap i (ρ i) * ρ₁` and `ρ₁` is an involution fixing `i` and `ρ i`
      have hmul : ρ = Equiv.swap i (ρ i) * ρ₁ := by
        rw [hρ₁def, ← mul_assoc,
          show Equiv.swap i (ρ i) * Equiv.swap i (ρ i) = 1 from
            Equiv.ext (fun y => Equiv.swap_apply_self i (ρ i) y), one_mul]
      have hρi : ρ₁ i = i := by
        rw [hρ₁def, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have hρj : ρ₁ (ρ i) = ρ i := by
        rw [hρ₁def, Equiv.Perm.mul_apply, hj, Equiv.swap_apply_left]
      have hρy : ∀ y, y ≠ i → y ≠ ρ i → ρ₁ y = ρ y := by
        intro y hy hy'
        have h1 : ρ y ≠ i := fun hc => hy' (hρinj (hc.trans hj.symm))
        have h2 : ρ y ≠ ρ i := fun hc => hy (hρinj hc)
        rw [hρ₁def, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hinv : ∀ y, ρ₁ (ρ₁ y) = y := by
        intro y
        by_cases hy : y = i
        · subst hy; rw [hρi, hρi]
        · by_cases hy2 : y = ρ i
          · subst hy2; rw [hρj, hρj]
          · have h1 : ρ y ≠ i := fun hc => hy2 (hρinj (hc.trans hj.symm))
            have h2 : ρ y ≠ ρ i := fun hc => hy (hρinj hc)
            rw [hρy y hy hy2, hρy (ρ y) h1 h2, hρ]
      -- the support of `ρ₁` is the support of `ρ` minus `{i, ρ i}`
      have hsup₁ : ∀ y, ρ₁ y ≠ y → y ∈ (S.erase i).erase (ρ i) := by
        intro y hy
        have hyi : y ≠ i := by
          intro hc; subst hc; exact hy hρi
        have hyj : y ≠ ρ i := by
          intro hc; subst hc; exact hy hρj
        have hry : ρ y ≠ y := by rw [← hρy y hyi hyj]; exact hy
        refine Finset.mem_erase.mpr ⟨hyj, Finset.mem_erase.mpr ⟨hyi, hsub y hry⟩⟩
      have himem : i ∈ S := hsub i hi
      have hjmem : ρ i ∈ S := hsub (ρ i) (by rw [hj]; exact Ne.symm hi)
      have hlt : (S.erase i).erase (ρ i) ⊂ S := by
        refine Finset.ssubset_def.mpr
          ⟨(Finset.erase_subset (ρ i) (S.erase i)).trans (Finset.erase_subset i S), ?_⟩
        intro hc
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hc himem)).2).1 rfl
      -- the support of `ρ₁` has `2(t-1)` elements
      have hiF : i ∉ Finset.univ.filter (fun y => ρ₁ y ≠ y) := fun hc =>
        (Finset.mem_filter.mp hc).2 hρi
      have hjF : ρ i ∉ Finset.univ.filter (fun y => ρ₁ y ≠ y) := fun hc =>
        (Finset.mem_filter.mp hc).2 hρj
      have hiIns : i ∉ insert (ρ i) (Finset.univ.filter (fun y => ρ₁ y ≠ y)) := fun hc =>
        (Finset.mem_insert.mp hc).elim hij hiF
      have hcard' : (Finset.univ.filter (fun y => ρ₁ y ≠ y)).card = 2 * (t - 1) := by
        have hFeq : (Finset.univ.filter (fun y => ρ y ≠ y)) =
            insert i (insert (ρ i) (Finset.univ.filter (fun y => ρ₁ y ≠ y))) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro h
            rcases eq_or_ne y i with hc | hc
            · exact Or.inl hc
            · rcases eq_or_ne y (ρ i) with hc2 | hc2
              · exact Or.inr (Or.inl hc2)
              · exact Or.inr (Or.inr (by rw [hρy y hc hc2]; exact h))
          · rintro (hc | hc | h)
            · subst hc; exact hi
            · subst hc; rw [hj]; exact Ne.symm hi
            · have hyi : y ≠ i := by
                intro hc; subst hc; exact h hρi
              have hyj : y ≠ ρ i := by
                intro hc; subst hc; exact h hρj
              rw [← hρy y hyi hyj]
              exact h
        rw [hFeq, Finset.card_insert_of_notMem hiIns,
          Finset.card_insert_of_notMem hjF] at ht
        omega
      -- conclude by the induction hypothesis
      have htpos : 0 < t := by
        have htwo : insert (ρ i) ({i} : Finset (Fin n)) ⊆
            Finset.univ.filter (fun y => ρ y ≠ y) := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
            Finset.mem_univ, true_and] at hy ⊢
          rcases hy with hc | hc
          · rw [hc, hj]; exact Ne.symm hi
          · rw [hc]; exact hi
        have h2le := Finset.card_le_card htwo
        rw [Finset.card_insert_of_notMem (fun hmem => hi (Finset.mem_singleton.mp hmem)),
          Finset.card_singleton] at h2le
        omega
      have hsign1 : (Equiv.Perm.sign ρ₁ : ℤ) = (-1 : ℤ) ^ (t - 1) :=
        IH ((S.erase i).erase (ρ i)) hlt ρ₁ hinv hsup₁ (t - 1) hcard'
      have hsign2 : (-1 : ℤ) * (-1 : ℤ) ^ (t - 1) = (-1 : ℤ) ^ t := by
        conv_rhs => rw [show t = (t - 1).succ from (Nat.succ_pred_eq_of_pos htpos).symm,
          Nat.succ_eq_add_one, pow_succ']
      rw [hmul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
      simp only [Units.val_mul, Units.val_neg, Units.val_one, hsign1]
      exact hsign2
    · push Not at hsup
      have hid : ρ = 1 := Equiv.ext (fun y => by simpa using hsup y)
      have hcard0 : (Finset.univ.filter (fun y => ρ y ≠ y)).card = 0 := by
        refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr ?_)
        intro y hy
        exact (Finset.mem_filter.mp hy).2 (hsup y)
      rw [hcard0] at ht
      have ht0 : t = 0 := by omega
      subst ht0
      rw [hid, Equiv.Perm.sign_one, Units.val_one, pow_zero]
  exact key Finset.univ π hπ (fun i _ => Finset.mem_univ i) s hcard

open scoped Classical in
/-- FT `cg3` (Milne's "more direct" argument): let `E ⊆ ℂ` be an intermediate field over `ℚ`
stable under complex conjugation, and let `r : Fin n → E` be an injective enumeration of
elements which is closed under conjugation (each `star (r i)` is again enumerated).  If
exactly `2s` of the enumerated elements are non-real, then conjugation acts on the
discriminant square root `Δ = vandermondeDelta r` by `star Δ = (-1)^s · Δ`.  Proof:
conjugation restricts to `σ_c ∈ Gal(E/ℚ)` (`starAlgEquiv`), which permutes the enumerated
elements and induces an involution `π = inducedRootPerm` of `Fin n` whose non-fixed points
are exactly the non-real ones; `vandermondeDelta_gal_smul'` gives `σ_c • Δ = sign π · Δ`,
and `sign_involutive_perm_of_card` computes `sign π = (-1)^s`. -/
theorem star_vandermondeDelta_eq_neg_one_pow_mul {E : IntermediateField ℚ ℂ} {n : ℕ}
    (hstar : ∀ x ∈ E, star x ∈ E)
    (r : Fin n → ↥E) (hri : Function.Injective r) (s : ℕ)
    (hσ : ∀ i, star ((r i : ℂ)) ∈ Set.range (fun i : Fin n => ((r i : ℂ))))
    (hcard : (Finset.univ.filter (fun i => star ((r i : ℂ)) ≠ ((r i : ℂ)))).card = 2 * s) :
    star ((vandermondeDelta r : ↥E) : ℂ) =
      ((((-1 : ℤ) ^ s : ℤ) : ℂ)) * ((vandermondeDelta r : ↥E) : ℂ) := by
  classical
  have hvalinj : Function.Injective ⇑E.val := by
    rw [IntermediateField.coe_val]
    exact Subtype.val_injective
  set σc : Gal(↥E/ℚ) := starAlgEquiv hstar with hσcdef
  have hσapp : ∀ x : ↥E, ⇑E.val (σc x) = star (⇑E.val x) := fun x => starAlgEquiv_apply hstar x
  have hσ' : ∀ i, σc (r i) ∈ Set.range r := by
    intro i
    obtain ⟨j, hj⟩ := hσ i
    refine ⟨j, ?_⟩
    apply hvalinj
    rw [hσapp]
    exact hj
  set π := inducedRootPerm r hri σc hσ' with hπdef
  have h2 : ∀ i, r (π i) = σc (r i) := fun i => inducedRootPerm_apply r hri σc hσ' i
  have hfix : ∀ i, π i = i ↔ star ((r i : ℂ)) = ((r i : ℂ)) := by
    intro i
    constructor
    · intro h
      have h5 : ((r (π i) : ℂ)) = ((σc (r i) : ℂ)) := by rw [h2 i]
      have h6 : ((r i : ℂ)) = ((r (π i) : ℂ)) := by rw [h]
      calc star ((r i : ℂ)) = ((σc (r i) : ℂ)) := (hσapp _).symm
        _ = ((r (π i) : ℂ)) := h5.symm
        _ = ((r i : ℂ)) := h6.symm
    · intro h
      have h3 : σc (r i) = r i := hvalinj (by rw [hσapp]; exact h)
      exact hri ((h2 i).trans h3)
  have hinv : ∀ i, π (π i) = i := by
    intro i
    have h1 : r (π (π i)) = σc (r (π i)) := inducedRootPerm_apply r hri σc hσ' (π i)
    rw [h2 i] at h1
    refine hri (hvalinj ?_)
    rw [h1, hσapp, hσapp, star_star]
  have hfilters : (Finset.univ.filter (fun i => π i ≠ i)) =
      (Finset.univ.filter (fun i => star ((r i : ℂ)) ≠ ((r i : ℂ)))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (hfix i)
  have hcardπ : (Finset.univ.filter (fun i => π i ≠ i)).card = 2 * s := by
    rw [hfilters]; exact hcard
  have hsign : (Equiv.Perm.sign π : ℤ) = (-1 : ℤ) ^ s :=
    sign_involutive_perm_of_card π hinv hcardπ
  have hcomb : ⇑E.val (σc (vandermondeDelta r)) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ⇑E.val (vandermondeDelta r) := by
    have hsmul : σc • vandermondeDelta r = σc (vandermondeDelta r) := rfl
    rw [← hsmul, vandermondeDelta_gal_smul' r hri σc hσ', map_mul, map_intCast]
  rw [hsign] at hcomb
  calc star ((vandermondeDelta r : ↥E) : ℂ)
      = ⇑E.val (σc (vandermondeDelta r)) := (hσapp _).symm
    _ = ((((-1 : ℤ) ^ s : ℤ) : ℂ)) * ((vandermondeDelta r : ↥E) : ℂ) := hcomb

/-- FT `cg3` (a): if `Δ : ℂ` satisfies `star Δ = (-1)^s · Δ` with `s` odd and `Δ ≠ 0`, then
`Δ` is not the image of a rational number under `algebraMap ℚ ℂ`.  Proof: rationals are
fixed by conjugation (`star_algebraMap_rat`), so `Δ` would satisfy `Δ = star Δ = -Δ`,
forcing `Δ = 0`. -/
theorem not_algebraMap_of_star_eq_neg_one_pow_mul {s : ℕ} (hodd : Odd s) {Δ : ℂ} (hΔ : Δ ≠ 0)
    (hstar : star Δ = ((((-1 : ℤ) ^ s : ℤ) : ℂ)) * Δ) :
    ¬ ∃ a : ℚ, algebraMap ℚ ℂ a = Δ := by
  rintro ⟨a, ha⟩
  have hstar' : star Δ = -Δ := by rw [hstar, Odd.neg_one_pow hodd]; push_cast; ring
  have h1 : Δ = star Δ := by rw [← ha, star_algebraMap_rat a]
  rw [hstar'] at h1
  have h2 : Δ + Δ = 0 := eq_neg_iff_add_eq_zero.mp h1
  have h3 : (2 : ℂ) * Δ = 0 := by rw [two_mul]; exact h2
  rcases mul_eq_zero.mp h3 with h' | h'
  · exact absurd h' (by norm_num : (2 : ℂ) ≠ 0)
  · exact hΔ h'

/-- FT `cg3` (b): if `Δ : ℂ` satisfies `star Δ = (-1)^s · Δ` with `s` odd and `Δ ≠ 0`, then
`Δ²` is not a rational square.  Proof: `star Δ = -Δ` gives `Δ.re = 0`, so `Δ = Δ.im * I` and
`Δ² = -(Δ.im)²` with `Δ.im ≠ 0`, a negative real number, while a rational square is
nonnegative (`sq_nonneg`). -/
theorem sq_not_sq_algebraMap_of_star_eq_neg_one_pow_mul {s : ℕ} (hodd : Odd s) {Δ : ℂ}
    (hΔ : Δ ≠ 0) (hstar : star Δ = ((((-1 : ℤ) ^ s : ℤ) : ℂ)) * Δ) :
    ¬ ∃ a : ℚ, algebraMap ℚ ℂ a * algebraMap ℚ ℂ a = Δ ^ 2 := by
  rintro ⟨a, ha⟩
  have hstar' : star Δ = -Δ := by rw [hstar, Odd.neg_one_pow hodd]; push_cast; ring
  have hre : Δ.re = 0 := by
    have h1 : Δ.re = (-Δ).re := by rw [← hstar', Complex.star_def, Complex.conj_re]
    rw [Complex.neg_re] at h1
    linarith
  have him : Δ.im ≠ 0 := by
    intro hc
    exact hΔ (Complex.ext hre (by simp [hc]))
  have hval : Δ = (Δ.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im Δ, hre]
    simp
  have hsq : Δ ^ 2 = ((-(Δ.im) ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hval, mul_pow,
      show Complex.I ^ 2 = -1 from by rw [pow_two, Complex.I_mul_I]]
    push_cast
    ring
  have hpos : (0 : ℝ) < Δ.im ^ 2 := sq_pos_of_ne_zero him
  have hreal : (((a * a : ℚ) : ℝ) : ℂ) = ((-(Δ.im) ^ 2 : ℝ) : ℂ) := by
    rw [← hsq, ← ha]
    simp
  have hsqeq : ((a * a : ℚ) : ℝ) = (-(Δ.im) ^ 2 : ℝ) := Complex.ofReal_injective hreal
  have hxx : ((a * a : ℚ) : ℝ) = ((a : ℚ) : ℝ) ^ 2 := by push_cast; ring
  linarith [sq_nonneg (((a : ℚ) : ℝ)), hpos]

open scoped Classical in
/-- FT `cg3` (a), instantiated: with the hypotheses of
`star_vandermondeDelta_eq_neg_one_pow_mul` and `s` odd, `Δ = vandermondeDelta r` is not
rational: a rational `a` with `algebraMap ℚ ℂ a = Δ` would satisfy `a = star a = star Δ =
-Δ`, forcing `Δ = 0`, contradicting `Δ ≠ 0` (which follows from the injectivity of `r` via
`vandermondeProd_ne_zero`). -/
theorem vandermondeDelta_not_algebraMap_of_s_odd {E : IntermediateField ℚ ℂ} {n : ℕ}
    (hstar : ∀ x ∈ E, star x ∈ E)
    (r : Fin n → ↥E) (hri : Function.Injective r) (s : ℕ)
    (hσ : ∀ i, star ((r i : ℂ)) ∈ Set.range (fun i : Fin n => ((r i : ℂ))))
    (hcard : (Finset.univ.filter (fun i => star ((r i : ℂ)) ≠ ((r i : ℂ)))).card = 2 * s)
    (hodd : Odd s) :
    ¬ ∃ a : ℚ, algebraMap ℚ ℂ a = ((vandermondeDelta r : ↥E) : ℂ) := by
  have hv : Function.Injective ⇑E.val := by
    rw [IntermediateField.coe_val]; exact Subtype.val_injective
  refine not_algebraMap_of_star_eq_neg_one_pow_mul hodd ?_
    (star_vandermondeDelta_eq_neg_one_pow_mul hstar r hri s hσ hcard)
  intro hc
  refine vandermondeProd_ne_zero r hri (hv ?_)
  calc ⇑E.val (vandermondeDelta r) = ((vandermondeDelta r : ↥E) : ℂ) := rfl
    _ = 0 := hc
    _ = ⇑E.val 0 := (map_zero _).symm

open scoped Classical in
/-- FT `cg3` (b), instantiated: with the hypotheses of
`star_vandermondeDelta_eq_neg_one_pow_mul` and `s` odd, `D(f) = Δ²` is not a square in `ℚ`:
a rational square is a nonnegative real number, while `Δ² = -(Δ.im)² < 0` since
`star Δ = -Δ` and `Δ ≠ 0`. -/
theorem vandermondeDelta_sq_not_sq_algebraMap_of_s_odd {E : IntermediateField ℚ ℂ} {n : ℕ}
    (hstar : ∀ x ∈ E, star x ∈ E)
    (r : Fin n → ↥E) (hri : Function.Injective r) (s : ℕ)
    (hσ : ∀ i, star ((r i : ℂ)) ∈ Set.range (fun i : Fin n => ((r i : ℂ))))
    (hcard : (Finset.univ.filter (fun i => star ((r i : ℂ)) ≠ ((r i : ℂ)))).card = 2 * s)
    (hodd : Odd s) :
    ¬ ∃ a : ℚ, algebraMap ℚ ℂ a * algebraMap ℚ ℂ a = ((vandermondeDelta r : ↥E) : ℂ) ^ 2 := by
  have hv : Function.Injective ⇑E.val := by
    rw [IntermediateField.coe_val]; exact Subtype.val_injective
  refine sq_not_sq_algebraMap_of_star_eq_neg_one_pow_mul hodd ?_
    (star_vandermondeDelta_eq_neg_one_pow_mul hstar r hri s hσ hcard)
  intro hc
  refine vandermondeProd_ne_zero r hri (hv ?_)
  calc ⇑E.val (vandermondeDelta r) = ((vandermondeDelta r : ↥E) : ℂ) := rfl
    _ = 0 := hc
    _ = ⇑E.val 0 := (map_zero _).symm

open scoped Polynomial in
open scoped Classical in
/-- FT `cg3` (the remark's content): let `f ∈ ℚ[X]` be separable and split in `ℂ`, let
`E₀ = ℚ(adjoin the complex roots of f)` (a splitting field of `f` in `ℂ`), and let
`r : Fin n → E₀` enumerate its roots injectively (range = root set of `f` in `E₀`).  If
exactly `2s` of the roots are non-real and `s` is odd, then not every element of
`Gal(E₀/ℚ)` induces an even permutation of the roots, i.e. `G_f` is not contained in `A_n`
in the sense of `FT.gal_even_iff_delta_mem` (whose left side this negates; equivalently,
`Δ ∉ ℚ` and `D(f)` is not a rational square).  Proof: conjugation preserves the root set of
a rational polynomial (`star_rootSet_iff`), so it restricts to `Gal(E₀/ℚ)` and
`star_vandermondeDelta_eq_neg_one_pow_mul` gives `star Δ = (-1)^s Δ`; since `Δ ≠ 0`
(`vandermondeProd_ne_zero`) and `s` is odd, `vandermondeDelta_not_algebraMap_of_s_odd`
gives `Δ ∉ ℚ`; but `gal_even_iff_delta_mem` shows that all-even would force `Δ ∈ ℚ`. -/
theorem not_forall_sign_eq_one_of_s_odd {f : ℚ[X]} {n : ℕ} (hf : f.Separable)
    (hsplits : (f.map (algebraMap ℚ ℂ)).Splits)
    (r : Fin n → ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) (hri : Function.Injective r)
    (hr : Set.range r =
      (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))).rootSet
        ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))
    (s : ℕ) (hodd : Odd s)
    (hcard : (Finset.univ.filter (fun i => star ((r i : ℂ)) ≠ ((r i : ℂ)))).card = 2 * s) :
    ¬ ∀ σ : Gal(↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))/ℚ),
        Equiv.Perm.sign (inducedRootPerm r hri σ
          (fun i => gal_apply_mem_range f hf.ne_zero hr σ i)) = 1 := by
  intro hall
  haveI hsplit : Polynomial.IsSplittingField ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplits
  haveI : IsGalois ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    IsGalois.of_separable_splitting_field hf
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  obtain ⟨a, ha⟩ := (gal_even_iff_delta_mem f hf.ne_zero hr hri
    (vandermondeProd_ne_zero r hri) (two_ne_zero_algebraMap (by norm_num : (2 : ℚ) ≠ 0))).mp hall
  have hv : Function.Injective ⇑(IntermediateField.adjoin ℚ (f.rootSet ℂ)).val := by
    rw [IntermediateField.coe_val]; exact Subtype.val_injective
  have hΔc : ((vandermondeDelta r : ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) : ℂ) ≠ 0 := by
    intro hc
    refine vandermondeProd_ne_zero r hri (hv ?_)
    calc ⇑(IntermediateField.adjoin ℚ (f.rootSet ℂ)).val (vandermondeDelta r)
        = ((vandermondeDelta r : ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) : ℂ) := rfl
      _ = 0 := hc
      _ = ⇑(IntermediateField.adjoin ℚ (f.rootSet ℂ)).val 0 := (map_zero _).symm
  have hstar0 : ∀ x ∈ IntermediateField.adjoin ℚ (f.rootSet ℂ),
      star x ∈ IntermediateField.adjoin ℚ (f.rootSet ℂ) := fun _ hx => star_mem_adjoin_rootSet hx
  have hσ0 : ∀ i, star ((r i : ℂ)) ∈ Set.range (fun i : Fin n => ((r i : ℂ))) := by
    intro i
    have hmemU : r i ∈ (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))).rootSet
        ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) := hr ▸ (⟨i, rfl⟩ : r i ∈ Set.range r)
    have hae : aeval (r i) (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))) = 0 :=
      (Polynomial.mem_rootSet'.mp hmemU).2
    rw [Polynomial.aeval_map_algebraMap] at hae
    have h2 : star ((r i : ℂ)) ∈ f.rootSet ℂ := by
      rw [Polynomial.mem_rootSet']
      refine ⟨(Polynomial.map_ne_zero_iff
        (RingHom.injective (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))))).mpr
        hf.ne_zero, ?_⟩
      rw [aeval_star, (aeval_E_eq_zero_iff _).mp hae, star_zero]
    have h3 : star ((r i : ℂ)) ∈ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
      star_mem_adjoin_rootSet (IntermediateField.subset_adjoin ℚ (f.rootSet ℂ) h2)
    have hy : (⟨star ((r i : ℂ)), h3⟩ : ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) ∈
        (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))).rootSet
          ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) := by
      rw [Polynomial.mem_rootSet']
      refine ⟨(Polynomial.map_ne_zero_iff
        (RingHom.injective (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))))).mpr
        hf.ne_zero, ?_⟩
      have hcoeeq : ((⟨star ((r i : ℂ)), h3⟩ :
        ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) : ℂ) = star ((r i : ℂ)) := rfl
      rw [Polynomial.aeval_map_algebraMap, aeval_E_eq_zero_iff _, hcoeeq, aeval_star,
        (aeval_E_eq_zero_iff _).mp hae, star_zero]
    have hyr : (⟨star ((r i : ℂ)), h3⟩ : ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) ∈
        Set.range r := by
      rw [hr]
      exact hy
    obtain ⟨j, hj⟩ := hyr
    exact ⟨j, by rw [hj]⟩
  refine vandermondeDelta_not_algebraMap_of_s_odd hstar0 r hri s hσ0 hcard hodd ⟨a, ?_⟩
  calc algebraMap ℚ ℂ a
      = ⇑(IntermediateField.adjoin ℚ (f.rootSet ℂ)).val
          (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) a) :=
        (AlgHom.map_algebraMap _ a).symm
    _ = ⇑(IntermediateField.adjoin ℚ (f.rootSet ℂ)).val (vandermondeDelta r) := by rw [ha]
    _ = ((vandermondeDelta r : ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) : ℂ) := rfl
