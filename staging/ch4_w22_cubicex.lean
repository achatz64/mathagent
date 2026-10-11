-- staging/ch4_w22_cubicex.lean — worker w22, delivered verbatim (transcription slips to fix
-- at integration: "push Not at hcon" → push_neg; "refine hm.irreducible_iff_natDegree,
-- and_iff_right hf1]" malformed; verify names irreducible_iff_natDegree etc. in REPL).
-- Setup: E explicit parameter with hE : E = adjoin ℚ (rootSet ℂ) (TC-search workaround);
-- four main theorems need maxHeartbeats 1000000. Axioms: propext/Classical.choice/Quot.sound.
/-! ## FT chapter IV §3 (cg6): the two concrete cubic examples `X³ − 3X + 1` and `X³ + 3X + 1` -/

section Cg6CubicExamples

open Polynomial

/-- FT cg6 (auxiliary).  Coefficients of the depressed cubic `X³ − a·X + b`. -/
theorem coeffDepressedCubic {K : Type*} [CommRing K] (a b : K) (n : ℕ) :
    (X ^ 3 - C a * X + C b : K[X]).coeff n
      = if n = 3 then 1 else if n = 1 then -a else if n = 0 then b else 0 := by
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
      if_neg (show ¬((n:ℕ)+4 = 3) by omega),
      if_neg (show ¬((n:ℕ)+4 = 1) by omega),
      if_neg (show ¬((n:ℕ)+4 = 0) by omega)]
    norm_num

/-- FT cg6 (auxiliary).  The depressed cubic `X³ − a·X + b` is monic of degree `3` (for
`1 ≠ 0` in `K`). -/
theorem monicNatDegreeDepressedCubic {K : Type*} [CommRing K] [Nontrivial K] {a b : K} :
    (X ^ 3 - C a * X + C b : K[X]).Monic ∧ (X ^ 3 - C a * X + C b : K[X]).natDegree = 3 := by
  have hle : (X ^ 3 - C a * X + C b : K[X]).natDegree ≤ 3 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeffDepressedCubic]
    split_ifs with h3c h1c h0c
    · omega
    · omega
    · omega
    · rfl
  have hc : (X ^ 3 - C a * X + C b : K[X]).coeff 3 ≠ 0 := by
    rw [coeffDepressedCubic]
    norm_num
  have hnd := le_antisymm hle
    (Nat.le_of_not_gt fun hlt => hc (Polynomial.coeff_eq_zero_of_natDegree_lt hlt))
  refine ⟨?_, hnd⟩
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hnd, coeffDepressedCubic]
  norm_num

/-- FT cg6 (auxiliary).  A monic degree-one factor `X + c` of `f` over an integral domain
gives the root `−c` of `f`. -/
theorem rootOfMonicFactorNatDegreeOne {K : Type*} [CommRing K] {f g h : K[X]}
    (he : g * h = f) (hg : g.Monic) (h1 : g.natDegree = 1) :
    f.eval (-(g.coeff 0)) = 0 := by
  rw [← he, Polynomial.eval_mul, hg.eq_X_add_C h1]
  simp

/-- FT cg6 (auxiliary, `ef4`/`ef5` route).  A monic cubic over an integral domain with no root
in the domain is irreducible: any nontrivial factorization has a monic degree-one factor
`X + c`, whose negated constant term is a root. -/
theorem irreducibleMonicCubicOfNoRoot {K : Type*} [CommRing K] [IsDomain K] {f : K[X]}
    (hm : f.Monic) (h3 : f.natDegree = 3) (hno : ∀ a : K, f.eval a ≠ 0) : Irreducible f := by
  have hf1 : f ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at h3
    simp at h3
  rw [hm.irreducible_iff_natDegree, and_iff_right hf1]
  intro g h hg hh he
  have hg0 : g ≠ 0 := hg.ne_zero
  have hh0 : h ≠ 0 := hh.ne_zero
  have hsum : g.natDegree + h.natDegree = 3 := by
    have h0 : (g * h).natDegree = 3 := by rw [he]; exact h3
    rw [Polynomial.natDegree_mul hg0 hh0] at h0
    exact h0
  by_contra hcon
  push_neg at hcon
  have hchoice : g.natDegree = 1 ∨ h.natDegree = 1 := by omega
  rcases hchoice with hdeg1 | hdeg1
  · exact hno (-(g.coeff 0)) (rootOfMonicFactorNatDegreeOne he hg hdeg1)
  · rw [mul_comm g h] at he
    exact hno (-(h.coeff 0)) (rootOfMonicFactorNatDegreeOne he hh hdeg1)

/-- FT cg6 (auxiliary for the root tests `ef4`/`ef5`).  Both depressed cubics `t³ − 3t + 1` and
`t³ + 3t + 1` take odd values at every integer `t`, hence have no integer root. -/
theorem oddValuesDepressedCubics (r : ℤ) :
    (r ^ 3 - 3 * r + 1 : ℤ) % 2 = 1 ∧ (r ^ 3 + 3 * r + 1 : ℤ) % 2 = 1 := by
  rcases Int.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    refine ⟨?_, ?_⟩
    · have h2 : (k + k) ^ 3 - 3 * (k + k) + 1 = 1 + 2 * (4 * k ^ 3 - 3 * k) := by ring
      rw [h2]
      omega
    · have h2 : (k + k) ^ 3 + 3 * (k + k) + 1 = 1 + 2 * (4 * k ^ 3 + 3 * k) := by ring
      rw [h2]
      omega
  · subst hk
    refine ⟨?_, ?_⟩
    · have h2 : (2 * k + 1) ^ 3 - 3 * (2 * k + 1) + 1 = 1 + 2 * (4 * k ^ 3 + 6 * k ^ 2 - 1) := by
        ring
      rw [h2]
      omega
    · have h2 : (2 * k + 1) ^ 3 + 3 * (2 * k + 1) + 1 = 1 + 2 * (4 * k ^ 3 + 6 * k ^ 2 + 6 * k + 2) := by
        ring
      rw [h2]
      omega

/-- FT cg6 (auxiliary).  Integer evaluation of `X³ − 3X + 1` and of `X³ − (−3)·X + 1`. -/
theorem evalX3SubInt (r : ℤ) :
    eval r (X ^ 3 - C (3:ℤ) * X + C (1:ℤ) : ℤ[X]) = r ^ 3 - 3 * r + 1 ∧
    eval r (X ^ 3 - C (-(3:ℤ)) * X + C (1:ℤ) : ℤ[X]) = r ^ 3 + 3 * r + 1 := by
  refine ⟨?_, ?_⟩ <;>
  · simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]

/-- FT ef5 (rational root test): `X³ − 3X + 1` is irreducible over `ℤ` (its values at integers
are odd, by `oddValuesDepressedCubics`), hence over `ℚ` by Gauss's lemma
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`). -/
theorem irreducible_X3_sub_3X_add_1 : Irreducible (X ^ 3 - C 3 * X + C 1 : ℚ[X]) := by
  have hmap : (X ^ 3 - C 3 * X + C 1 : ℚ[X])
      = (X ^ 3 - C (3:ℤ) * X + C (1:ℤ) : ℤ[X]).map (algebraMap ℤ ℚ) := by
    refine Polynomial.ext fun n => ?_
    simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  rw [hmap]
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (monicNatDegreeDepressedCubic (K := ℤ) (a := 3) (b := 1)).1).mp
    (irreducibleMonicCubicOfNoRoot (monicNatDegreeDepressedCubic (K := ℤ) (a := 3) (b := 1)).1
      (monicNatDegreeDepressedCubic (K := ℤ) (a := 3) (b := 1)).2
      (by intro r hr
          have hodd := (oddValuesDepressedCubics r).1
          rw [(evalX3SubInt r).1] at hr
          rw [hr] at hodd
          norm_num at hodd))

/-- FT ef4 (rational root test): `X³ + 3X + 1` is irreducible over `ℤ` (its values at integers
are odd, by `oddValuesDepressedCubics`), hence over `ℚ` by Gauss's lemma. -/
theorem irreducible_X3_add_3X_add_1 : Irreducible (X ^ 3 + C 3 * X + C 1 : ℚ[X]) := by
  have hmap : (X ^ 3 - C (-(3:ℚ)) * X + C 1 : ℚ[X])
      = (X ^ 3 - C (-(3:ℤ)) * X + C (1:ℤ) : ℤ[X]).map (algebraMap ℤ ℚ) := by
    refine Polynomial.ext fun n => ?_
    simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hform : (X ^ 3 + C 3 * X + C 1 : ℚ[X])
      = (X ^ 3 - C (-(3:ℚ)) * X + C 1 : ℚ[X]) := by
    simp only [Polynomial.C_neg]
    rw [sub_eq_add_neg, neg_mul, neg_neg]
  rw [hform, hmap]
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (monicNatDegreeDepressedCubic (K := ℤ) (a := -(3:ℤ)) (b := 1)).1).mp
    (irreducibleMonicCubicOfNoRoot (monicNatDegreeDepressedCubic (K := ℤ) (a := -(3:ℤ)) (b := 1)).1
      (monicNatDegreeDepressedCubic (K := ℤ) (a := -(3:ℤ)) (b := 1)).2
      (by intro r hr
          have hodd := (oddValuesDepressedCubics r).2
          rw [(evalX3SubInt r).2] at hr
          rw [hr] at hodd
          norm_num at hodd))

/-- FT cg6 (setup for the two cubic examples).  For `f : ℚ[X]` monic, separable, irreducible
of degree `3` that splits over `ℂ`, the field `E := IntermediateField.adjoin ℚ (f.rootSet ℂ)`
is a finite Galois splitting field of `f`, and `f` has three pairwise distinct roots
`u, v, w ∈ E` realizing the factorization `f = (X − u)(X − v)(X − w)` over `E` and generating
the root set. -/
theorem cubicExampleData {f : ℚ[X]} (hmq : f.Monic) (hsep : f.Separable)
    (hirr : Irreducible f) (h3q : f.natDegree = 3) :
    ∃ (E : IntermediateField ℚ ℂ), E = IntermediateField.adjoin ℚ (f.rootSet ℂ) ∧
      f.IsSplittingField ℚ ↥E ∧ IsGalois ℚ ↥E ∧ FiniteDimensional ℚ ↥E ∧
      (f.map (algebraMap ℚ ↥E)).Splits ∧ IntermediateField.adjoin ℚ (f.rootSet ↥E) = ⊤ ∧
      ∃ u v w : ↥E, f.map (algebraMap ℚ ↥E) = (X - C u) * (X - C v) * (X - C w) ∧
        u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ (Polynomial.aeval u) f = 0 ∧
        (Polynomial.aeval v) f = 0 ∧ (Polynomial.aeval w) f = 0 ∧
        ∀ x ∈ f.rootSet ↥E, x = u ∨ x = v ∨ x = w := by
  classical
  have hsplitC : (f.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  haveI hsp : f.IsSplittingField ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplitC
  have hsplit : (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))).Splits :=
    hsp.splits
  haveI hgal : IsGalois ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    IsGalois.of_separable_splitting_field hsep
  haveI hfd : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  have hgen : IntermediateField.adjoin ℚ
      (f.rootSet ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ))) = ⊤ := by
    refine top_le_iff.mp (fun x _ => ?_)
    exact IntermediateField.algebra_adjoin_le_adjoin ℚ
      (f.rootSet ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) :
        Set ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))
      (by rw [Polynomial.IsSplittingField.adjoin_rootSet
        ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)) f]; trivial)
  obtain ⟨u, v, w, hR, huv, huw, hvw, hchar⟩ := cubic_roots_extract hmq hsep hsplit h3q
  have hcard : (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))).roots.card
      = (f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))).natDegree := by
    rw [(Polynomial.splits_iff_card_roots).mp hsplit]
  have hfac : f.map (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (f.rootSet ℂ)))
      = (X - C u) * (X - C v) * (X - C w) := by
    rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (hmq.map (algebraMap ℚ _)) hcard, hR]
    simp
    ring
  refine ⟨IntermediateField.adjoin ℚ (f.rootSet ℂ), rfl, hsp, hgal, hfd, hsplit, hgen,
    u, v, w, hfac, huv, huw, hvw, ?_, ?_, ?_, fun x hx => (hchar x).mp hx⟩
  · exact (Polynomial.mem_rootSet.mp (hchar u |>.mpr (Or.inl rfl))).2
  · exact (Polynomial.mem_rootSet.mp (hchar v |>.mpr (Or.inr (Or.inl rfl)))).2
  · exact (Polynomial.mem_rootSet.mp (hchar w |>.mpr (Or.inr (Or.inr rfl)))).2

set_option maxHeartbeats 1000000 in
/-- FT cg6, first cubic example.  `X³−3X+1` irreducible, discriminant 81 = 9², |Gal| = 3. -/
theorem galCard_splittingField_X3_sub_3X_add_1_eq_three (E : IntermediateField ℚ ℂ)
    (hE : E = IntermediateField.adjoin ℚ ((X ^ 3 - C 3 * X + C 1 : ℚ[X]).rootSet ℂ)) :
    Nat.card Gal(↥E/ℚ) = 3 := by
  classical
  set f : ℚ[X] := X ^ 3 - C 3 * X + C 1 with hfdef
  have hmq : f.Monic := (monicNatDegreeDepressedCubic (K := ℚ) (a := 3) (b := 1)).1
  have h3 : f.natDegree = 3 := (monicNatDegreeDepressedCubic (K := ℚ) (a := 3) (b := 1)).2
  have hirr : Irreducible f := irreducible_X3_sub_3X_add_1
  have hsep : f.Separable := hirr.separable
  obtain ⟨E₀, hE₀, hsp, hgal, hfd, hsplit, hgen, u, v, w, hfac, huv, huw, hvw, hu, hv, hw, hchar⟩ :=
    cubicExampleData hmq hsep hirr h3
  haveI : IsGalois ℚ ↥E₀ := hgal
  haveI : FiniteDimensional ℚ ↥E₀ := hfd
  have hEE : E₀ = E := hE₀.trans hE.symm
  rw [← hEE]
  have hsign : (X ^ 3 + C (-(3 : ↥E₀)) * X + C 1 : Polynomial ↥E₀)
      = (X - C u) * (X - C v) * (X - C w) := by
    have hmp : map (algebraMap ℚ ↥E₀) f
        = (X ^ 3 + C (-(3 : ↥E₀)) * X + C 1 : Polynomial ↥E₀) := by
      rw [hfdef]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X]
      norm_num
      rw [← sub_eq_add_neg]
    rw [← hmp, hfac]
  obtain hD := disc_cubic_vieta hsign
  rw [← cubic_galCard_three_iff_discriminant_square hmq hsep hirr h3 hsplit hgen
    (by norm_num : (2:ℚ) ≠ 0)]
  refine ⟨u, v, w, hu, hv, hw, huv, huw, hvw, 9, ?_⟩
  rw [← map_mul, mul_pow, mul_pow, hD]
  norm_num

set_option maxHeartbeats 1000000 in
/-- FT cg6, second cubic example.  `X³+3X+1` irreducible, discriminant −135 not a square, |Gal| = 6. -/
theorem galCard_splittingField_X3_add_3X_add_1_eq_six (E : IntermediateField ℚ ℂ)
    (hE : E = IntermediateField.adjoin ℚ ((X ^ 3 + C 3 * X + C 1 : ℚ[X]).rootSet ℂ)) :
    Nat.card Gal(↥E/ℚ) = 6 := by
  classical
  set f : ℚ[X] := X ^ 3 - C (-(3:ℚ)) * X + C 1 with hfdef
  have hform : (X ^ 3 + C 3 * X + C 1 : ℚ[X]) = f := by
    rw [hfdef, Polynomial.C_neg, neg_mul, sub_neg_eq_add]
  have hmq : f.Monic := (monicNatDegreeDepressedCubic (K := ℚ) (a := -(3:ℚ)) (b := 1)).1
  have h3 : f.natDegree = 3 := (monicNatDegreeDepressedCubic (K := ℚ) (a := -(3:ℚ)) (b := 1)).2
  have hirr : Irreducible f := by rw [← hform]; exact irreducible_X3_add_3X_add_1
  have hsep : f.Separable := hirr.separable
  have hf0 : f ≠ 0 := hmq.ne_zero
  rw [hform] at hE
  obtain ⟨E₀, hE₀, hsp, hgal, hfd, hsplit, hgen, u, v, w, hfac, huv, huw, hvw, hu, hv, hw, hchar⟩ :=
    cubicExampleData hmq hsep hirr h3
  haveI : IsGalois ℚ ↥E₀ := hgal
  haveI : FiniteDimensional ℚ ↥E₀ := hfd
  have hEE : E₀ = E := hE₀.trans hE.symm
  rw [← hEE]
  have hsign : (X ^ 3 + C 3 * X + C 1 : Polynomial ↥E₀)
      = (X - C u) * (X - C v) * (X - C w) := by
    have hmp : map (algebraMap ℚ ↥E₀) f
        = (X ^ 3 + C 3 * X + C 1 : Polynomial ↥E₀) := by
      rw [hfdef]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X]
      norm_num
    rw [← hmp, hfac]
  obtain hD := disc_cubic_vieta hsign
  have hD' : ((u - v) * (u - w) * (v - w)) ^ 2 = (-(135 : ↥E₀)) := by
    rw [mul_pow, mul_pow, hD]
    norm_num
  have hcontra : ∀ t : ℚ, algebraMap ℚ ↥E₀ t * algebraMap ℚ ↥E₀ t
      = ((u - v) * (u - w) * (v - w)) ^ 2 → False := by
    intro t ht
    rw [hD'] at ht
    rw [← map_mul] at ht
    have h2 : (-(135 : ↥E₀)) = algebraMap ℚ ↥E₀ (-(135:ℚ)) := by norm_num
    rw [h2] at ht
    have hsq : (t * t : ℚ) = -(135:ℚ) := injective_algebraMap_intermediateField E₀ ht
    have hnn : (0:ℚ) ≤ t * t := by rw [← sq]; exact sq_nonneg t
    rw [hsq] at hnn
    norm_num at hnn
  obtain ⟨-, -, hdisj⟩ := cubic_galCard_count hmq hsep hirr h3 hsplit hgen
  rcases hdisj with h3c | h6c
  · exfalso
    obtain ⟨u', v', w', hu'', hv'', hw'', hu'v', hu'w', hv'w', t, ht⟩ :=
      (cubic_galCard_three_iff_discriminant_square hmq hsep hirr h3 hsplit hgen
        (by norm_num : (2:ℚ) ≠ 0)).mpr h3c
    have hu'm : u' ∈ f.rootSet ↥E₀ := Polynomial.mem_rootSet.mpr ⟨hf0, hu''⟩
    have hv'm : v' ∈ f.rootSet ↥E₀ := Polynomial.mem_rootSet.mpr ⟨hf0, hv''⟩
    have hw'm : w' ∈ f.rootSet ↥E₀ := Polynomial.mem_rootSet.mpr ⟨hf0, hw''⟩
    rcases triple_perm_cases (hchar u' hu'm) (hchar v' hv'm) (hchar w' hw'm)
      hu'v' hu'w' hv'w' with hc | hc | hc | hc | hc | hc
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      exact hcontra t ht
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [(by ring : ((u' - v') * (u' - w') * (v' - w')) ^ 2
          = ((v' - u') * (v' - w') * (u' - w')) ^ 2)] at ht
      exact hcontra t ht
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [(by ring : ((u' - v') * (u' - w') * (v' - w')) ^ 2
          = ((w' - v') * (w' - u') * (v' - u')) ^ 2)] at ht
      exact hcontra t ht
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [(by ring : ((u' - v') * (u' - w') * (v' - w')) ^ 2
          = ((u' - w') * (u' - v') * (w' - v')) ^ 2)] at ht
      exact hcontra t ht
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [(by ring : ((u' - v') * (u' - w') * (v' - w')) ^ 2
          = ((w' - u') * (w' - v') * (u' - v')) ^ 2)] at ht
      exact hcontra t ht
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [(by ring : ((u' - v') * (u' - w') * (v' - w')) ^ 2
          = ((v' - w') * (v' - u') * (w' - u')) ^ 2)] at ht
      exact hcontra t ht
  · exact h6c

set_option maxHeartbeats 1000000 in
/-- FT cg6, first cubic example (transitivity clause). -/
theorem gal_transitive_splittingField_X3_sub_3X_add_1 (E : IntermediateField ℚ ℂ)
    (hE : E = IntermediateField.adjoin ℚ ((X ^ 3 - C 3 * X + C 1 : ℚ[X]).rootSet ℂ)) :
    ∀ α ∈ (X ^ 3 - C 3 * X + C 1 : ℚ[X]).rootSet ↥E,
      ∀ β ∈ (X ^ 3 - C 3 * X + C 1 : ℚ[X]).rootSet ↥E, ∃ σ : Gal(↥E/ℚ), σ α = β := by
  classical
  set f : ℚ[X] := X ^ 3 - C 3 * X + C 1 with hfdef
  have hmq : f.Monic := (monicNatDegreeDepressedCubic (K := ℚ) (a := 3) (b := 1)).1
  have h3 : f.natDegree = 3 := (monicNatDegreeDepressedCubic (K := ℚ) (a := 3) (b := 1)).2
  have hirr : Irreducible f := irreducible_X3_sub_3X_add_1
  have hsep : f.Separable := hirr.separable
  obtain ⟨E₀, hE₀, hsp, hgal, hfd, hsplit, hgen, u, v, w, hfac, huv, huw, hvw, hu, hv, hw, hchar⟩ :=
    cubicExampleData hmq hsep hirr h3
  haveI : IsGalois ℚ ↥E₀ := hgal
  haveI : FiniteDimensional ℚ ↥E₀ := hfd
  have hEE : E₀ = E := hE₀.trans hE.symm
  rw [← hEE]
  exact (gal_transitive_iff_irreducible hmq hsep hsplit (by rw [h3]; norm_num)).mp hirr

set_option maxHeartbeats 1000000 in
/-- FT cg6, second cubic example (transitivity clause). -/
theorem gal_transitive_splittingField_X3_add_3X_add_1 (E : IntermediateField ℚ ℂ)
    (hE : E = IntermediateField.adjoin ℚ ((X ^ 3 + C 3 * X + C 1 : ℚ[X]).rootSet ℂ)) :
    ∀ α ∈ (X ^ 3 + C 3 * X + C 1 : ℚ[X]).rootSet ↥E,
      ∀ β ∈ (X ^ 3 + C 3 * X + C 1 : ℚ[X]).rootSet ↥E, ∃ σ : Gal(↥E/ℚ), σ α = β := by
  classical
  set f : ℚ[X] := X ^ 3 - C (-(3:ℚ)) * X + C 1 with hfdef
  have hform : (X ^ 3 + C 3 * X + C 1 : ℚ[X]) = f := by
    rw [hfdef, Polynomial.C_neg, neg_mul, sub_neg_eq_add]
  have hmq : f.Monic := (monicNatDegreeDepressedCubic (K := ℚ) (a := -(3:ℚ)) (b := 1)).1
  have h3 : f.natDegree = 3 := (monicNatDegreeDepressedCubic (K := ℚ) (a := -(3:ℚ)) (b := 1)).2
  have hirr : Irreducible f := by rw [← hform]; exact irreducible_X3_add_3X_add_1
  have hsep : f.Separable := hirr.separable
  rw [hform] at hE
  obtain ⟨E₀, hE₀, hsp, hgal, hfd, hsplit, hgen, u, v, w, hfac, huv, huw, hvw, hu, hv, hw, hchar⟩ :=
    cubicExampleData hmq hsep hirr h3
  haveI : IsGalois ℚ ↥E₀ := hgal
  haveI : FiniteDimensional ℚ ↥E₀ := hfd
  have hEE : E₀ = E := hE₀.trans hE.symm
  rw [← hEE, hform]
  exact (gal_transitive_iff_irreducible hmq hsep hsplit (by rw [h3]; norm_num)).mp hirr

end Cg6CubicExamples
