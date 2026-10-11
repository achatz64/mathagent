-- STAGING: FT cg6 dichotomy (discriminant square ↔ |G| = 3) + A₃ corollary,
-- re-derivation worker w19 deliverable, received verbatim. All nine declarations
-- verified in shared REPL gen 9; temp-name mapping (byte-identical modulo rename):
--   cg6_gal_smul_root_tmp2 → cg6_gal_smul_root, cg6_perm_cases_tmp7 → cg6_perm_cases,
--   cg6_roots_extract_tmp5 → cg6_roots_extract, cg6_finset_char_tmp3 → cg6_finset_char,
--   cg6_perm_triple_tmp7 → cg6_perm_triple, cg6_delta_fixed_tmp8 → cg6_delta_fixed,
--   cg6_card3_of_fixed_tmp4 → cg6_card3_of_fixed, cg6_dichotomy_tmp6 → cg6_dichotomy,
--   cg6_a3_cycle_tmp6 → cg6_a3_cycle.
-- Char-2 caveat (worker scope note 1): the literal statement is false in char 2;
-- h2 : (2 : F) ≠ 0 hypothesis mirrors the cg5 precedent.
-- Paste inside namespace FT (drop the open/namespace wrapper lines below).

-- FT cg6 (action on roots)
/-- A root of `f` is sent to a root of `f` by any `F`-algebra automorphism of `E`. -/
theorem cg6_gal_smul_root {F E : Type u} [Field F] [Field E] [Algebra F E] {f : F[X]}
    (hf : f ≠ 0) (σ : Gal(E/F)) {x : E} (hx : x ∈ f.rootSet E) : σ x ∈ f.rootSet E := by
  rw [Polynomial.mem_rootSet] at hx ⊢
  refine ⟨hf, ?_⟩
  have h2 : aeval (σ x) f = σ.toAlgHom (aeval x f) := aeval_algHom_apply σ.toAlgHom x f
  rw [h2, hx.2, map_zero]

-- FT cg6 (pure permutation bookkeeping)
/-- Three pairwise distinct elements, each equal to one of `u, v, w`, realize one of the six
permutations of `(u, v, w)`. -/
theorem cg6_perm_cases {E : Type*} {u v w a b c : E}
    (ha : a = u ∨ a = v ∨ a = w) (hb : b = u ∨ b = v ∨ b = w) (hc : c = u ∨ c = v ∨ c = w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a = u ∧ b = v ∧ c = w) ∨ (a = v ∧ b = u ∧ c = w) ∨ (a = w ∧ b = v ∧ c = u) ∨
      (a = u ∧ b = w ∧ c = v) ∨ (a = v ∧ b = w ∧ c = u) ∨ (a = w ∧ b = u ∧ c = v) := by
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact absurd rfl hac
      | exact absurd rfl hbc
      | exact Or.inl ⟨rfl, rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))

-- FT cg6 (the three roots)
/-- A monic separable cubic that splits in `E` has exactly three roots `u, v, w` of multiplicity
one, and its root set is exactly `{u, v, w}`. -/
theorem cg6_roots_extract {F E : Type u} [Field F] [Field E] [Algebra F E] {f : F[X]}
    (hf : f.Monic) (hsep : f.Separable) (hsplit : (f.map (algebraMap F E)).Splits)
    (h3 : f.natDegree = 3) :
    ∃ u v w : E, (f.map (algebraMap F E)).roots = u ::ₘ v ::ₘ w ::ₘ 0 ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ ∀ x : E, x ∈ f.rootSet E ↔ (x = u ∨ x = v ∨ x = w) := by
  classical
  haveI : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  have hnd : (f.map (algebraMap F E)).roots.Nodup :=
    Polynomial.nodup_roots ((Polynomial.separable_map (algebraMap F E)).mpr hsep)
  have hcard : (f.map (algebraMap F E)).roots.card = 3 := by
    rw [(Polynomial.splits_iff_card_roots).mp hsplit,
      Polynomial.Monic.natDegree_map hf (algebraMap F E), h3]
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp (by rw [hcard]; norm_num))
  have hcard2 : (Multiset.erase (f.map (algebraMap F E)).roots u).card = 2 := by
    rw [Multiset.card_erase_of_mem hu, hcard]; norm_num
  obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp (by rw [hcard2]; norm_num))
  have hcard3 : (Multiset.erase (Multiset.erase (f.map (algebraMap F E)).roots u) v).card = 1 := by
    rw [Multiset.card_erase_of_mem hv, hcard2]; norm_num
  obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp (by rw [hcard3]; norm_num))
  have hw0 : (Multiset.erase (Multiset.erase (Multiset.erase (f.map (algebraMap F E)).roots u) v) w).card = 0 := by
    rw [Multiset.card_erase_of_mem hw, hcard3]; norm_num
  have hwz : Multiset.erase (Multiset.erase (Multiset.erase (f.map (algebraMap F E)).roots u) v) w = 0 :=
    Multiset.card_eq_zero.mp hw0
  have h1 : Multiset.erase (Multiset.erase (f.map (algebraMap F E)).roots u) v = w ::ₘ 0 := by
    rw [← Multiset.cons_erase hw, hwz]
  have h2 : Multiset.erase (f.map (algebraMap F E)).roots u = v ::ₘ (w ::ₘ 0) := by
    rw [← Multiset.cons_erase hv, h1]
  have hR : (f.map (algebraMap F E)).roots = u ::ₘ v ::ₘ w ::ₘ 0 := by
    rw [← Multiset.cons_erase hu, h2]
  rw [hR] at hnd
  rw [Multiset.nodup_cons] at hnd
  obtain ⟨hu', hnd2⟩ := hnd
  rw [Multiset.nodup_cons] at hnd2
  obtain ⟨hv', -⟩ := hnd2
  refine ⟨u, v, w, hR, ?_, ?_, ?_, ?_⟩
  · exact fun h => hu' (by rw [h]; simp)
  · exact fun h => hu' (by rw [h]; simp)
  · exact fun h => hv' (by rw [h]; simp)
  · intro x
    rw [Polynomial.rootSet_def f E, Polynomial.aroots_def f E, Finset.mem_coe,
      Multiset.mem_toFinset, hR]
    simp [Multiset.mem_cons]

-- FT cg6 (three points determine the root set)
/-- If `{u, v, w} ⊆ s` are pairwise distinct and `s` has three elements, then every element of
`s` is one of `u, v, w`. -/
theorem cg6_finset_char {E : Type*} [DecidableEq E] {s : Finset E} {u v w : E}
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hcard : s.card = 3) : ∀ x ∈ s, x = u ∨ x = v ∨ x = w := by
  have hcard3 : ({u, v, w} : Finset E).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, huw] : u ∉ {v, w}),
      Finset.card_insert_of_notMem (fun h => hvw (Finset.mem_singleton.mp h)),
      Finset.card_singleton]
  have hsub : ({u, v, w} : Finset E) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx1 | hx1
    · rw [hx1]; exact hu
    · rcases Finset.mem_insert.mp hx1 with hx2 | hx2
      · rw [hx2]; exact hv
      · rw [Finset.mem_singleton.mp hx2]; exact hw
  have hseq : ({u, v, w} : Finset E) = s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard3])
  intro x hx
  have hx' : x ∈ ({u, v, w} : Finset E) := hseq.ge hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  exact hx'

-- FT cg6 (the Galois group permutes the three roots)
/-- For three pairwise distinct roots `u, v, w` of `f`, any `F`-automorphism of `E` permutes
them in one of the six possible ways. -/
theorem cg6_perm_triple {F E : Type u} [Field F] [Field E] [Algebra F E] {f : F[X]}
    (hf : f ≠ 0) {u v w : E} (hmem : ∀ x ∈ f.rootSet E, x = u ∨ x = v ∨ x = w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u ∈ f.rootSet E) (hv : v ∈ f.rootSet E) (hw : w ∈ f.rootSet E) (σ : Gal(E/F)) :
    (σ u = u ∧ σ v = v ∧ σ w = w) ∨ (σ u = v ∧ σ v = u ∧ σ w = w) ∨
      (σ u = w ∧ σ v = v ∧ σ w = u) ∨ (σ u = u ∧ σ v = w ∧ σ w = v) ∨
      (σ u = v ∧ σ v = w ∧ σ w = u) ∨ (σ u = w ∧ σ v = u ∧ σ w = v) :=
  cg6_perm_cases (hmem (σ u) (cg6_gal_smul_root hf σ hu))
    (hmem (σ v) (cg6_gal_smul_root hf σ hv)) (hmem (σ w) (cg6_gal_smul_root hf σ hw))
    (fun h => huv (EquivLike.injective σ h)) (fun h => huw (EquivLike.injective σ h))
    (fun h => hvw (EquivLike.injective σ h))

-- FT cg6 (order-3 case: the Vandermonde product is G-fixed)
/-- If the Galois group has order 3, it fixes the Vandermonde product
`(u - v) * (u - w) * (v - w)` of three distinct roots. -/
theorem cg6_delta_fixed {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [FiniteDimensional F E] {f : F[X]} (hf0 : f ≠ 0)
    (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤)
    (hcard3 : Nat.card (Gal(E/F)) = 3) {u v w : E}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hmem : ∀ x ∈ f.rootSet E, x = u ∨ x = v ∨ x = w)
    (hu : u ∈ f.rootSet E) (hv : v ∈ f.rootSet E) (hw : w ∈ f.rootSet E) :
    ∀ σ : Gal(E/F), σ ((u - v) * (u - w) * (v - w)) = (u - v) * (u - w) * (v - w) := by
  intro σ
  have hdvd : orderOf σ ∣ Fintype.card (Gal(E/F)) := orderOf_dvd_card
  rw [Nat.card_eq_fintype_card] at hcard3
  rw [hcard3] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · rw [orderOf_eq_one_iff.mp h1]
    rfl
  · have hσ3 : σ ^ 3 = 1 := by rw [← h1, pow_orderOf_eq_one]
    rcases cg6_perm_triple hf0 hmem huv huw hvw hu hv hw σ with hc | hc | hc | hc | hc | hc
    · show σ.toAlgHom ((u - v) * (u - w) * (v - w)) = (u - v) * (u - w) * (v - w)
      have e1 : σ.toAlgHom u = u := hc.1
      have e2 : σ.toAlgHom v = v := hc.2.1
      have e3 : σ.toAlgHom w = w := hc.2.2
      rw [map_mul, map_mul, map_sub, map_sub, map_sub, e1, e2, e3]
    · have hsq : ∀ x ∈ f.rootSet E, (σ * σ) x = x := by
        intro x hx
        rcases hmem x hx with hx1 | hx1 | hx1
        · show σ (σ x) = x
          rw [hx1, hc.1, hc.2.1]
        · show σ (σ x) = x
          rw [hx1, hc.2.1, hc.1]
        · show σ (σ x) = x
          rw [hx1, hc.2.2, hc.2.2]
      have hs2 : σ * σ = 1 := gal_eq_one_of_fixes_rootSet hgen (σ * σ) hsq
      have hσ1 : σ = 1 := by rw [← hσ3, pow_succ, pow_two, hs2, one_mul]
      rw [hσ1]
      rfl
    · have hsq : ∀ x ∈ f.rootSet E, (σ * σ) x = x := by
        intro x hx
        rcases hmem x hx with hx1 | hx1 | hx1
        · show σ (σ x) = x
          rw [hx1, hc.1, hc.2.2]
        · show σ (σ x) = x
          rw [hx1, hc.2.1, hc.2.1]
        · show σ (σ x) = x
          rw [hx1, hc.2.2, hc.1]
      have hs2 : σ * σ = 1 := gal_eq_one_of_fixes_rootSet hgen (σ * σ) hsq
      have hσ1 : σ = 1 := by rw [← hσ3, pow_succ, pow_two, hs2, one_mul]
      rw [hσ1]
      rfl
    · have hsq : ∀ x ∈ f.rootSet E, (σ * σ) x = x := by
        intro x hx
        rcases hmem x hx with hx1 | hx1 | hx1
        · show σ (σ x) = x
          rw [hx1, hc.1, hc.1]
        · show σ (σ x) = x
          rw [hx1, hc.2.1, hc.2.2]
        · show σ (σ x) = x
          rw [hx1, hc.2.2, hc.2.1]
      have hs2 : σ * σ = 1 := gal_eq_one_of_fixes_rootSet hgen (σ * σ) hsq
      have hσ1 : σ = 1 := by rw [← hσ3, pow_succ, pow_two, hs2, one_mul]
      rw [hσ1]
      rfl
    · show σ.toAlgHom ((u - v) * (u - w) * (v - w)) = (u - v) * (u - w) * (v - w)
      have e1 : σ.toAlgHom u = v := hc.1
      have e2 : σ.toAlgHom v = w := hc.2.1
      have e3 : σ.toAlgHom w = u := hc.2.2
      rw [map_mul, map_mul, map_sub, map_sub, map_sub, e1, e2, e3]
      ring
    · show σ.toAlgHom ((u - v) * (u - w) * (v - w)) = (u - v) * (u - w) * (v - w)
      have e1 : σ.toAlgHom u = w := hc.1
      have e2 : σ.toAlgHom v = u := hc.2.1
      have e3 : σ.toAlgHom w = v := hc.2.2
      rw [map_mul, map_mul, map_sub, map_sub, map_sub, e1, e2, e3]
      ring

-- FT cg6 (order-3 case, converse: a fixed Vandermonde product forces order 3)
/-- If the Vandermonde product `(u' - v') * (u' - w') * (v' - w')` of the three distinct roots is
fixed by the Galois group (and `2 ≠ 0` in `F`), then the Galois group has order 3. -/
theorem cg6_card3_of_fixed {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [FiniteDimensional F E] {f : F[X]} (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f)
    (h3 : f.natDegree = 3) (hsplit : (f.map (algebraMap F E)).Splits)
    (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤) (h2 : (2 : F) ≠ 0)
    {u' v' w' : E} (hu'v' : u' ≠ v') (hu'w' : u' ≠ w') (hv'w' : v' ≠ w')
    (hmem' : ∀ x ∈ f.rootSet E, x = u' ∨ x = v' ∨ x = w')
    (hu'mem : u' ∈ f.rootSet E) (hv'mem : v' ∈ f.rootSet E) (hw'mem : w' ∈ f.rootSet E)
    (hfix : ∀ σ : Gal(E/F),
      σ ((u' - v') * (u' - w') * (v' - w')) = (u' - v') * (u' - w') * (v' - w')) :
    Nat.card (Gal(E/F)) = 3 := by
  classical
  set δ' : E := (u' - v') * (u' - w') * (v' - w') with hδ'def
  have hδ0 : δ' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hu'v') (sub_ne_zero.mpr hu'w'))
      (sub_ne_zero.mpr hv'w')
  rcases (cg6_count hf hsep hirr h3 hsplit hgen).2.2 with h3c | h6c
  · exact h3c
  · obtain ⟨σ, hσo⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [h6c]; norm_num)
    have hσ2 : σ ^ 2 = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
    have hσne : σ ≠ 1 := by
      intro h
      rw [h] at hσo
      exact absurd (((orderOf_eq_one_iff).mpr rfl).symm.trans hσo) (by norm_num)
    have hσsq : ∀ x : E, σ (σ x) = x := by
      intro x
      show (σ ^ 2) x = x
      rw [hσ2]
      rfl
    rcases cg6_perm_triple hf.ne_zero hmem' hu'v' hu'w' hv'w' hu'mem hv'mem hw'mem σ
      with hc | hc | hc | hc | hc | hc
    · refine absurd (gal_eq_one_of_fixes_rootSet hgen σ ?_) hσne
      intro x hx
      rcases hmem' x hx with hx1 | hx1 | hx1
      · show σ x = x
        rw [hx1, hc.1]
      · show σ x = x
        rw [hx1, hc.2.1]
      · show σ x = x
        rw [hx1, hc.2.2]
    · have e1 : σ.toAlgHom u' = v' := hc.1
      have e2 : σ.toAlgHom v' = u' := hc.2.1
      have e3 : σ.toAlgHom w' = w' := hc.2.2
      have hsd' : σ.toAlgHom δ' = δ' := hfix σ
      rw [map_mul, map_mul, map_sub, map_sub, map_sub, e1, e2, e3] at hsd'
      have hzero : δ' + (v' - u') * (v' - w') * (u' - w') = 0 := by ring
      rw [hsd'] at hzero
      have h2d : (2 : E) * δ' = 0 := by rw [two_mul]; exact hzero
      rcases mul_eq_zero.mp h2d with hzz | hzz
      · exact absurd hzz (two_ne_zero_algebraMap h2)
      · exact absurd hzz hδ0
    · have e1 : σ.toAlgHom u' = w' := hc.1
      have e2 : σ.toAlgHom v' = v' := hc.2.1
      have e3 : σ.toAlgHom w' = u' := hc.2.2
      have hsd' : σ.toAlgHom δ' = δ' := hfix σ
      rw [map_mul, map_mul, map_sub, map_sub, map_sub, e1, e2, e3] at hsd'
      have hzero : δ' + (w' - v') * (w' - u') * (v' - u') = 0 := by ring
      rw [hsd'] at hzero
      have h2d : (2 : E) * δ' = 0 := by rw [two_mul]; exact hzero
      rcases mul_eq_zero.mp h2d with hzz | hzz
      · exact absurd hzz (two_ne_zero_algebraMap h2)
      · exact absurd hzz hδ0
    · have e1 : σ.toAlgHom u' = u' := hc.1
      have e2 : σ.toAlgHom v' = w' := hc.2.1
      have e3 : σ.toAlgHom w' = v' := hc.2.2
      have hsd' : σ.toAlgHom δ' = δ' := hfix σ
      rw [map_mul, map_mul, map_sub, map_sub, map_sub, e1, e2, e3] at hsd'
      have hzero : δ' + (u' - w') * (u' - v') * (w' - v') = 0 := by ring
      rw [hsd'] at hzero
      have h2d : (2 : E) * δ' = 0 := by rw [two_mul]; exact hzero
      rcases mul_eq_zero.mp h2d with hzz | hzz
      · exact absurd hzz (two_ne_zero_algebraMap h2)
      · exact absurd hzz hδ0
    · have h1 : σ (σ u') = u' := hσsq u'
      rw [hc.1, hc.2.1] at h1
      exact absurd h1.symm hu'w'
    · have h1 : σ (σ u') = u' := hσsq u'
      rw [hc.1, hc.2.2] at h1
      exact absurd h1.symm hu'v'

-- FT cg6 (dichotomy: δ² is a square over F ⟺ Gal(E/F) has order 3)
/-- **FT cg6 (dichotomy).** For an irreducible separable cubic over `F` (char `F ≠ 2`) with
splitting field `E`, a square root of the Vandermonde product
`(u - v) * (u - w) * (v - w)` of the three distinct roots lies in `F` if and only if the Galois
group `Gal(E/F)` has order 3 (i.e. the discriminant is a square exactly when the Galois group is
cyclic of order 3). -/
theorem cg6_dichotomy {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [FiniteDimensional F E] {f : F[X]} (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f)
    (h3 : f.natDegree = 3) (hsplit : (f.map (algebraMap F E)).Splits)
    (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤) (h2 : (2 : F) ≠ 0) :
    (∃ u v w : E, aeval u f = 0 ∧ aeval v f = 0 ∧ aeval w f = 0 ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        ∃ t : F, algebraMap F E t * algebraMap F E t = ((u - v) * (u - w) * (v - w)) ^ 2) ↔
      Nat.card (Gal(E/F)) = 3 := by
  classical
  haveI : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  have hf0 : f ≠ 0 := hf.ne_zero
  obtain ⟨u, v, w, hR, huv, huw, hvw, hchar⟩ := cg6_roots_extract hf hsep hsplit h3
  have hu : u ∈ f.rootSet E := (hchar u).mpr (Or.inl rfl)
  have hv : v ∈ f.rootSet E := (hchar v).mpr (Or.inr (Or.inl rfl))
  have hw : w ∈ f.rootSet E := (hchar w).mpr (Or.inr (Or.inr rfl))
  set s : Finset E := ((f.map (algebraMap F E)).roots).toFinset with hsdef
  have hnd : (f.map (algebraMap F E)).roots.Nodup :=
    Polynomial.nodup_roots ((Polynomial.separable_map (algebraMap F E)).mpr hsep)
  have hscard : s.card = 3 := by
    rw [hsdef, Multiset.toFinset_card_of_nodup hnd, (Polynomial.splits_iff_card_roots).mp hsplit,
      Polynomial.Monic.natDegree_map hf (algebraMap F E), h3]
  have hrootroot : ∀ x : E, x ∈ f.rootSet E ↔ x ∈ s := by
    intro x
    rw [hsdef, Multiset.mem_toFinset]
    exact (hchar x).trans (by rw [hR]; simp [Multiset.mem_cons])
  have hu's : u ∈ s := (hrootroot u).mp hu
  have hv's : v ∈ s := (hrootroot v).mp hv
  have hw's : w ∈ s := (hrootroot w).mp hw
  have hmem' : ∀ x ∈ s, x = u ∨ x = v ∨ x = w :=
    cg6_finset_char hu's hv's hw's huv huw hvw hscard
  constructor
  · rintro ⟨u', v', w', hu'', hv'', hw'', hu'v', hu'w', hv'w', t, ht⟩
    have hu'mem : u' ∈ f.rootSet E := Polynomial.mem_rootSet.mpr ⟨hf0, hu''⟩
    have hv'mem : v' ∈ f.rootSet E := Polynomial.mem_rootSet.mpr ⟨hf0, hv''⟩
    have hw'mem : w' ∈ f.rootSet E := Polynomial.mem_rootSet.mpr ⟨hf0, hw''⟩
    have hmem'' : ∀ x ∈ f.rootSet E, x = u' ∨ x = v' ∨ x = w' :=
      fun x hx =>
        cg6_finset_char ((hrootroot u').mp hu'mem) ((hrootroot v').mp hv'mem)
          ((hrootroot w').mp hw'mem) hu'v' hu'w' hv'w' hscard x ((hrootroot x).mp hx)
    set δ' : E := (u' - v') * (u' - w') * (v' - w') with hδ'def
    have hz : (algebraMap F E t - δ') * (algebraMap F E t + δ') = 0 := by
      rw [pow_two] at ht
      linear_combination ht
    rcases mul_eq_zero.mp hz with hz' | hz'
    · have heq : δ' = algebraMap F E t := (sub_eq_zero.mp hz').symm
      refine cg6_card3_of_fixed hf hsep hirr h3 hsplit hgen h2 hu'v' hu'w' hv'w' hmem''
        hu'mem hv'mem hw'mem ?_
      intro σ
      show σ.toAlgHom δ' = δ'
      rw [heq]
      exact σ.toAlgHom.commutes t
    · have heq : δ' = -algebraMap F E t :=
        eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hz')
      refine cg6_card3_of_fixed hf hsep hirr h3 hsplit hgen h2 hu'v' hu'w' hv'w' hmem''
        hu'mem hv'mem hw'mem ?_
      intro σ
      show σ.toAlgHom δ' = δ'
      rw [heq, map_neg, σ.toAlgHom.commutes t]
  · rintro hcard3
    have hfixδ := cg6_delta_fixed hf0 hgen hcard3 huv huw hvw
      (fun x hx => (hchar x).mp hx) hu hv hw
    have hfixmem : (u - v) * (u - w) * (v - w) ∈
        IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ _
      exact hfixδ σ
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hfixmem
    obtain ⟨t, ht⟩ := hfixmem
    exact ⟨u, v, w, (Polynomial.mem_rootSet.mp hu).2, (Polynomial.mem_rootSet.mp hv).2,
      (Polynomial.mem_rootSet.mp hw).2, huv, huw, hvw, t, by rw [pow_two, ht]⟩

-- FT cg6 (corollary: A₃ is the cyclic subgroup generated by the 3-cycle (0 1 2))
/-- **FT cg6 (corollary).** The alternating group `A₃ = ker(sign) ` of `S₃` on `Fin 3` is the
cyclic subgroup generated by the 3-cycle `Equiv.swap 0 1 * Equiv.swap 1 2` (which maps
`0 ↦ 1 ↦ 2 ↦ 0`).

Proof idea: the closure `{c}` contains `1`, `c`, `c²`; conversely an element of the kernel has
sign `+1`, and among the six permutations of `S₃` exactly `1`, `c`, `c²` have sign `+1` while
the three transpositions have sign `-1`; injectivity of permutations plus the possible images of
`0, 1, 2` finish the case analysis. -/
theorem cg6_a3_cycle :
    Subgroup.closure {Equiv.swap 0 1 * Equiv.swap 1 2}
      = (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).ker := by
  classical
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have hcM : c ∈ Subgroup.closure {c} := Subgroup.subset_closure (Set.mem_singleton c)
  have hcM2 : c * c ∈ Subgroup.closure {c} :=
    Subgroup.mul_mem (Subgroup.closure {c}) hcM hcM
  have hone : 1 ∈ Subgroup.closure {c} := Subgroup.one_mem _
  have hsw0 : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 from by decide) (show (0 : Fin 3) ≠ 2 from by decide)
  have hsw1 : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 1 = 2 := Equiv.swap_apply_left _ _
  have hsw2 : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 2 = 1 := Equiv.swap_apply_right _ _
  have hsw0' : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 0 = 1 := Equiv.swap_apply_left _ _
  have hsw1' : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 1 = 0 := Equiv.swap_apply_right _ _
  have hsw2' : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 3) ≠ 0 from by decide) (show (2 : Fin 3) ≠ 1 from by decide)
  have hsw0'' : (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 0 = 2 := Equiv.swap_apply_left _ _
  have hsw1'' : (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 from by decide) (show (1 : Fin 3) ≠ 2 from by decide)
  have hsw2'' : (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 2 = 0 := Equiv.swap_apply_right _ _
  have hc0 : c 0 = 1 := by rw [hc, Equiv.Perm.mul_apply, hsw0, hsw0']
  have hc1 : c 1 = 2 := by rw [hc, Equiv.Perm.mul_apply, hsw1, hsw2']
  have hc2 : c 2 = 0 := by rw [hc, Equiv.Perm.mul_apply, hsw2, hsw1']
  have hcc0 : (c * c) 0 = 2 := by rw [Equiv.Perm.mul_apply, hc0, hc1]
  have hcc1 : (c * c) 1 = 0 := by rw [Equiv.Perm.mul_apply, hc1, hc2]
  have hcc2 : (c * c) 2 = 1 := by rw [Equiv.Perm.mul_apply, hc2, hc0]
  have honeval : ∀ i : Fin 3, (1 : Equiv.Perm (Fin 3)) i = i := fun i => rfl
  have hfin3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact MonoidHom.mem_ker.mpr (by
      rw [hc, map_mul, Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 from by decide),
        Equiv.Perm.sign_swap (show (1 : Fin 3) ≠ 2 from by decide)]
      norm_num)
  · intro σ hσ
    have hs : Equiv.Perm.sign σ = 1 := MonoidHom.mem_ker.mp hσ
    have hinj : Function.Injective ⇑σ := Equiv.injective σ
    rcases hfin3 (σ 0) with e0 | e0 | e0
    · rcases hfin3 (σ 1) with e1 | e1 | e1
      · exact absurd (hinj (e1.trans e0.symm)) (by decide)
      · rcases hfin3 (σ 2) with e2 | e2 | e2
        · exact absurd (hinj (e2.trans e0.symm)) (by decide)
        · exact absurd (hinj (e2.trans e1.symm)) (by decide)
        · rw [show σ = 1 from Equiv.ext (fun i => by
            rcases hfin3 i with h | h | h
            · rw [h, e0]; exact (honeval _).symm
            · rw [h, e1]; exact (honeval _).symm
            · rw [h, e2]; exact (honeval _).symm)]
          exact hone
      · rcases hfin3 (σ 2) with e2 | e2 | e2
        · exact absurd (hinj (e2.trans e0.symm)) (by decide)
        · rw [show σ = Equiv.swap 1 2 from Equiv.ext (fun i => by
            rcases hfin3 i with h | h | h
            · rw [h, e0, hsw0]
            · rw [h, e1, hsw1]
            · rw [h, e2, hsw2])] at hs ⊢
          rw [Equiv.Perm.sign_swap (show (1 : Fin 3) ≠ 2 from by decide)] at hs
          exact absurd (congrArg Units.val hs) (by
            rw [Units.val_neg, Units.val_one]; norm_num)
        · exact absurd (hinj (e1.trans e2.symm)) (by decide)
    · rcases hfin3 (σ 1) with e1 | e1 | e1
      · rcases hfin3 (σ 2) with e2 | e2 | e2
        · exact absurd (hinj (e2.trans e1.symm)) (by decide)
        · exact absurd (hinj (e2.trans e0.symm)) (by decide)
        · rw [show σ = Equiv.swap 0 1 from Equiv.ext (fun i => by
            rcases hfin3 i with h | h | h
            · rw [h, e0, hsw0']
            · rw [h, e1, hsw1']
            · rw [h, e2, hsw2'])] at hs ⊢
          rw [Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 from by decide)] at hs
          exact absurd (congrArg Units.val hs) (by
            rw [Units.val_neg, Units.val_one]; norm_num)
      · exact absurd (hinj (e1.trans e0.symm)) (by decide)
      · rcases hfin3 (σ 2) with e2 | e2 | e2
        · rw [show σ = c from Equiv.ext (fun i => by
            rcases hfin3 i with h | h | h
            · rw [h, e0, hc0]
            · rw [h, e1, hc1]
            · rw [h, e2, hc2])]
          exact hcM
        · exact absurd (hinj (e2.trans e0.symm)) (by decide)
        · exact absurd (hinj (e2.trans e1.symm)) (by decide)
    · rcases hfin3 (σ 1) with e1 | e1 | e1
      · rcases hfin3 (σ 2) with e2 | e2 | e2
        · exact absurd (hinj (e2.trans e1.symm)) (by decide)
        · rw [show σ = c * c from Equiv.ext (fun i => by
            rcases hfin3 i with h | h | h
            · rw [h, e0, hcc0]
            · rw [h, e1, hcc1]
            · rw [h, e2, hcc2])]
          exact hcM2
        · exact absurd (hinj (e2.trans e0.symm)) (by decide)
      · rcases hfin3 (σ 2) with e2 | e2 | e2
        · rw [show σ = Equiv.swap 0 2 from Equiv.ext (fun i => by
            rcases hfin3 i with h | h | h
            · rw [h, e0, hsw0'']
            · rw [h, e1, hsw1'']
            · rw [h, e2, hsw2''])] at hs ⊢
          rw [Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 2 from by decide)] at hs
          exact absurd (congrArg Units.val hs) (by
            rw [Units.val_neg, Units.val_one]; norm_num)
        · exact absurd (hinj (e2.trans e1.symm)) (by decide)
        · exact absurd (hinj (e2.trans e0.symm)) (by decide)
      · exact absurd (hinj (e1.trans e0.symm)) (by decide)
