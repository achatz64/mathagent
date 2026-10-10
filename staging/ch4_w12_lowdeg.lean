-- STAGING: FT ch. IV §2–3 (cg4, cg5, cg6 core), re-derivation worker w12 deliverable,
-- received verbatim. All declarations verified in shared REPL; [V*] temp-name mapping:
--   disc_cubic_vieta_tmp2 → disc_cubic_vieta, gal_trans_tmp4 → gal_transitive_iff_irreducible,
--   cg5_tmp10 → cg5, gal_fix_tmp2 → gal_eq_one_of_fixes_rootSet, gal_inj_v2 → gal_inj_on_rootSet,
--   cg6_root_card_tmp2 → cg6_root_card, cg6_count_v3 → cg6_count, cg6_trans_v2 → cg6_transitive.
-- NOT delivered (recorded): cg5/cg6 inseparable clauses; cg6 dichotomy (A_3 vs S_3) —
--   [P] with full fix plan (see worker report; needs multiset surgery + orderOf bookkeeping).
-- Paste inside namespace FT.

open Polynomial

-- FT cg5/cg6 (discriminant formulas, degree 2)
/-- **FT cg5/cg6 auxiliary (Vieta, quadratic).** If `X^2 + b·X + c = (X - u)(X - v)` over a
commutative ring, then the discriminant (squared difference of the roots) is
`(u - v)^2 = b^2 - 4c` (Vieta's formula: `u + v = -b`, `u·v = c`, and
`(u-v)^2 = (u+v)^2 - 4uv`).

Proof idea: expand the product into the normalized form `X^2 - (u+v)·X + u·v` (`ring` after
pushing `C` through `+`/`*`), compare the coefficients of `X` and `1` on both sides via
`Polynomial.coeff`, then compute `(u-v)^2 = (u+v)^2 - 4uv` by `ring`. -/
theorem disc_quad_vieta {K : Type*} [CommRing K] {b c u v : K}
    (h : X ^ 2 + C b * X + C c = (X - C u) * (X - C v)) :
    (u - v) ^ 2 = b ^ 2 - 4 * c := by
  have key : (X - C u) * (X - C v) = X ^ 2 - C (u + v) * X + C (u * v) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]; ring
  rw [key] at h
  have h1 := congrArg (fun P => P.coeff 1) h
  have h0 := congrArg (fun P => P.coeff 0) h
  simp at h1 h0
  rw [h1, h0]; ring

-- FT cg5 (Vieta data, degree 2)
/-- **FT cg5 auxiliary (Vieta, quadratic): the full Vieta data.** If `X^2 + b·X + c =
(X - u)(X - v)` over a commutative ring, then `u + v = -b` (sum of the roots) and
`u * v = c` (product of the roots). Used for the degree-two Galois dichotomy, where
`u + v ∈ F` is needed to symmetrize expressions in the two roots.

Proof idea: expand the product into the normalized form `X^2 - (u+v)·X + u·v` (`ring` after
pushing `C` through `+`/`*`), then compare the coefficients of `X` and `1` on both sides. -/
theorem quad_vieta {K : Type*} [CommRing K] {b c u v : K}
    (h : X ^ 2 + C b * X + C c = (X - C u) * (X - C v)) :
    u + v = -b ∧ u * v = c := by
  have key : (X - C u) * (X - C v) = X ^ 2 - C (u + v) * X + C (u * v) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]; ring
  rw [key] at h
  have h1 := congrArg (fun P => P.coeff 1) h
  have h0 := congrArg (fun P => P.coeff 0) h
  simp at h1 h0
  exact ⟨by rw [h1]; ring, h0.symm⟩

-- FT cg6 (Vieta data, degree 3)
/-- **FT cg6 auxiliary (Vieta, depressed cubic).** If `X^3 + p·X + q = (X - u)(X - v)(X - w)`
over a commutative ring, then `u + v + w = 0` (the cubic is depressed: no `X^2` term),
`u * v + u * w + v * w = p` and `u * v * w = -q` (comparison of the coefficients of `X^2`,
`X` and `1`).

Proof idea: expand the product into the normalized form `X^3 - (u+v+w)·X^2 + (uv+uw+vw)·X -
uvw` (`ring` after pushing `C` through `+`/`*`), then compare coefficients; the symmetric
functions are named `s1, s2, s3` so that the coefficient of `C s1 · X^2` is read off directly. -/
theorem cubic_vieta {K : Type*} [CommRing K] {p q u v w : K}
    (h : X ^ 3 + C p * X + C q = (X - C u) * (X - C v) * (X - C w)) :
    u + v + w = 0 ∧ u * v + u * w + v * w = p ∧ u * v * w = -q := by
  have key : (X - C u) * (X - C v) * (X - C w)
      = X ^ 3 - C (u + v + w) * X ^ 2 + C (u * v + u * w + v * w) * X - C (u * v * w) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]; ring
  rw [key] at h
  have h2 := congrArg (fun P => P.coeff 2) h
  have h1 := congrArg (fun P => P.coeff 1) h
  have h0 := congrArg (fun P => P.coeff 0) h
  set s1 : K := u + v + w with hs1
  set s2 : K := u * v + u * w + v * w with hs2
  set s3 : K := u * v * w with hs3
  simp [Polynomial.coeff_C_mul] at h2 h1 h0
  exact ⟨h2, h1.symm, by rw [h0]; ring⟩

-- FT cg6 (discriminant formula, degree 3)
/-- **FT cg6 auxiliary (discriminant of a depressed cubic).** If `X^3 + p·X + q =
(X - u)(X - v)(X - w)` over a commutative ring, then the discriminant (squared Vandermonde
product) of the roots is `(u-v)^2 (u-w)^2 (v-w)^2 = -4·p^3 - 27·q^2` (the discriminant
formula for a depressed cubic).

Proof idea: by `FT.cubic_vieta` the symmetric functions of the roots are `u+v+w = 0`,
`uv+uw+vw = p`, `uvw = -q`; substituting `w = -(u+v)` from the first relation reduces the
claim to a polynomial identity in `u` and `v`, closed by `ring`. -/
theorem disc_cubic_vieta {K : Type*} [CommRing K] {p q u v w : K}
    (h : X ^ 3 + C p * X + C q = (X - C u) * (X - C v) * (X - C w)) :
    (u - v) ^ 2 * (u - w) ^ 2 * (v - w) ^ 2 = -4 * p ^ 3 - 27 * q ^ 2 := by
  obtain ⟨hs1, hs2, hs3⟩ := cubic_vieta h
  have hw : w = -(u + v) := by linear_combination hs1
  subst hw
  have hs3' : q = -(u * v * -(u + v)) := by rw [hs3]; ring
  rw [← hs2, hs3']; ring

-- FT cg4
/-- **FT cg4** (transitivity of the Galois group on the roots). Let `E/F` be a Galois
extension and `f ∈ F[X]` monic, separable, of positive degree, splitting over `E`. Then `f`
is irreducible if and only if `Gal(E/F)` permutes the root set `f.rootSet E` transitively,
i.e. for any two roots `α, β ∈ E` of `f` there is `σ ∈ Gal(E/F)` with `σ α = β`.

Proof idea. Fix a root `α` of `f` in `E` and put `m = minpoly F α` (which divides `f`, since
`f` is monic). By FT ch3 (`FT.orbit_eq_rootSet_minpoly`) the orbit of `α` under `Gal(E/F)`
is exactly `m.rootSet E`.
(⇐) If the action is transitive then `f.rootSet E ⊆ m.rootSet E`, while `m ∣ f` gives the
reverse inclusion, so the root sets agree. Comparing coefficients: `f` and `m` are both monic
and separable and split over `E`, so their (nodup) root multisets coincide; their
cardinalities equal their degrees (`Polynomial.splits_iff_card_roots`), hence `f` and `m` are
monic of equal degree with `m ∣ f`, so `f = m` is irreducible.
(⇒) If `f` is irreducible then `f = minpoly F α`, so the root set of `f` is the orbit of `α`,
and every root is of the form `σ α`. -/
theorem gal_transitive_iff_irreducible {F E : Type u} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] {f : F[X]} (hf : f.Monic) (hsep : f.Separable)
    (hsplit : (f.map (algebraMap F E)).Splits) (hdeg : 0 < f.natDegree) :
    Irreducible f ↔ ∀ α ∈ f.rootSet E, ∀ β ∈ f.rootSet E, ∃ σ : Gal(E/F), σ α = β := by
  classical
  have hmap0 : (f.map (algebraMap F E)) ≠ 0 := (hf.map (algebraMap F E)).ne_zero
  obtain ⟨α, hα⟩ : ∃ α : E, (Polynomial.aeval α) f = 0 := by
    have hcard : ((f.map (algebraMap F E)).roots).card = f.natDegree := by
      rw [(Polynomial.splits_iff_card_roots).mp hsplit, hf.natDegree_map (algebraMap F E)]
    obtain ⟨β, hβ⟩ := Multiset.exists_mem_of_ne_zero
      (Multiset.card_pos.mp (by rw [hcard]; exact hdeg))
    refine ⟨β, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact (Polynomial.mem_roots hmap0).mp hβ
  constructor
  · intro hirr α' hα' β hβ
    have horb : (fun σ : Gal(E/F) => σ α') '' Set.univ = (minpoly F α').rootSet E :=
      orbit_eq_rootSet_minpoly α' (IsGalois.integral F α')
    have key : f = minpoly F α' := minpoly.eq_of_irreducible_of_monic hirr
      (Polynomial.mem_rootSet_of_ne hf.ne_zero |>.mp hα') hf
    rw [key] at hβ
    rw [← horb, Set.image_univ] at hβ
    obtain ⟨σ, hσ⟩ := Set.mem_range.mp hβ
    exact ⟨σ, hσ⟩
  · intro hRhs
    set m := minpoly F α with hm
    have hαi : IsIntegral F α := IsGalois.integral F α
    have hdv : m ∣ f := minpoly.dvd F α hα
    have hαmem : α ∈ f.rootSet E := Polynomial.mem_rootSet_of_ne hf.ne_zero |>.mpr hα
    have horb : (fun σ : Gal(E/F) => σ α) '' Set.univ = m.rootSet E :=
      orbit_eq_rootSet_minpoly α hαi
    have h1 : f.rootSet E ⊆ m.rootSet E := by
      intro β hβ
      obtain ⟨σ, hσ⟩ := hRhs α hαmem β hβ
      rw [← horb, Set.image_univ]
      exact ⟨σ, hσ⟩
    have h2 : m.rootSet E ⊆ f.rootSet E := by
      intro β hβ
      simp only [Polynomial.mem_rootSet'] at hβ ⊢
      refine ⟨hmap0, ?_⟩
      obtain ⟨g, rfl⟩ := hdv
      rw [Polynomial.aeval_mul, hβ.2, zero_mul]
    have hsepm : m.Separable := hsep.of_dvd hdv
    have hsplm : ((m.map (algebraMap F E)).Splits) :=
      Polynomial.Splits.of_dvd hsplit hmap0 (Polynomial.map_dvd _ hdv)
    have hset : f.rootSet E = m.rootSet E := le_antisymm h1 h2
    simp only [Polynomial.rootSet_def] at hset
    have hfin : (f.map (algebraMap F E)).roots.toFinset
        = (m.map (algebraMap F E)).roots.toFinset := Finset.coe_inj.mp hset
    have hnd1 : ((f.map (algebraMap F E)).roots).Nodup :=
      Polynomial.nodup_roots ((Polynomial.separable_map _).mpr hsep)
    have hnd2 : ((m.map (algebraMap F E)).roots).Nodup :=
      Polynomial.nodup_roots ((Polynomial.separable_map _).mpr hsepm)
    have hcardf : ((f.map (algebraMap F E)).roots).card
        = ((m.map (algebraMap F E)).roots).card := by
      rw [← Multiset.toFinset_card_of_nodup hnd1, ← Multiset.toFinset_card_of_nodup hnd2, hfin]
    have hnd : f.natDegree = m.natDegree := by
      rw [← hf.natDegree_map (algebraMap F E),
        ← (minpoly.monic hαi).natDegree_map (algebraMap F E),
        ← (Polynomial.splits_iff_card_roots).mp hsplit,
        ← (Polynomial.splits_iff_card_roots).mp hsplm, hcardf]
    have hfm : f = m :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hαi) hf hdv hnd.le
    rw [hfm]
    exact minpoly.irreducible hαi

-- FT cg5
/-- **FT cg5** (degree-2 dichotomy, separable case). Let `E/F` be a finite Galois extension
of characteristic `≠ 2` generated by the root set of the monic quadratic
`f = X^2 + b·X + c`, factored over `E` as `f = (X - u)(X - v)`. Then:
* `Nat.card Gal(E/F) = 1` iff the discriminant `D = (u - v)^2` is a square in `F`
  (i.e. `G_f = 1 = A_2` iff `D ∈ F^2`), and
* `Nat.card Gal(E/F) = 2` iff `D` is not a square (i.e. `G_f = S_2` otherwise).

Caveat: the hypothesis `(2 : F) ≠ 0` is necessary — in characteristic 2 the discriminant
`(u - v)^2 = (u + v)^2` is always a square, while `G_f` need not be trivial (e.g.
`X^2 + X + 1` over `F_2`).

Proof idea. Comparing coefficients (`FT.quad_vieta`) gives `u + v = -algebraMap b ∈ F`, so
one root is in `F` iff both are. If `D = t^2` with `t ∈ F` then `t = ±(u - v)` in `E`, and
`u = ((u + v) + (u - v))·(2^{-1}) ∈ F` since `2` is invertible; conversely `u, v ∈ F` gives
`t = u - v`. Moreover `E = F⟨u⟩` (the root set is `{u, v}` and `v = -b - u`), so
`Nat.card Gal(E/F) = [E : F] = deg minpoly F u` (`IsGalois.card_aut_eq_finrank`,
`IntermediateField.adjoin.finrank`), which is `1` iff `u ∈ F` and `2` otherwise
(`deg minpoly F u ∣ deg f = 2`). -/
theorem cg5 {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [FiniteDimensional F E] (hchar : (2 : F) ≠ 0) {f : F[X]} {b c : F} {u v : E}
    (hb : f = X ^ 2 + C b * X + C c)
    (hfac : (f.map (algebraMap F E)) = (X - C u) * (X - C v))
    (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤) :
    (Nat.card Gal(E/F) = 1 ↔ ∃ t : F, algebraMap F E t * algebraMap F E t = (u - v) ^ 2) ∧
    (Nat.card Gal(E/F) = 2 ↔ ¬ ∃ t : F, algebraMap F E t * algebraMap F E t = (u - v) ^ 2) := by
  classical
  have hainj : Function.Injective (algebraMap F E) := by
    intro a₀ a₁ h
    by_contra hc
    have hu : IsUnit (a₀ - a₁) := isUnit_iff_ne_zero.mpr (sub_ne_zero_of_ne hc)
    have hunit : IsUnit (algebraMap F E (a₀ - a₁)) := hu.map (algebraMap F E)
    exact hunit.ne_zero (by rw [map_sub, h, sub_self])
  have htwo' : algebraMap F E (2 : F) ≠ 0 := by
    intro h
    exact hchar (hainj (by rw [h]; simp))
  have hv1 : u + v = -(algebraMap F E b) := by
    have hfac' : X ^ 2 + C (algebraMap F E b) * X + C (algebraMap F E c)
        = (X - C u) * (X - C v) := by
      rw [hb] at hfac
      simpa using hfac
    exact (quad_vieta hfac').1
  have hintu : IsIntegral F u := IsGalois.integral F u
  have hmu0 : minpoly F u ≠ 0 := minpoly.ne_zero hintu
  have hU : (Polynomial.aeval u) f = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hfac]
    try simp
  have hdvu : minpoly F u ∣ f := minpoly.dvd F u hU
  have hnd2 : f.natDegree = 2 := by
    rw [← Polynomial.natDegree_map_eq_of_injective hainj f, hfac,
      Polynomial.natDegree_mul
        (by exact fun hc => absurd (sub_eq_zero.mp hc) (Polynomial.X_ne_C u))
        (by exact fun hc => absurd (sub_eq_zero.mp hc) (Polynomial.X_ne_C v))]
    rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
  have hf0 : f ≠ 0 := by
    intro h
    rw [h] at hnd2
    simp at hnd2
  have hdvu2 : (minpoly F u).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_of_dvd hdvu hf0).trans hnd2.le
  have hdeg1 : (minpoly F u).natDegree ≠ 0 := by
    intro h0
    have hmae := minpoly.aeval F u
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.aeval_C] at hmae
    have hcoe : (minpoly F u).coeff 0 = 0 := hainj (by rw [hmae]; simp)
    have hmz : minpoly F u = C ((minpoly F u).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero h0
    exact hmu0 (by rw [hmz, hcoe]; simp)
  have hdegcase : (minpoly F u).natDegree = 1 ∨ (minpoly F u).natDegree = 2 := by omega
  have hEq : IntermediateField.adjoin F {u} = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgen, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Polynomial.mem_rootSet', Polynomial.aeval_def, ← Polynomial.eval_map, hfac,
      Polynomial.eval_mul] at hx
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hx
    rcases mul_eq_zero.mp hx.2 with hx | hx
    · exact sub_eq_zero.mp hx ▸ IntermediateField.mem_adjoin_simple_self F u
    · rw [sub_eq_zero.mp hx]
      have hvx : v = -(algebraMap F E b) - u := by
        rw [← hv1]
        ring
      rw [hvx]
      have hbb : (algebraMap F E b : E) ∈
          (IntermediateField.adjoin F {u} : IntermediateField F E) :=
        SetLike.le_def.mp (bot_le (α := IntermediateField F E))
          (IntermediateField.mem_bot.mpr ⟨b, rfl⟩)
      exact IntermediateField.sub_mem (IntermediateField.adjoin F {u})
        (IntermediateField.neg_mem (IntermediateField.adjoin F {u}) hbb)
        (IntermediateField.mem_adjoin_simple_self F u)
  have hfr : Module.finrank F E = (minpoly F u).natDegree := by
    rw [← IntermediateField.adjoin.finrank hintu, hEq,
      IntermediateField.topEquiv.toLinearEquiv.finrank_eq]
  have hcardG : Nat.card Gal(E/F) = (minpoly F u).natDegree := by
    rw [IsGalois.card_aut_eq_finrank F E, hfr]
  have hnd1iff : (minpoly F u).natDegree = 1 ↔ ∃ u₀ : F, algebraMap F E u₀ = u := by
    constructor
    · intro h1
      have hme : (Polynomial.aeval u) (minpoly F u) = 0 := minpoly.aeval F u
      have hdg : (minpoly F u).degree = 1 := by
        rw [Polynomial.degree_eq_natDegree hmu0]; exact_mod_cast h1
      have hform : minpoly F u = C (minpoly F u).leadingCoeff * X
          + C ((minpoly F u).coeff 0) :=
        Polynomial.eq_X_add_C_of_degree_eq_one hdg
      have hlc : (minpoly F u).leadingCoeff = 1 := (minpoly.monic hintu).leadingCoeff
      rw [hform, hlc] at hme
      simp [Polynomial.aeval_C, Polynomial.aeval_X] at hme
      exact ⟨-((minpoly F u).coeff 0),
        by rw [map_neg, neg_eq_iff_add_eq_zero]; linear_combination hme⟩
    · rintro ⟨u₀, hu₀⟩
      have hd : minpoly F u ∣ (X - C u₀) := by
        refine minpoly.dvd F u ?_
        simp [Polynomial.aeval_X, Polynomial.aeval_C, hu₀]
      have hle : (minpoly F u).natDegree ≤ 1 :=
        (Polynomial.natDegree_le_of_dvd hd
          (by exact fun hc => absurd (sub_eq_zero.mp hc) (Polynomial.X_ne_C u₀))).trans
          (le_of_eq (Polynomial.natDegree_X_sub_C u₀))
      omega
  have hsqiff : (∃ t : F, algebraMap F E t * algebraMap F E t = (u - v) ^ 2)
      ↔ (∃ u₀ : F, algebraMap F E u₀ = u) := by
    constructor
    · rintro ⟨t, ht⟩
      have h0 : (algebraMap F E t - (u - v)) * (algebraMap F E t + (u - v)) = 0 := by
        linear_combination ht
      obtain ⟨d, hd⟩ : ∃ d : F, algebraMap F E d = u - v := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact ⟨t, sub_eq_zero.mp h1⟩
        · exact ⟨-t, by rw [map_neg, neg_eq_iff_add_eq_zero]; exact h1⟩
      have h2eq : algebraMap F E (2 : F) = (2 : E) := by
        rw [show (2 : F) = ((2 : ℕ) : F) from Nat.cast_ofNat, map_natCast, Nat.cast_ofNat]
      refine ⟨(2:F)⁻¹ * ((-b) + d), ?_⟩
      rw [map_mul, map_inv₀ (algebraMap F E) 2, map_add, map_neg, ← hv1, hd,
        show (u + v) + (u - v) = (2 : E) * u by ring, ← h2eq]
      exact inv_mul_cancel_left₀ htwo' u
    · rintro ⟨u₀, hu₀⟩
      have hv0 : algebraMap F E ((-b) - u₀) = v := by
        rw [map_sub, map_neg, hu₀, ← hv1]
        ring
      have ht : algebraMap F E (u₀ - ((-b) - u₀)) = u - v := by
        rw [map_sub, hv0, hu₀]
      refine ⟨u₀ - ((-b) - u₀), ?_⟩
      rw [ht]
      ring
  refine ⟨?_, ?_⟩
  · rw [hcardG]
    refine ⟨fun h => hsqiff.mpr (hnd1iff.mp h), fun hsq => hnd1iff.mpr (hsqiff.mp hsq)⟩
  · rw [hcardG]
    refine ⟨fun h2 hsq => ?_, fun hnsq => ?_⟩
    · have h1 := hnd1iff.mpr (hsqiff.mp hsq)
      omega
    · rcases hdegcase with h | h
      · exact absurd (hsqiff.mpr (hnd1iff.mp h)) hnsq
      · exact h

-- FT cg6 (faithfulness of the root action)
/-- **FT cg6 (faithfulness of the root action).** If `E/F` is Galois and `E` is generated by
the root set of `f ∈ F[X]` (i.e. `E = F(f.rootSet E)`), then an element of `Gal(E/F)` fixing
every root of `f` is the identity; equivalently, the action of `Gal(E/F)` on `f.rootSet E`
is faithful.

Proof idea: the set `S` of elements fixing every root is a subgroup of `Gal(E/F)`, so every
root lies in the fixed field `IntermediateField.fixedField S`; since `E` is generated by the
roots, `fixedField S = ⊤`, and thus `ρ` fixes all of `E`, i.e. `ρ = 1`. -/
theorem gal_eq_one_of_fixes_rootSet {F E : Type u} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] {f : F[X]} (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤)
    (ρ : Gal(E/F)) (hρ : ∀ x ∈ f.rootSet E, ρ x = x) : ρ = 1 := by
  classical
  set S : Subgroup Gal(E/F) :=
    { carrier := {ρ' : Gal(E/F) | ∀ x ∈ f.rootSet E, ρ' x = x}
      one_mem' := by
        intro x _
        rfl
      mul_mem' := by
        intro a b ha hb x hx
        rw [show (a * b) x = a (b x) from rfl, hb x hx, ha x hx]
      inv_mem' := by
        intro a ha x hx
        calc (a⁻¹ : Gal(E/F)) x = a⁻¹ (a x) := by rw [ha x hx]
          _ = x := AlgEquiv.symm_apply_apply a x }
    with hS
  have hsub : f.rootSet E ⊆ ↑(IntermediateField.fixedField S) := by
    intro x hx
    exact (IntermediateField.mem_fixedField_iff S x).mpr fun ρ' hρ' => hρ' x hx
  have htop : (⊤ : IntermediateField F E) ≤ IntermediateField.fixedField S := by
    rw [← hgen, IntermediateField.adjoin_le_iff]
    exact hsub
  have hftop : IntermediateField.fixedField S = ⊤ := le_antisymm le_top htop
  refine AlgEquiv.ext fun x => ?_
  have hx : x ∈ IntermediateField.fixedField S := by
    rw [hftop]
    simp
  exact (IntermediateField.mem_fixedField_iff S x).mp hx ρ hρ

-- FT cg6 (injectivity of the action on the roots)
/-- **FT cg6 (injectivity of the action on the roots).** With the hypotheses of
`FT.gal_eq_one_of_fixes_rootSet`, the action homomorphism
`Gal(E/F) → Equiv.Perm ↥(f.rootSet E)` is injective: two automorphisms agreeing on every
root of `f` are equal.

Proof idea: if `σ` and `τ` agree on the roots, then `σ⁻¹ * τ` fixes every root, hence is `1`
by `FT.gal_eq_one_of_fixes_rootSet`, so `σ = τ`. -/
theorem gal_inj_on_rootSet {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    {f : F[X]} (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤)
    (σ τ : Gal(E/F)) (h : (MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) σ
        = (MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) τ) : σ = τ := by
  classical
  have hρ : ∀ x ∈ f.rootSet E, (σ.symm * τ) x = x := by
    intro x hx
    have h1 := DFunLike.congr_fun h ⟨x, hx⟩
    have h2 : ((MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) σ ⟨x, hx⟩ : E) = σ (x : E) := rfl
    have h3 : ((MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) τ ⟨x, hx⟩ : E) = τ (x : E) := rfl
    have hcoe : (σ (x : E)) = (τ (x : E)) :=
      h2.symm.trans ((congrArg Subtype.val h1).trans h3)
    rw [show (σ.symm * τ) x = σ.symm (τ x) from rfl, ← hcoe]
    exact AlgEquiv.symm_apply_apply σ x
  have h1 : (σ.symm * τ) = 1 := gal_eq_one_of_fixes_rootSet hgen _ hρ
  refine AlgEquiv.ext fun x => ?_
  have happ := congrArg (fun z : Gal(E/F) => z x) h1
  rw [show (σ.symm * τ) x = σ.symm (τ x) from rfl, show (1 : Gal(E/F)) x = x from rfl] at happ
  have happ2 := congrArg (fun z : E => σ z) happ
  rw [AlgEquiv.apply_symm_apply] at happ2
  exact happ2.symm

-- FT cg6 (root and root-set cardinality for a cubic)
/-- **FT cg6 (root and root-set cardinality for a cubic).** For a monic separable `f ∈ F[X]`
of degree `3` splitting over `E` there is a root `u ∈ E` of `f`, and the root set
`f.rootSet E` has cardinality `3` (the roots are distinct because `f` is separable).

Proof idea: `(f.map (algebraMap F E)).roots` is a nodup multiset of card `= natDegree f = 3`
(`Polynomial.splits_iff_card_roots`, nodup from separability), and the root set is its
underlying finset. -/
theorem cg6_root_card {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    {f : F[X]} (hf : f.Monic) (hsep : f.Separable)
    (hsplit : (f.map (algebraMap F E)).Splits) (h3 : f.natDegree = 3) :
    ∃ u : E, (Polynomial.aeval u) f = 0 ∧ Nat.card ↥(f.rootSet E) = 3 := by
  classical
  haveI : Fact ((f.map (algebraMap F E)).Splits) := ⟨hsplit⟩
  have hcard3 : Nat.card ↥(f.rootSet E) = 3 := by
    rw [Nat.card_eq_fintype_card, Polynomial.card_rootSet_eq_natDegree hsep hsplit, h3]
  have hmap0 : (f.map (algebraMap F E)) ≠ 0 := (hf.map (algebraMap F E)).ne_zero
  obtain ⟨u, hu⟩ : ∃ u : E, (Polynomial.aeval u) f = 0 := by
    obtain ⟨β, hβ⟩ := Multiset.exists_mem_of_ne_zero
      (Multiset.card_pos.mp (by rw [(Polynomial.splits_iff_card_roots).mp hsplit,
        hf.natDegree_map (algebraMap F E), h3]; norm_num))
    refine ⟨β, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact (Polynomial.mem_roots hmap0).mp hβ
  exact ⟨u, hu, hcard3⟩

-- FT cg6 (order of the Galois group of an irreducible cubic)
/-- **FT cg6** (order of the Galois group of an irreducible cubic). Let `f ∈ F[X]` be
monic, separable, irreducible of degree `3`, and let `E/F` be a finite Galois splitting
field for `f` (i.e. `E` is generated by `f.rootSet E`). Then `Gal(E/F)` acts faithfully and
transitively on the 3-element root set, so:
* `3 ∣ Nat.card Gal(E/F)` (the orbit of a root has 3 elements; orbit–stabilizer), and
* `Nat.card Gal(E/F) ≤ 6` (faithful action embeds `G_f` into `S_3`), hence
* `Nat.card Gal(E/F) = 3` or `Nat.card Gal(E/F) = 6`.

Proof idea: the orbit of a root `u` equals `f.rootSet E` (FT cg4, since
`f = minpoly F u`), of cardinality `3`; orbit–stabilizer
(`MulAction.orbitEquivQuotientStabilizer`, `Subgroup.index_mul_card`) gives `3 ∣ |G|`.
Faithfulness (`FT.gal_eq_one_of_fixes_rootSet`) makes the action homomorphism into
`Equiv.Perm ↥(f.rootSet E)` injective, and `|S_3| = 3! = 6`. The disjunction is the
cardinality computation `3k ≤ 6`, `k ≥ 1`. -/
theorem cg6_count {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [FiniteDimensional F E] {f : F[X]} (hf : f.Monic) (hsep : f.Separable)
    (hirr : Irreducible f) (h3 : f.natDegree = 3)
    (hsplit : (f.map (algebraMap F E)).Splits)
    (hgen : IntermediateField.adjoin F (f.rootSet E) = ⊤) :
    3 ∣ Nat.card Gal(E/F) ∧ Nat.card Gal(E/F) ≤ 6 ∧
      (Nat.card Gal(E/F) = 3 ∨ Nat.card Gal(E/F) = 6) := by
  classical
  obtain ⟨u, hu, hcard3⟩ := cg6_root_card hf hsep hsplit h3
  have hintu : IsIntegral F u := IsGalois.integral F u
  set m := minpoly F u with hm
  have key : f = m := minpoly.eq_of_irreducible_of_monic hirr hu hf
  have horbset : MulAction.orbit Gal(E/F) u = f.rootSet E := by
    show Set.range (fun τ : Gal(E/F) => τ • u) = f.rootSet E
    rw [← Set.image_univ,
      show (fun τ : Gal(E/F) => τ • u) = (fun τ : Gal(E/F) => τ u)
        from funext fun τ => rfl,
      orbit_eq_rootSet_minpoly u hintu, key]
  have hstab := Subgroup.index_mul_card (MulAction.stabilizer Gal(E/F) u)
  rw [Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Gal(E/F) u), horbset, hcard3]
    at hstab
  have hdvd : 3 ∣ Nat.card Gal(E/F) := ⟨_, hstab.symm⟩
  haveI : Fact ((f.map (algebraMap F E)).Splits) := ⟨hsplit⟩
  have hinj : Function.Injective ⇑(MulAction.toPermHom Gal(E/F) ↥(f.rootSet E)) := by
    intro σ τ h
    exact gal_inj_on_rootSet hgen σ τ h
  have hle : Nat.card Gal(E/F) ≤ 6 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (Equiv.Perm ↥(f.rootSet E)) :=
        Nat.card_le_card_of_injective _ hinj
      _ = (Nat.card ↥(f.rootSet E)).factorial := by
          simp only [Nat.card_eq_fintype_card]
          rw [Fintype.card_perm]
      _ = 6 := by rw [hcard3]; norm_num
  haveI : Nonempty Gal(E/F) := ⟨1⟩
  have hne0 : Nat.card Gal(E/F) ≠ 0 := ne_of_gt Nat.card_pos
  refine ⟨hdvd, hle, ?_⟩
  obtain ⟨k, hk⟩ := hdvd
  omega

-- FT cg6 (transitivity)
/-- **FT cg6 (transitivity).** For an irreducible separable cubic `f` splitting over the
Galois extension `E/F`, the group `Gal(E/F)` acts transitively on the root set
`f.rootSet E` (instance of FT `cg4`, using `0 < f.natDegree` since `f` is a cubic). -/
theorem cg6_transitive {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [FiniteDimensional F E] {f : F[X]} (hf : f.Monic) (hsep : f.Separable)
    (hirr : Irreducible f) (h3 : f.natDegree = 3)
    (hsplit : (f.map (algebraMap F E)).Splits) :
    ∀ α ∈ f.rootSet E, ∀ β ∈ f.rootSet E, ∃ σ : Gal(E/F), σ α = β := by
  refine (gal_transitive_iff_irreducible hf hsep hsplit ?_).mp hirr
  rw [h3]
  norm_num
