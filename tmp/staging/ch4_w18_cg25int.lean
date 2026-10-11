-- STAGING: FT ch. IV §8 cg25 assembly worker (w18) deliverable — item (ii) [V] complete,
-- item (iii) ~90% (endgame not delivered), item (i) [B]. Received verbatim.
-- Verified under temp namespaces FT.CGD.* / FT.CGD2.* / FT.CGD4.* (zombie-REPL artifact);
-- delivered text = same proofs under one namespace FT.CGD. sum_X_mul_C_* verified under
-- final names. Re-run under one namespace before/with integration build.
-- Uses FT.fracAlg/fracHom/algebraMap_fracAlg/fracHom_algebraMap/dedekindThetaFrac (w14 block,
-- already in Target). BLOCKED: (i) f(X,T) ∈ F[X,T]; cg25 isomorphism; cg20 reduction.
-- Paste inside namespace FT (CGD is a sub-namespace of FT).

namespace CGD
open MvPolynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}

/-- The `F(T₁,…,T_m)`-algebra structure on `E(T₁,…,T_m)` induced by the coefficient
embedding `F ↪ E` (the same structure as `FT.fracAlg`). -/
noncomputable instance fracAlgCGD : Algebra (FractionRing (MvPolynomial (Fin m) F))
    (FractionRing (MvPolynomial (Fin m) E)) := FT.fracAlg

/-- The constants embedding of `a ∈ E` into `E(T₁,…,T_m)`. -/
noncomputable def constFrac (m : ℕ) (a : E) : FractionRing (MvPolynomial (Fin m) E) :=
  algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) (MvPolynomial.C a)

/-- The constants embedding `E →+* E(T₁,…,T_m)`. -/
noncomputable def constFracHom (m : ℕ) : E →+* FractionRing (MvPolynomial (Fin m) E) :=
  (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))).comp
    (algebraMap E (MvPolynomial (Fin m) E))

theorem constFracHom_apply (m : ℕ) (a : E) : constFracHom m a = constFrac m a := rfl

/-- The `F`-scalars of `F(T₁,…,T_m)` land in the constants of `E(T₁,…,T_m)`. -/
theorem algebraMap_F_constFrac (c : F) :
    algebraMap (FractionRing (MvPolynomial (Fin m) F)) (FractionRing (MvPolynomial (Fin m) E))
        (algebraMap F (FractionRing (MvPolynomial (Fin m) F)) c)
      = constFrac m (algebraMap F E c) := by
  have h1 : algebraMap F (FractionRing (MvPolynomial (Fin m) F)) c
      = algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F))
          (MvPolynomial.C c) := IsScalarTower.algebraMap_apply F (MvPolynomial (Fin m) F) _ c
  rw [h1, FT.algebraMap_fracAlg]
  show fracHom (A := F) (B := E)
      (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F))
        (MvPolynomial.C c)) = constFrac m (algebraMap F E c)
  rw [FT.fracHom_algebraMap, MvPolynomial.map_C]
  rfl

theorem constFracHom_comp_algebraMap (m : ℕ) :
    RingHom.comp (algebraMap (FractionRing (MvPolynomial (Fin m) F))
        (FractionRing (MvPolynomial (Fin m) E)))
      (algebraMap F (FractionRing (MvPolynomial (Fin m) F))) =
    RingHom.comp (constFracHom m) (algebraMap F E) :=
  RingHom.ext algebraMap_F_constFrac

/-- Elements of the base ring are integral over it. -/
theorem isIntegral_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (z : R) :
    IsIntegral R (algebraMap R S z) :=
  ⟨Polynomial.X - Polynomial.C z, Polynomial.monic_X_sub_C z, by simp⟩

/-- Constants `a` of `E` integral over `F` are integral in `E(T)` over `F(T)`. -/
theorem isIntegral_constFrac (m : ℕ) (a : E) (ha : IsIntegral F a) :
    IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (constFrac m a) := by
  refine ⟨(minpoly F a).map (algebraMap F (FractionRing (MvPolynomial (Fin m) F))),
    (minpoly.monic ha).map _, ?_⟩
  rw [Polynomial.eval₂_map, constFracHom_comp_algebraMap, ← constFracHom_apply m,
    ← Polynomial.hom_eval₂ (minpoly F a) (algebraMap F E) (constFracHom m) a]
  have h0 : Polynomial.eval₂ (algebraMap F E) a (minpoly F a) = 0 := by
    rw [← Polynomial.aeval_def]; exact minpoly.aeval F a
  rw [h0, map_zero]

/-- The indeterminate `X i` of `E(T)` is the image of the indeterminate of `F(T)`. -/
theorem algebraMap_X_eq (i : Fin m) :
    algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) (MvPolynomial.X i)
      = algebraMap (FractionRing (MvPolynomial (Fin m) F)) (FractionRing (MvPolynomial (Fin m) E))
          (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F))
            (MvPolynomial.X i)) := by
  rw [FT.algebraMap_fracAlg]
  show (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)))
      (MvPolynomial.X i) = (fracHom (A := F) (B := E)) (algebraMap (MvPolynomial (Fin m) F)
        (FractionRing (MvPolynomial (Fin m) F)) (MvPolynomial.X i))
  rw [FT.fracHom_algebraMap, MvPolynomial.map_X]

theorem term_eq (α : Fin m → E) (i : Fin m) :
    algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
        (MvPolynomial.X i * MvPolynomial.C (α i))
      = algebraMap (FractionRing (MvPolynomial (Fin m) F)) (FractionRing (MvPolynomial (Fin m) E))
          (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F))
            (MvPolynomial.X i)) * constFrac m (α i) := by
  rw [map_mul, algebraMap_X_eq (F := F) (E := E) (m := m) i, constFrac]

theorem dedekindThetaFrac_eq_sum (m : ℕ) (α : Fin m → E) :
    FT.dedekindThetaFrac (m := m) α
      = ∑ i, (algebraMap (FractionRing (MvPolynomial (Fin m) F))
            (FractionRing (MvPolynomial (Fin m) E))
            (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F))
              (MvPolynomial.X i)))
          * constFrac m (α i) := by
  have h1 : FT.dedekindThetaFrac (m := m) α
      = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
          (∑ i, MvPolynomial.X i * MvPolynomial.C (α i)) := rfl
  rw [h1, map_sum (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)))]
  exact Finset.sum_congr rfl fun i _ => term_eq α i

theorem sum_mem_integralClosure (m : ℕ) (α : Fin m → E) (hα : ∀ i, IsAlgebraic F (α i)) :
    (∑ i, (algebraMap (FractionRing (MvPolynomial (Fin m) F)) (FractionRing (MvPolynomial (Fin m) E))
        (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F))
          (MvPolynomial.X i))) * constFrac m (α i))
      ∈ integralClosure (FractionRing (MvPolynomial (Fin m) F))
        (FractionRing (MvPolynomial (Fin m) E)) := by
  apply Subalgebra.sum_mem
  intro i _
  apply Subalgebra.mul_mem
  · exact isIntegral_algebraMap
      (R := FractionRing (MvPolynomial (Fin m) F))
      (S := FractionRing (MvPolynomial (Fin m) E)) _
  · exact isIntegral_constFrac m (α i) (IsAlgebraic.isIntegral (hα i))

/-- **FT IV §8, item (ii): θ = T₁α₁ + ⋯ + T_mα_m is integral over `F(T₁,…,T_m)`.**
It suffices that every root `αᵢ` is algebraic over `F` (e.g. the αᵢ are the roots of a
polynomial in `F[X]`).
Proof idea: each summand `Tᵢ·ι(αᵢ)` is a product of integral elements over `F(T)` (the
indeterminate image `Tᵢ` is integral as an element of the base field; `ι(αᵢ)` satisfies
the image of `minpoly F (αᵢ)`), and the integral elements form a subalgebra
(`integralClosure`), to which the finite sum belongs. -/
theorem isIntegral_dedekindThetaFrac (m : ℕ) (α : Fin m → E) (hα : ∀ i, IsAlgebraic F (α i)) :
    IsIntegral (FractionRing (MvPolynomial (Fin m) F)) (FT.dedekindThetaFrac (m := m) α) := by
  have h := sum_mem_integralClosure m α hα
  rw [← dedekindThetaFrac_eq_sum m α] at h
  exact h

/-- Every polynomial over `E`, viewed as an element of `E(T₁,…,T_m)`, is integral over
`F(T₁,…,T_m)`, provided every element of `E` is integral over `F`.
Proof idea: induction on the polynomial; a monomial `T^n·ι(a)` is a product of the
integral element `algebraMap (T^n·1)` (it is the image of a polynomial over `F`) and
the constant `ι(a)`. -/
theorem isIntegral_algebraMap_polyE (hint : ∀ a : E, IsIntegral F a) (m : ℕ)
    (p : MvPolynomial (Fin m) E) :
    IsIntegral (FractionRing (MvPolynomial (Fin m) F))
      (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) p) := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro n a
    have hsplit : MvPolynomial.monomial n a = MvPolynomial.C a * MvPolynomial.monomial n 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [hsplit, map_mul]
    refine IsIntegral.mul ?_ ?_
    · exact isIntegral_constFrac m a (hint a)
    · have h1 : MvPolynomial.monomial n (1 : E)
          = MvPolynomial.map (algebraMap F E) (MvPolynomial.monomial n (1 : F)) := by
        rw [MvPolynomial.map_monomial]; simp
      have hmap : ∀ z : MvPolynomial (Fin m) F,
          algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
            (MvPolynomial.map (algebraMap F E) z)
          = algebraMap (FractionRing (MvPolynomial (Fin m) F)) (FractionRing (MvPolynomial (Fin m) E))
            (algebraMap (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)) z) := by
        intro z
        rw [FT.algebraMap_fracAlg]
        show algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E))
          (MvPolynomial.map (algebraMap F E) z)
          = (fracHom (A := F) (B := E)) (algebraMap (MvPolynomial (Fin m) F)
              (FractionRing (MvPolynomial (Fin m) F)) z)
        rw [FT.fracHom_algebraMap]
      rw [h1, hmap]
      exact isIntegral_algebraMap
        (R := FractionRing (MvPolynomial (Fin m) F))
        (S := FractionRing (MvPolynomial (Fin m) E)) _
  · intro p q hp hq
    rw [map_add]
    exact IsIntegral.add hp hq

/-- If `E` is algebraic over `F`, then every element of `E(T₁,…,T_m)` is algebraic over
`F(T₁,…,T_m)`. Proof idea: an element is a quotient `p/q` of images of polynomials over
`E`; these are integral over `F(T)` (induction on the polynomial), and the inverse of the
integral `q` is integral again (`IsAlgebraic.inv_iff`), so the quotient is integral. -/
theorem isAlgebraic_frac_of_algebraic {E : Type*} [Field E] {m : ℕ} (F : Type*) [Field F]
    [Algebra F E] [hAE : Algebra.IsAlgebraic F E] :
    Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E)) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, q, -, hx⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) E) x
  have hp := isIntegral_algebraMap_polyE
    (fun a => isAlgebraic_iff_isIntegral.mp (hAE.isAlgebraic a)) m p
  have hq := isIntegral_algebraMap_polyE
    (fun a => isAlgebraic_iff_isIntegral.mp (hAE.isAlgebraic a)) m q
  have hqi : IsIntegral (FractionRing (MvPolynomial (Fin m) F))
      ((algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) q)⁻¹) :=
    isAlgebraic_iff_isIntegral.mp
      (IsAlgebraic.inv_iff.mpr (isAlgebraic_iff_isIntegral.mpr hq))
  have hx' : x = algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) p
      * (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) q)⁻¹ := by
    rw [← hx, div_eq_mul_inv]
  have hint : IsIntegral (FractionRing (MvPolynomial (Fin m) F))
      (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) p
        * (algebraMap (MvPolynomial (Fin m) E) (FractionRing (MvPolynomial (Fin m) E)) q)⁻¹) :=
    IsIntegral.mul hp hqi
  rw [hx']
  exact isAlgebraic_iff_isIntegral.mpr hint

/-- Integrality is preserved under enlarging the base field to an intermediate field. -/
theorem isIntegral_of_le {E : Type*} [Field E] {m : ℕ} (F : Type*) [Field F] [Algebra F E]
    (L : IntermediateField (FractionRing (MvPolynomial (Fin m) F))
      (FractionRing (MvPolynomial (Fin m) E))) {x : FractionRing (MvPolynomial (Fin m) E)}
    (h : IsIntegral (FractionRing (MvPolynomial (Fin m) F)) x) : IsIntegral L x := by
  obtain ⟨p, hp1, hp2⟩ := h
  refine ⟨p.map (algebraMap (FractionRing (MvPolynomial (Fin m) F)) L), hp1.map _, ?_⟩
  rw [Polynomial.eval₂_map,
    ← IsScalarTower.algebraMap_eq (FractionRing (MvPolynomial (Fin m) F)) L
      (FractionRing (MvPolynomial (Fin m) E))]
  exact hp2

end CGD
