-- STAGING: FT ch. IV §8 van der Waerden θ-trick preliminaries (cg25 heart; cg20 input),
-- re-derivation worker w14 deliverable, received verbatim. All 23 declarations verified
-- in shared REPL gen 8, axioms exactly [propext, Classical.choice, Quot.sound].
-- BLOCKED items (recorded, NOT in this file):
--   (i)   f(X,T) = ∏_σ (X − σ_T θ) has coefficients in F[T] (needs symmetric-poly/Vieta
--         packaging Mathlib v4.31 lacks)
--   (ii)  θ integral over F(T) (needs Frac(MvPoly K)/Frac(MvPoly F) finite-dim transport)
--   (iii) Galois-membership ⟸ direction (full construction plan in worker report)
--   cg25 isomorphism and cg20 final reduction depend on (i)-(iii).
-- Paste: both blocks inside namespace FT, in this order. Note the local-instance policy
-- of `fracAlg` (block 2): downstream consumers must `letI := fracAlg`.

open MvPolynomial Equiv

section Theta
variable {E : Type*} [CommRing E] {m : ℕ}

/-- FT IV §8 (van der Waerden): the element θ = T₁α₁ + ⋯ + T_mα_m, encoded as a
polynomial in the indeterminates T₁,…,T_m (the variables of `MvPolynomial (Fin m) E`)
with the roots αᵢ ∈ E as coefficients. -/
noncomputable def dedekindTheta (α : Fin m → E) : MvPolynomial (Fin m) E :=
  ∑ i, (X i : MvPolynomial (Fin m) E) * C (α i)

/-- The action of a ring homomorphism `g : E →+* E'` on θ: it applies `g` to the
coefficients, `g θ = ∑ Tᵢ g(αᵢ)`. -/
theorem map_dedekindTheta {E' : Type*} [CommRing E'] (g : E →+* E') (α : Fin m → E) :
    MvPolynomial.map g (dedekindTheta α) = dedekindTheta (g ∘ α) := by
  simp only [dedekindTheta, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C,
    Function.comp_apply]

/-- FT eq12, first form: the permutation σ_T of the indeterminates acts on θ by
sending the root tuple α to α ∘ σ.symm, i.e. σ_T θ = ∑ⱼ Tⱼ α_{σ⁻¹ j}. -/
theorem dedekindTheta_rename (α : Fin m → E) (σ : Equiv.Perm (Fin m)) :
    rename σ (dedekindTheta α) = dedekindTheta (α ∘ σ.symm) := by
  simp only [dedekindTheta, map_sum, map_mul, rename_X, rename_C, Function.comp_apply]
  refine Finset.sum_equiv (s := Finset.univ) (t := Finset.univ) σ (fun _ => by simp) (fun x _ => ?_)
  rw [Equiv.symm_apply_apply]

/-- FT eq12: `s_T s_α θ = θ`, i.e. the permutation σ of the roots followed by the
same permutation of the indeterminates fixes θ = ∑ Tᵢαᵢ. -/
theorem dedekindTheta_eq12 (α : Fin m → E) (σ : Equiv.Perm (Fin m)) :
    rename σ (dedekindTheta (α ∘ σ)) = dedekindTheta α := by
  rw [dedekindTheta_rename]
  congr 1
  simp [Function.comp_assoc]

/-- FT eq12, solved for the root permutation: s_α θ = s_T⁻¹ θ, i.e. applying the
root permutation σ to θ gives the T-permutation σ⁻¹ applied to θ. -/
theorem dedekindTheta_permAlpha (α : Fin m → E) (σ : Equiv.Perm (Fin m)) :
    dedekindTheta (α ∘ σ) = rename σ.symm (dedekindTheta α) := by
  rw [dedekindTheta_rename, Equiv.symm_symm]
end Theta

section Frac
variable {A B : Type*} [Field A] [Field B] [Algebra A B] {m : ℕ}

/-- FT IV §8: σ_T as a B-algebra automorphism of B(T₁,…,T_m), the field of fractions
of the polynomial ring in the indeterminates T₁,…,T_m; it permutes the T's. -/
noncomputable def sigmaTFrac (σ : Equiv.Perm (Fin m)) :
    FractionRing (MvPolynomial (Fin m) B) ≃ₐ[B] FractionRing (MvPolynomial (Fin m) B) :=
  IsFractionRing.fieldEquivOfAlgEquivHom (A := B) (B := MvPolynomial (Fin m) B) B
    (FractionRing (MvPolynomial (Fin m) B)) (MvPolynomial.renameEquiv B σ)

/-- The embedding A(T₁,…,T_m) ↪ B(T₁,…,T_m) induced by A ↪ B. -/
noncomputable def fracHom :
    FractionRing (MvPolynomial (Fin m) A) →ₐ[A] FractionRing (MvPolynomial (Fin m) B) :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) B)
      (FractionRing (MvPolynomial (Fin m) B))).comp
        (MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom A A B)))
    (by
      intro a b hab
      exact MvPolynomial.map_injective (algebraMap A B)
        (FaithfulSMul.algebraMap_injective A B)
        (by simpa [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply] using hab))

theorem fracHom_algebraMap (p : MvPolynomial (Fin m) A) :
    fracHom (algebraMap (MvPolynomial (Fin m) A)
      (FractionRing (MvPolynomial (Fin m) A)) p) =
      algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
        (MvPolynomial.map (algebraMap A B) p) := by
  simp [fracHom, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply]

theorem sigmaTFrac_algebraMap (σ : Equiv.Perm (Fin m)) (p : MvPolynomial (Fin m) B) :
    sigmaTFrac σ (algebraMap (MvPolynomial (Fin m) B)
      (FractionRing (MvPolynomial (Fin m) B)) p) =
      algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
        (MvPolynomial.renameEquiv B σ p) := by
  simp [sigmaTFrac]

/-- The T-permutation automorphisms on A(T₁,…,T_m) and on B(T₁,…,T_m) commute with
the coefficient embedding A(T₁,…,T_m) ↪ B(T₁,…,T_m). -/
theorem fracHom_sigmaT_comm (σ : Equiv.Perm (Fin m))
    (z : FractionRing (MvPolynomial (Fin m) A)) :
    fracHom (B := B) (sigmaTFrac σ z) = sigmaTFrac σ (fracHom (B := B) z) := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) A) z
  simp only [map_div₀, sigmaTFrac_algebraMap, fracHom_algebraMap, sigmaTFrac_algebraMap,
    MvPolynomial.renameEquiv_apply, MvPolynomial.map_rename]

/-- FT IV §8: θ = T₁α₁ + ⋯ + T_mα_m as an element of B(T₁,…,T_m), for a root tuple
α : Fin m → B. -/
noncomputable def dedekindThetaFrac (α : Fin m → B) :
    FractionRing (MvPolynomial (Fin m) B) :=
  algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B)) (dedekindTheta α)

/-- eq12 in the fraction field: σ_T θ = ∑ⱼ Tⱼ α_{σ⁻¹ j} inside B(T₁,…,T_m). -/
theorem sigmaTFrac_dedekindThetaFrac (σ : Equiv.Perm (Fin m)) (α : Fin m → B) :
    sigmaTFrac σ (dedekindThetaFrac α) = dedekindThetaFrac (α ∘ σ.symm) := by
  simp only [dedekindThetaFrac, sigmaTFrac_algebraMap, MvPolynomial.renameEquiv_apply,
    dedekindTheta_rename]
end Frac

section Abstract
open Polynomial
variable {M L : Type*} [Field M] [Field L] [Algebra M L]

/-- Evaluation under a ring automorphism of the coefficient field: evaluating the
`s`-transformed polynomial at `s x` is the `s`-image of the evaluation at `x`. -/
theorem eval₂_equiv_apply (s : L ≃+* L) (q : Polynomial L) (x : L) :
    Polynomial.eval₂ (s : L →+* L) (s x) q = s (Polynomial.eval x q) := by
  induction q using Polynomial.induction_on' with
  | add p q ihp ihq => simp [ihp, ihq]
  | monomial n a => simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial]

/-- FT IV §8, proof of Lemma cg25 (invariance criterion; FT 4423). Let `p : M[X]`
be monic and irreducible, let `θ : L` be a root of `p`, and let `s : L ≃+* L` be a
ring automorphism extending a ring automorphism `sM : M ≃+* M` (compatibility
`hcomp`). Then `sM` fixes `p` if and only if `s θ` is still a root of `p`, i.e.
iff `s` maps the linear factor `X - θ` into a linear factor of `p`.
Proof idea: if `s θ` is a root of both `p` and `sM p`, then the minimal polynomial
of `s θ` over `M` divides both; being nonconstant it makes `p` and `sM p`
associates, hence equal since both are monic. -/
theorem linearFactor_stabilizer (p : Polynomial M) (hp1 : p.Monic) (hp : Irreducible p)
    (θ : L) (s : L ≃+* L) (sM : M ≃+* M)
    (hcomp : ∀ z : M, s (algebraMap M L z) = algebraMap M L (sM z))
    (hroot : Polynomial.eval θ (Polynomial.map (algebraMap M L) p) = 0) :
    Polynomial.map sM.toRingHom p = p ↔
      Polynomial.eval (s θ) (Polynomial.map (algebraMap M L) p) = 0 := by
  have hroot' : Polynomial.eval₂ (algebraMap M L) θ p = 0 := by
    rw [Polynomial.eval₂_eq_eval_map]; exact hroot
  have hmap : RingHom.comp (algebraMap M L) sM.toRingHom = RingHom.comp s (algebraMap M L) := by
    ext z; simpa using (hcomp z).symm
  have hcomm : ∀ q : Polynomial M, Polynomial.map (algebraMap M L) (Polynomial.map sM.toRingHom q)
      = Polynomial.map s (Polynomial.map (algebraMap M L) q) := by
    intro q; rw [Polynomial.map_map, Polynomial.map_map, hmap]
  have hp' : Irreducible (Polynomial.map sM.toRingHom p) := by
    have h1 : Polynomial.map sM.toRingHom p = Polynomial.mapEquiv sM p := rfl
    rw [h1, MulEquiv.irreducible_iff]; exact hp
  have hmonic' : (Polynomial.map sM.toRingHom p).Monic := hp1.map _
  constructor
  · intro heq
    have h1 : Polynomial.map (algebraMap M L) p
        = Polynomial.map s (Polynomial.map (algebraMap M L) p) := by
      rw [← hcomm, heq]
    rw [h1, Polynomial.eval_map, eval₂_equiv_apply, ← Polynomial.eval₂_eq_eval_map,
      hroot', map_zero]
  · intro hev
    have hint : IsIntegral M (s θ) := ⟨p, hp1, by
      rw [Polynomial.eval₂_eq_eval_map]; exact hev⟩
    have hd1 : minpoly M (s θ) ∣ p :=
      minpoly.dvd M (s θ) (by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; exact hev)
    have hd2 : minpoly M (s θ) ∣ Polynomial.map sM.toRingHom p :=
      minpoly.dvd M (s θ) (by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hcomm, Polynomial.eval_map,
          eval₂_equiv_apply, ← Polynomial.eval₂_eq_eval_map, hroot', map_zero])
    exact Polynomial.eq_of_monic_of_associated hmonic' hp1
      (((minpoly.irreducible hint).associated_of_dvd hp' hd2).symm.trans
        ((minpoly.irreducible hint).associated_of_dvd hp hd1))

/-- FT IV §8 (heart of Lemma cg25, FT 4423): for `θ : L` algebraic over `M` with
minimal polynomial `p`, a ring automorphism `s` of `L` extending the ring
automorphism `sM` of `M` fixes `p` if and only if `s θ` has the same minimal
polynomial over `M` as `θ` (i.e. iff `s` maps the linear factor `X - θ` into a
linear factor of `p`).
Proof idea: combine the invariance criterion (a common root of two monic
irreducible polynomials forces them to be equal) with the characterization of
equality of minimal polynomials by vanishing. -/
theorem minpoly_stabilizer_equiv (θ : L) (hint : IsIntegral M θ)
    (s : L ≃+* L) (sM : M ≃+* M)
    (hcomp : ∀ z : M, s (algebraMap M L z) = algebraMap M L (sM z)) :
    Polynomial.map sM.toRingHom (minpoly M θ) = minpoly M θ ↔
      minpoly M (s θ) = minpoly M θ := by
  have hm : (minpoly M θ).Monic := minpoly.monic hint
  have hirr : Irreducible (minpoly M θ) := minpoly.irreducible hint
  have hroot : Polynomial.eval θ (Polynomial.map (algebraMap M L) (minpoly M θ)) = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval M θ
  rw [linearFactor_stabilizer _ hm hirr θ s sM hcomp hroot]
  constructor
  · intro hev
    have hint' : IsIntegral M (s θ) := ⟨minpoly M θ, hm, by
      rw [Polynomial.eval₂_eq_eval_map]; exact hev⟩
    exact ((minpoly.eq_iff_aeval_minpoly_eq_zero hint (c := s θ)).mpr
      (by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; exact hev)).symm
  · intro heq
    rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, ← heq]
    exact minpoly.aeval M (s θ)
end Abstract

open MvPolynomial Equiv Polynomial
variable {A B : Type*} [Field A] [Field B] [Algebra A B] {m : ℕ}

/-- The algebra structure of B(T₁,…,T_m) over A(T₁,…,T_m) induced by the coefficient
embedding A ↪ B; its algebraMap is the embedding `fracHom`. -/
@[implicit_reducible]
noncomputable def fracAlg : Algebra (FractionRing (MvPolynomial (Fin m) A))
    (FractionRing (MvPolynomial (Fin m) B)) :=
  RingHom.toAlgebra (fracHom (A := A) (B := B)).toRingHom

attribute [local instance] fracAlg

/-- The algebraMap of `fracAlg` is the embedding A(T₁,…,T_m) ↪ B(T₁,…,T_m). -/
theorem algebraMap_fracAlg :
    algebraMap (FractionRing (MvPolynomial (Fin m) A)) (FractionRing (MvPolynomial (Fin m) B)) =
      (fracHom (A := A) (B := B)).toRingHom := rfl

/-- FT IV §8 (heart of Lemma cg25), concrete form (FT 4423): the T-permutation σ_T
fixes the minimal polynomial f₁ of θ = ∑ Tᵢαᵢ over A(T₁,…,T_m) if and only if σ_T θ
has the same minimal polynomial over A(T₁,…,T_m) as θ, i.e. iff σ_T maps the linear
factor X - θ into a linear factor of f₁.
Proof idea: the abstract invariance criterion, instantiated with the σ_T-actions on
A(T₁,…,T_m) and B(T₁,…,T_m), which commute with the coefficient embedding. -/
theorem sigmaT_minpoly_iff (σ : Equiv.Perm (Fin m)) (α : Fin m → B)
    (hint : IsIntegral (FractionRing (MvPolynomial (Fin m) A)) (dedekindThetaFrac α)) :
    Polynomial.map (sigmaTFrac σ).toRingHom
        (minpoly (FractionRing (MvPolynomial (Fin m) A)) (dedekindThetaFrac α)) =
      minpoly (FractionRing (MvPolynomial (Fin m) A)) (dedekindThetaFrac α) ↔
    minpoly (FractionRing (MvPolynomial (Fin m) A))
        (sigmaTFrac σ (dedekindThetaFrac α)) =
      minpoly (FractionRing (MvPolynomial (Fin m) A)) (dedekindThetaFrac α) := by
  refine minpoly_stabilizer_equiv _ hint (sigmaTFrac σ).toRingEquiv
    (sigmaTFrac σ).toRingEquiv ?_
  intro z
  exact (fracHom_sigmaT_comm σ z).symm

/-- A coefficient automorphism τ of B fixes the embedded fraction field
A(T₁,…,T_m) pointwise. -/
theorem sigmaCoefFrac_ringHom_comm (τ : B ≃ₐ[A] B) :
    RingHom.comp
      (IsFractionRing.ringEquivOfRingEquiv
        (B := MvPolynomial (Fin m) B) (L := FractionRing (MvPolynomial (Fin m) B))
        (MvPolynomial.mapEquiv (Fin m) τ.toRingEquiv)).toRingHom
      (fracHom (A := A) (B := B)).toRingHom =
      (fracHom (A := A) (B := B)).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin m) A)
  intro p
  have h1 : (fracHom (A := A) (B := B)).toRingHom
      (algebraMap (MvPolynomial (Fin m) A) (FractionRing (MvPolynomial (Fin m) A)) p) =
      algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
        (MvPolynomial.map (algebraMap A B) p) := fracHom_algebraMap p
  rw [RingHom.comp_apply, h1]
  show (IsFractionRing.ringEquivOfRingEquiv
      (MvPolynomial.mapEquiv (Fin m) τ.toRingEquiv))
    (algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
      (MvPolynomial.map (algebraMap A B) p)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_map]
  exact congrArg (algebraMap (MvPolynomial (Fin m) B)
      (FractionRing (MvPolynomial (Fin m) B)))
    (congrArg (MvPolynomial.map · p) (RingHom.ext fun a => τ.commutes a))

/-- FT IV §8: a coefficient automorphism `τ : B ≃ₐ[A] B` extends to the fraction
field B(T₁,…,T_m) by acting trivially on the indeterminates; the result is an
A(T₁,…,T_m)-algebra automorphism. -/
noncomputable def sigmaCoefFrac (τ : B ≃ₐ[A] B) :
    FractionRing (MvPolynomial (Fin m) B) ≃ₐ[FractionRing (MvPolynomial (Fin m) A)]
      FractionRing (MvPolynomial (Fin m) B) where
  toRingEquiv := IsFractionRing.ringEquivOfRingEquiv
    (B := MvPolynomial (Fin m) B) (L := FractionRing (MvPolynomial (Fin m) B))
    (MvPolynomial.mapEquiv (Fin m) τ.toRingEquiv)
  commutes' z := by
    have h : (IsFractionRing.ringEquivOfRingEquiv
        (MvPolynomial.mapEquiv (Fin m) τ.toRingEquiv)).toRingHom
        (algebraMap (FractionRing (MvPolynomial (Fin m) A))
          (FractionRing (MvPolynomial (Fin m) B)) z) =
        algebraMap (FractionRing (MvPolynomial (Fin m) A))
          (FractionRing (MvPolynomial (Fin m) B)) z :=
      DFunLike.congr_fun (sigmaCoefFrac_ringHom_comm τ) z
    exact h

theorem sigmaCoefFrac_algebraMap (τ : B ≃ₐ[A] B) (p : MvPolynomial (Fin m) B) :
    sigmaCoefFrac τ (algebraMap (MvPolynomial (Fin m) B)
      (FractionRing (MvPolynomial (Fin m) B)) p) =
      algebraMap (MvPolynomial (Fin m) B) (FractionRing (MvPolynomial (Fin m) B))
        (MvPolynomial.map τ.toRingHom p) := by
  simp [sigmaCoefFrac]

/-- The extended coefficient automorphism maps θ = ∑ Tᵢαᵢ to ∑ Tᵢ τ(αᵢ). -/
theorem sigmaCoefFrac_dedekindThetaFrac (τ : B ≃ₐ[A] B) (α : Fin m → B) :
    sigmaCoefFrac τ (dedekindThetaFrac α) = dedekindThetaFrac (fun i => τ (α i)) := by
  simp only [dedekindThetaFrac, sigmaCoefFrac_algebraMap, map_dedekindTheta]
  have h : (τ.toRingEquiv.toRingHom ∘ α) = fun i => τ (α i) := by
    funext i; rfl
  rw [h]

/-- FT IV §8 (Galois-membership criterion, forward direction): if the root
permutation σ_α (αᵢ ↦ α_{σ i}) is realized by an A-automorphism τ of B (for B the
splitting field this says σ_α ∈ G_f), then θ and σ_α θ = ∑ Tᵢ α_{σ i} have the same
minimal polynomial over A(T₁,…,T_m).
Proof idea: τ extends to an A(T)-algebra automorphism of B(T) fixing the
indeterminates; it maps θ to σ_α θ, and minimal polynomials are invariant under
A(T)-algebra equivalences. -/
theorem minpoly_permRoot (σ : Equiv.Perm (Fin m)) (α : Fin m → B) (τ : B ≃ₐ[A] B)
    (hτ : ∀ i, τ (α i) = α (σ i)) :
    minpoly (FractionRing (MvPolynomial (Fin m) A)) (dedekindThetaFrac (α ∘ σ)) =
      minpoly (FractionRing (MvPolynomial (Fin m) A)) (dedekindThetaFrac α) := by
  have h2 : dedekindThetaFrac (fun i => τ (α i)) = dedekindThetaFrac (α ∘ σ) := by
    congr 1; funext i; exact hτ i
  have h3 := (minpoly.algEquiv_eq
    (A := FractionRing (MvPolynomial (Fin m) A)) (sigmaCoefFrac τ) (dedekindThetaFrac α)).symm
  rw [sigmaCoefFrac_dedekindThetaFrac] at h3
  rw [← h2]
  exact h3.symm
