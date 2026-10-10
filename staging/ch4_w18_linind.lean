-- STAGING: FT ch. IV §8 linear independence of indeterminates (w18, verified under final
-- names FT.sum_X_mul_C_eq_zero / FT.sum_X_mul_C_inj). Paste inside namespace FT.

/-- FT IV §8 (van der Waerden θ-trick, linear independence of the indeterminates):
the elements `X i` of `MvPolynomial (Fin m) R` are linearly independent over `R`:
if `∑ i, X i * C (c i) = 0` then every coefficient `c i` vanishes.
Proof idea: evaluate at the indicator point `j ↦ if j = i then 1 else 0`; the
evaluation of the sum is `c i`, while the evaluation of `0` is `0`. -/
theorem sum_X_mul_C_eq_zero {R : Type*} [CommRing R] {m : ℕ} {c : Fin m → R}
    (h : ∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) R) * MvPolynomial.C (c i)) = 0 →
    ∀ i, c i = 0 := by
  intro i
  have he : MvPolynomial.eval (fun j => if j = i then (1 : R) else 0)
      (∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) R) * MvPolynomial.C (c j)) = 0 := by
    rw [h]; rfl
  rw [map_sum (MvPolynomial.eval (fun j => if j = i then (1 : R) else 0))] at he
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C] at he
  have h2 : ∀ j : Fin m, (fun j => if j = i then (1 : R) else 0) j * c j
      = if j = i then c j else 0 := by
    intro j; by_cases hj : j = i <;> simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => h2 j)] at he
  rw [Finset.sum_ite_eq' Finset.univ i c] at he
  simpa using he

/-- FT IV §8 (van der Waerden θ-trick): equality of the weighted sums determines the
weights: if `∑ i, X i * C (c i) = ∑ i, X i * C (d i)` in `MvPolynomial (Fin m) R`
then `c = d`. Proof idea: evaluate the equality at the indicator point
`j ↦ if j = i then 1 else 0`; both sides reduce to `c i` and `d i`. -/
theorem sum_X_mul_C_inj {R : Type*} [CommRing R] {m : ℕ} {c d : Fin m → R}
    (h : ∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) R) * MvPolynomial.C (c i)
        = ∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) R) * MvPolynomial.C (d i)) :
    c = d := by
  funext i
  have he : MvPolynomial.eval (fun j => if j = i then (1 : R) else 0)
      (∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) R) * MvPolynomial.C (c j)) =
      MvPolynomial.eval (fun j => if j = i then (1 : R) else 0)
        (∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) R) * MvPolynomial.C (d j)) := by rw [h]
  rw [map_sum (MvPolynomial.eval (fun j => if j = i then (1 : R) else 0)),
    map_sum (MvPolynomial.eval (fun j => if j = i then (1 : R) else 0))] at he
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C] at he
  have h2 : ∀ j : Fin m, ∀ w : Fin m → R, (fun j => if j = i then (1 : R) else 0) j * w j
      = if j = i then w j else 0 := by
    intro j _; by_cases hj : j = i <;> simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => h2 j c), Finset.sum_congr rfl (fun j _ => h2 j d)] at he
  rw [Finset.sum_ite_eq' Finset.univ i c, Finset.sum_ite_eq' Finset.univ i d] at he
  simpa using he
