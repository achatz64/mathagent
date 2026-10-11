-- staging/ch4_w31_s4complete.lean — worker w31 (S₄/Klein block completion, FT IV §4).
-- STATUS per w31 report (REPL gen 22:26953):
-- * Part A (quarticKlein* through quarticKlein_normal) fully verified, axiom-clean;
--   four decls verified under tmp names (quarticKlein_card_tmp, _involution_mem_tmp,
--   _gen_conj_tmp, _normal_tmp) — proofs byte-identical, fresh re-verify needed.
-- * Part B opening verified verbatim through quarticPsi, incl. fixed quarticPairingIdx_perm
--   (bug 1: missing .symm in p=2 q=3 branch; bug 2: crossed rw names quarticPairingIdx_12/13
--   in p=1 block — fixed below, in the direction confirmed by REPL error messages:
--   p=1 q=2 needs rw _12, p=1 q=3 needs rw _13; the worker's swap was inverted).
-- * Parts B-D from quarticPsi_mul_apply onward NOT yet verified in this lineage;
--   spots to watch: `intro _; trivial` in orbit lemmas, Sylow/toSylow plumbing.
-- * Axiom batch over all main decls + private helpers still REQUIRED after fresh
--   re-elaboration.
-- Blocked at end by REPL-CONFLICT (orphan pid group 27004 holds ~7GB env).

namespace FT

/-! ## FT IV §4 (V/S₄ theory): the Klein four-group `V` -/

/-- FT IV §4: the first nontrivial element of the Klein group `V`: the double transposition
`(01)(23)`, i.e. `0↦1, 1↦0, 2↦3, 3↦2`. -/
def quarticKleinGen01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- FT IV §4: the second nontrivial element of the Klein group `V`: the double transposition
`(02)(13)`, i.e. `0↦2, 1↦3, 2↦0, 3↦1`. -/
def quarticKleinGen02 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- FT IV §4: the third nontrivial element of the Klein group `V`: the double transposition
`(03)(12)`, i.e. `0↦3, 1↦2, 2↦1, 3↦0`. -/
def quarticKleinGen03 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

@[simp] theorem quarticKleinGen01_apply_zero : quarticKleinGen01 0 = 1 := rfl
@[simp] theorem quarticKleinGen01_apply_one : quarticKleinGen01 1 = 0 := rfl
@[simp] theorem quarticKleinGen01_apply_two : quarticKleinGen01 2 = 3 := rfl
@[simp] theorem quarticKleinGen01_apply_three : quarticKleinGen01 3 = 2 := rfl
@[simp] theorem quarticKleinGen02_apply_zero : quarticKleinGen02 0 = 2 := rfl
@[simp] theorem quarticKleinGen02_apply_one : quarticKleinGen02 1 = 3 := rfl
@[simp] theorem quarticKleinGen02_apply_two : quarticKleinGen02 2 = 0 := rfl
@[simp] theorem quarticKleinGen02_apply_three : quarticKleinGen02 3 = 1 := rfl
@[simp] theorem quarticKleinGen03_apply_zero : quarticKleinGen03 0 = 3 := rfl
@[simp] theorem quarticKleinGen03_apply_one : quarticKleinGen03 1 = 2 := rfl
@[simp] theorem quarticKleinGen03_apply_two : quarticKleinGen03 2 = 1 := rfl
@[simp] theorem quarticKleinGen03_apply_three : quarticKleinGen03 3 = 0 := rfl

private theorem quarticKleinGen01_sq : quarticKleinGen01 * quarticKleinGen01 = 1 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen02_sq : quarticKleinGen02 * quarticKleinGen02 = 1 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen03_sq : quarticKleinGen03 * quarticKleinGen03 = 1 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen01_mul_gen02 :
    quarticKleinGen01 * quarticKleinGen02 = quarticKleinGen03 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen02_mul_gen01 :
    quarticKleinGen02 * quarticKleinGen01 = quarticKleinGen03 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen01_mul_gen03 :
    quarticKleinGen01 * quarticKleinGen03 = quarticKleinGen02 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen03_mul_gen01 :
    quarticKleinGen03 * quarticKleinGen01 = quarticKleinGen02 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen02_mul_gen03 :
    quarticKleinGen02 * quarticKleinGen03 = quarticKleinGen01 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen03_mul_gen02 :
    quarticKleinGen03 * quarticKleinGen02 = quarticKleinGen01 := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

private theorem quarticKleinGen01_inv : quarticKleinGen01⁻¹ = quarticKleinGen01 :=
  inv_eq_iff_mul_eq_one.mpr quarticKleinGen01_sq

private theorem quarticKleinGen02_inv : quarticKleinGen02⁻¹ = quarticKleinGen02 :=
  inv_eq_iff_mul_eq_one.mpr quarticKleinGen02_sq

private theorem quarticKleinGen03_inv : quarticKleinGen03⁻¹ = quarticKleinGen03 :=
  inv_eq_iff_mul_eq_one.mpr quarticKleinGen03_sq

private theorem quarticKleinGen01_noFix : ∀ i : Fin 4, quarticKleinGen01 i ≠ i := by
  intro i; fin_cases i <;> simp

private theorem quarticKleinGen02_noFix : ∀ i : Fin 4, quarticKleinGen02 i ≠ i := by
  intro i; fin_cases i <;> simp

private theorem quarticKleinGen03_noFix : ∀ i : Fin 4, quarticKleinGen03 i ≠ i := by
  intro i; fin_cases i <;> simp

private theorem quarticKleinGen01_ne_one : quarticKleinGen01 ≠ (1 : Equiv.Perm (Fin 4)) := by
  intro h
  have h0 : quarticKleinGen01 0 = (1 : Equiv.Perm (Fin 4)) 0 := DFunLike.congr_fun h 0
  rw [quarticKleinGen01_apply_zero] at h0
  have h1 : (1 : Equiv.Perm (Fin 4)) 0 = 0 := rfl
  rw [h1] at h0
  exact absurd h0 (by decide)

private theorem quarticKleinGen02_ne_one : quarticKleinGen02 ≠ (1 : Equiv.Perm (Fin 4)) := by
  intro h
  have h0 : quarticKleinGen02 0 = (1 : Equiv.Perm (Fin 4)) 0 := DFunLike.congr_fun h 0
  rw [quarticKleinGen02_apply_zero] at h0
  have h1 : (1 : Equiv.Perm (Fin 4)) 0 = 0 := rfl
  rw [h1] at h0
  exact absurd h0 (by decide)

private theorem quarticKleinGen03_ne_one : quarticKleinGen03 ≠ (1 : Equiv.Perm (Fin 4)) := by
  intro h
  have h0 : quarticKleinGen03 0 = (1 : Equiv.Perm (Fin 4)) 0 := DFunLike.congr_fun h 0
  rw [quarticKleinGen03_apply_zero] at h0
  have h1 : (1 : Equiv.Perm (Fin 4)) 0 = 0 := rfl
  rw [h1] at h0
  exact absurd h0 (by decide)

private theorem quarticKleinGen01_ne_quarticKleinGen02 :
    quarticKleinGen01 ≠ quarticKleinGen02 := by
  intro h
  have h0 : quarticKleinGen01 0 = quarticKleinGen02 0 := DFunLike.congr_fun h 0
  rw [quarticKleinGen01_apply_zero, quarticKleinGen02_apply_zero] at h0
  exact absurd h0 (by decide)

private theorem quarticKleinGen01_ne_quarticKleinGen03 :
    quarticKleinGen01 ≠ quarticKleinGen03 := by
  intro h
  have h0 : quarticKleinGen01 0 = quarticKleinGen03 0 := DFunLike.congr_fun h 0
  rw [quarticKleinGen01_apply_zero, quarticKleinGen03_apply_zero] at h0
  exact absurd h0 (by decide)

private theorem quarticKleinGen02_ne_quarticKleinGen03 :
    quarticKleinGen02 ≠ quarticKleinGen03 := by
  intro h
  have h0 : quarticKleinGen02 0 = quarticKleinGen03 0 := DFunLike.congr_fun h 0
  rw [quarticKleinGen02_apply_zero, quarticKleinGen03_apply_zero] at h0
  exact absurd h0 (by decide)

private theorem quarticKlein_carrier_mul_mem {a b : Equiv.Perm (Fin 4)}
    (ha : a ∈ ({1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03} :
      Set (Equiv.Perm (Fin 4))))
    (hb : b ∈ ({1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03} :
      Set (Equiv.Perm (Fin 4)))) :
    a * b ∈ ({1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03} :
      Set (Equiv.Perm (Fin 4))) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
  rcases ha with rfl|rfl|rfl|rfl <;>
    rcases hb with rfl|rfl|rfl|rfl <;>
    simp [mul_one, one_mul, quarticKleinGen01_sq, quarticKleinGen02_sq, quarticKleinGen03_sq,
      quarticKleinGen01_mul_gen02, quarticKleinGen02_mul_gen01, quarticKleinGen01_mul_gen03,
      quarticKleinGen03_mul_gen01, quarticKleinGen02_mul_gen03, quarticKleinGen03_mul_gen02]

private theorem quarticKlein_carrier_inv_mem {a : Equiv.Perm (Fin 4)}
    (ha : a ∈ ({1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03} :
      Set (Equiv.Perm (Fin 4)))) :
    a⁻¹ ∈ ({1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03} :
      Set (Equiv.Perm (Fin 4))) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl|rfl|rfl|rfl <;>
    simp [inv_one, quarticKleinGen01_inv, quarticKleinGen02_inv, quarticKleinGen03_inv]

/-- FT IV §4: the Klein four-group `V = {1, (01)(23), (02)(13), (03)(12)}` as a subgroup
of `S₄`; the kernel of the slot-permutation homomorphism `quarticSlotHom`. -/
def quarticKlein : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03}
  one_mem' := Or.inl rfl
  mul_mem' := @quarticKlein_carrier_mul_mem
  inv_mem' := @quarticKlein_carrier_inv_mem

/-- FT IV §4: membership in `V` is exactly being `1` or one of the three double
transpositions. -/
theorem quarticKlein_eq (σ : Equiv.Perm (Fin 4)) :
    σ ∈ quarticKlein ↔ σ = 1 ∨ σ = quarticKleinGen01 ∨ σ = quarticKleinGen02 ∨
      σ = quarticKleinGen03 := Iff.rfl

/-- FT IV §4: the Klein group `V` has order `4`. -/
theorem quarticKlein_card : Nat.card ↥quarticKlein = 4 := by
  have hA : ¬ (1 : Equiv.Perm (Fin 4)) ∈ insert quarticKleinGen01
      (insert quarticKleinGen02 ({quarticKleinGen03} : Set (Equiv.Perm (Fin 4)))) := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, Ne.symm quarticKleinGen01_ne_one,
      Ne.symm quarticKleinGen02_ne_one, Ne.symm quarticKleinGen03_ne_one]
  have hB : ¬ quarticKleinGen01 ∈ insert quarticKleinGen02
      ({quarticKleinGen03} : Set (Equiv.Perm (Fin 4))) := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff,
      quarticKleinGen01_ne_quarticKleinGen02, quarticKleinGen01_ne_quarticKleinGen03]
  have hC : ¬ quarticKleinGen02 ∈ ({quarticKleinGen03} :
      Set (Equiv.Perm (Fin 4))) := by
    simp [Set.mem_singleton_iff, quarticKleinGen02_ne_quarticKleinGen03]
  have h0 : Nat.card ↥quarticKlein = Nat.card
      ↥({1, quarticKleinGen01, quarticKleinGen02, quarticKleinGen03} :
        Set (Equiv.Perm (Fin 4))) := rfl
  rw [h0, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hA,
    Set.ncard_insert_of_notMem hB, Set.ncard_insert_of_notMem hC, Set.ncard_singleton]

private theorem quarticKlein_fin4 (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hv : x.val < 4 := x.isLt
  rcases Nat.lt_or_ge x.val 1 with h1 | h2
  · exact Or.inl (Fin.eq_of_val_eq (by omega))
  · rcases Nat.lt_or_ge x.val 2 with h1' | h2'
    · exact Or.inr (Or.inl (Fin.eq_of_val_eq (by omega)))
    · rcases Nat.lt_or_ge x.val 3 with h1'' | h2''
      · exact Or.inr (Or.inr (Or.inl (Fin.eq_of_val_eq (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Fin.eq_of_val_eq (by omega))))

/-- FT IV §4 (private): an involution of `{0,1,2,3}` without fixed points is one of the
three double transpositions, hence lies in `V`. -/
private theorem quarticKlein_involution_mem {σ : Equiv.Perm (Fin 4)} (hsq : σ * σ = 1)
    (hfix : ∀ i : Fin 4, σ i ≠ i) : σ ∈ quarticKlein := by
  have hinv : ∀ i : Fin 4, σ (σ i) = i := fun i => by
    have h := DFunLike.congr_fun hsq i
    rw [Equiv.Perm.mul_apply] at h
    exact h.trans rfl
  rcases quarticKlein_fin4 (σ 0) with h0|h0|h0|h0
  · exact absurd h0 (hfix 0)
  · have h0' := hinv 0
    rw [h0] at h0'
    have h1 : σ 1 = 0 := h0'
    have h2 : σ 2 = 3 := by
      rcases quarticKlein_fin4 (σ 2) with hc|hc|hc|hc
      · exact absurd (Equiv.injective σ (h1.trans hc.symm)) (by decide)
      · exact absurd (Equiv.injective σ (h0.trans hc.symm)) (by decide)
      · exact absurd hc (hfix 2)
      · exact hc
    have h2' := hinv 2
    rw [h2] at h2'
    have h3 : σ 3 = 2 := h2'
    refine (quarticKlein_eq σ).mpr (Or.inr (Or.inl ?_))
    apply Equiv.ext
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · have h0' := hinv 0
    rw [h0] at h0'
    have h2 : σ 2 = 0 := h0'
    have h1 : σ 1 = 3 := by
      rcases quarticKlein_fin4 (σ 1) with hc|hc|hc|hc
      · exact absurd (Equiv.injective σ (hc.trans h2.symm)) (by decide)
      · exact absurd hc (hfix 1)
      · exact absurd (Equiv.injective σ (h0.trans hc.symm)) (by decide)
      · exact hc
    have h1' := hinv 1
    rw [h1] at h1'
    have h3 : σ 3 = 1 := h1'
    refine (quarticKlein_eq σ).mpr (Or.inr (Or.inr (Or.inl ?_)))
    apply Equiv.ext
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · have h0' := hinv 0
    rw [h0] at h0'
    have h3 : σ 3 = 0 := h0'
    have h1 : σ 1 = 2 := by
      rcases quarticKlein_fin4 (σ 1) with hc|hc|hc|hc
      · exact absurd (Equiv.injective σ (hc.trans h3.symm)) (by decide)
      · exact absurd hc (hfix 1)
      · exact hc
      · exact absurd (Equiv.injective σ (hc.trans h0.symm)) (by decide)
    have h1' := hinv 1
    rw [h1] at h1'
    have h2 : σ 2 = 1 := h1'
    refine (quarticKlein_eq σ).mpr (Or.inr (Or.inr (Or.inr ?_)))
    apply Equiv.ext
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3]

/-- FT IV §4 (private): conjugating a fixed-point-free involution (one of the double
transpositions) by any permutation of `{0,1,2,3}` again yields a fixed-point-free
involution, hence an element of `V`. -/
private theorem quarticKlein_gen_conj {σ g : Equiv.Perm (Fin 4)} (hgi : g * g = 1)
    (hfix : ∀ i : Fin 4, g i ≠ i) : σ * g * σ⁻¹ ∈ quarticKlein := by
  apply quarticKlein_involution_mem
  · have h : (σ * g * σ⁻¹) * (σ * g * σ⁻¹) = σ * (g * g) * σ⁻¹ := by group
    rw [h, hgi, mul_one]
    exact mul_inv_cancel σ
  · intro i hi
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hi
    have h3 : g (σ⁻¹ i) = σ⁻¹ i :=
      (Equiv.symm_apply_apply σ (g (σ⁻¹ i))).symm.trans (congrArg (fun x => σ⁻¹ x) hi)
    exact absurd h3 (hfix (σ⁻¹ i))

/-- FT IV §4: the Klein group `V` is normal in `S₄`: conjugating a double transposition
by any permutation of `{0,1,2,3}` again yields a double transposition. -/
theorem quarticKlein_normal : quarticKlein.Normal := by
  constructor
  intro n hn g
  rcases (quarticKlein_eq n).mp hn with rfl|rfl|rfl|rfl
  · rw [mul_one]
    exact (quarticKlein_eq (g * g⁻¹)).mpr (Or.inl (mul_inv_cancel g))
  · exact quarticKlein_gen_conj quarticKleinGen01_sq quarticKleinGen01_noFix
  · exact quarticKlein_gen_conj quarticKleinGen02_sq quarticKleinGen02_noFix
  · exact quarticKlein_gen_conj quarticKleinGen03_sq quarticKleinGen03_noFix

/-! ## FT IV §4 (V/S₄ theory): the three pairings and the slot action -/

/-- FT IV §4: the index `0, 1, 2` of the perfect matching on `{0,1,2,3}` containing the
pair `(i, j)` (with `i = j` also giving index `2`): matching `0 = {{0,1},{2,3}}`,
`1 = {{0,2},{1,3}}`, `2 = {{0,3},{1,2}}`.  This indexes the three pairings of the four
roots permuted by `S₄`, whose kernel is the Klein group `V`. -/
def quarticPairingIdx (i j : Fin 4) : Fin 3 :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1
  else 2

theorem quarticPairingIdx_eq_zero {i j : Fin 4} : quarticPairingIdx i j = 0 ↔
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp [quarticPairingIdx]

theorem quarticPairingIdx_eq_one {i j : Fin 4} : quarticPairingIdx i j = 1 ↔
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
  fin_cases i <;> fin_cases j <;> simp [quarticPairingIdx]

/-- FIX: the `i = j` disjunct is essential (the `else` branch of the definition). -/
theorem quarticPairingIdx_eq_two {i j : Fin 4} : quarticPairingIdx i j = 2 ↔
    i = j ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  fin_cases i <;> fin_cases j <;> simp [quarticPairingIdx]

@[simp] theorem quarticPairingIdx_01 : quarticPairingIdx 0 1 = 0 := rfl
@[simp] theorem quarticPairingIdx_02 : quarticPairingIdx 0 2 = 1 := rfl
@[simp] theorem quarticPairingIdx_03 : quarticPairingIdx 0 3 = 2 := rfl
@[simp] theorem quarticPairingIdx_10 : quarticPairingIdx 1 0 = 0 := rfl
@[simp] theorem quarticPairingIdx_20 : quarticPairingIdx 2 0 = 1 := rfl
@[simp] theorem quarticPairingIdx_30 : quarticPairingIdx 3 0 = 2 := rfl
@[simp] theorem quarticPairingIdx_13 : quarticPairingIdx 1 3 = 1 := rfl
@[simp] theorem quarticPairingIdx_31 : quarticPairingIdx 3 1 = 1 := rfl
@[simp] theorem quarticPairingIdx_12 : quarticPairingIdx 1 2 = 2 := rfl
@[simp] theorem quarticPairingIdx_21 : quarticPairingIdx 2 1 = 2 := rfl
@[simp] theorem quarticPairingIdx_23 : quarticPairingIdx 2 3 = 0 := rfl
@[simp] theorem quarticPairingIdx_32 : quarticPairingIdx 3 2 = 0 := rfl

@[simp] theorem quarticPairingIdx_symm {i j : Fin 4} :
    quarticPairingIdx i j = quarticPairingIdx j i := by
  fin_cases i <;> fin_cases j <;> simp [quarticPairingIdx]

private theorem fin3_cases3 (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have hv : x.val < 3 := x.isLt
  rcases Nat.lt_or_ge x.val 1 with h1 | h2
  · exact Or.inl (Fin.eq_of_val_eq (by omega))
  · rcases Nat.lt_or_ge x.val 2 with h1' | h2'
    · exact Or.inr (Or.inl (Fin.eq_of_val_eq (by omega)))
    · exact Or.inr (Or.inr (Fin.eq_of_val_eq (by omega)))

private theorem fin4_cases4 (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hv : x.val < 4 := x.isLt
  rcases Nat.lt_or_ge x.val 1 with h1 | h2
  · exact Or.inl (Fin.eq_of_val_eq (by omega))
  · rcases Nat.lt_or_ge x.val 2 with h1' | h2'
    · exact Or.inr (Or.inl (Fin.eq_of_val_eq (by omega)))
    · rcases Nat.lt_or_ge x.val 3 with h1'' | h2''
      · exact Or.inr (Or.inr (Or.inl (Fin.eq_of_val_eq (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Fin.eq_of_val_eq (by omega))))

/-- FT IV §4: two distinct pairs `(i, j)` and `(k, l)` which are complementary in
`{0, 1, 2, 3}` lie in the same perfect matching. -/
theorem quarticPairingIdx_compl {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    quarticPairingIdx a b = quarticPairingIdx c d := by
  rcases fin3_cases3 (quarticPairingIdx a b) with h0 | h1 | h2
  · rw [quarticPairingIdx_eq_zero] at h0
    rcases h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      fin_cases c <;> fin_cases d <;> simp_all [quarticPairingIdx]
  · rw [quarticPairingIdx_eq_one] at h1
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      fin_cases c <;> fin_cases d <;> simp_all [quarticPairingIdx]
  · rw [quarticPairingIdx_eq_two] at h2
    rcases h2 with hab' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      fin_cases c <;> fin_cases d <;> simp_all [quarticPairingIdx]

/-- FT IV §4: the permutation of the three pairings induced by `σ ∈ S₄`:
`σ` sends the `k`-th pairing (the perfect matching whose pair containing `0` is `(0, k+1)`)
to the pairing containing the pair `(σ 0, σ (k+1))`.  The kernel of this action is exactly
the Klein group `V`. -/
def quarticPsi (σ : Equiv.Perm (Fin 4)) (k : Fin 3) : Fin 3 :=
  quarticPairingIdx (σ 0) (σ ⟨(k : ℕ) + 1, by omega⟩)

/-- FT IV §4: `σ` maps the matching containing a pair `(p, q)` (with `p ≠ q`) to the
matching containing its image `(σ p, σ q)`. -/
theorem quarticPairingIdx_perm (σ : Equiv.Perm (Fin 4)) {p q : Fin 4} (hpq : p ≠ q) :
    quarticPairingIdx (σ p) (σ q) = quarticPsi σ (quarticPairingIdx p q) := by
  have hσ : ∀ i j : Fin 4, i ≠ j → σ i ≠ σ j := fun i j h hc => h (Equiv.injective σ hc)
  rcases fin4_cases4 p with rfl|rfl|rfl|rfl
  · rcases fin4_cases4 q with rfl|rfl|rfl|rfl
    · exact absurd rfl hpq
    · simp only [quarticPairingIdx_01]; rfl
    · simp only [quarticPairingIdx_02]; rfl
    · simp only [quarticPairingIdx_03]; rfl
  · rcases fin4_cases4 q with rfl|rfl|rfl|rfl
    · simp only [quarticPairingIdx_10]; rw [quarticPairingIdx_symm]; rfl
    · exact absurd rfl hpq
    · rw [quarticPairingIdx_12]
      exact (quarticPairingIdx_compl (hσ 0 3 (by decide)) (hσ 1 2 hpq)
        (hσ 1 0 (by decide)) (hσ 1 3 (by decide)) (hσ 2 0 (by decide))
        (hσ 2 3 (by decide))).symm
    · rw [quarticPairingIdx_13]
      exact (quarticPairingIdx_compl (hσ 0 2 (by decide)) (hσ 1 3 hpq)
        (hσ 1 0 (by decide)) (hσ 1 2 (by decide)) (hσ 3 0 (by decide))
        (hσ 3 2 (by decide))).symm
  · rcases fin4_cases4 q with rfl|rfl|rfl|rfl
    · simp only [quarticPairingIdx_20]; rw [quarticPairingIdx_symm]; rfl
    · rw [quarticPairingIdx_21]
      exact (quarticPairingIdx_compl (hσ 0 3 (by decide)) (hσ 2 1 hpq)
        (hσ 2 0 (by decide)) (hσ 2 3 (by decide)) (hσ 1 0 (by decide))
        (hσ 1 3 (by decide))).symm
    · exact absurd rfl hpq
    · rw [quarticPairingIdx_23]
      exact (quarticPairingIdx_compl (hσ 0 1 (by decide)) (hσ 2 3 hpq)
        (hσ 2 0 (by decide)) (hσ 2 1 (by decide)) (hσ 3 0 (by decide))
        (hσ 3 1 (by decide))).symm
  · rcases fin4_cases4 q with rfl|rfl|rfl|rfl
    · simp only [quarticPairingIdx_30]; rw [quarticPairingIdx_symm]; rfl
    · rw [quarticPairingIdx_31]
      exact (quarticPairingIdx_compl (hσ 0 2 (by decide)) (hσ 3 1 hpq)
        (hσ 3 0 (by decide)) (hσ 3 2 (by decide)) (hσ 1 0 (by decide))
        (hσ 1 2 (by decide))).symm
    · rw [quarticPairingIdx_32]
      exact (quarticPairingIdx_compl (hσ 0 1 (by decide)) (hσ 3 2 hpq)
        (hσ 3 0 (by decide)) (hσ 3 1 (by decide)) (hσ 2 0 (by decide))
        (hσ 2 1 (by decide))).symm
    · exact absurd rfl hpq

theorem quarticPsi_mul_apply (σ τ : Equiv.Perm (Fin 4)) (k : Fin 3) :
    quarticPsi (σ * τ) k = quarticPsi σ (quarticPsi τ k) := by
  have h0 : τ 0 ≠ τ ⟨(k : ℕ) + 1, by omega⟩ := fun hc => by
    have hv := k.isLt
    have hij : (0 : Fin 4) = ⟨(k : ℕ) + 1, by omega⟩ := Equiv.injective τ hc
    have hval : (0 : ℕ) = ((k : ℕ) + 1 : ℕ) := congrArg Fin.val hij
    omega
  show quarticPairingIdx ((σ * τ) 0) ((σ * τ) ⟨(k : ℕ) + 1, by omega⟩)
    = quarticPsi σ (quarticPsi τ k)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact quarticPairingIdx_perm σ h0

theorem quarticPsi_one (k : Fin 3) : quarticPsi 1 k = k := by
  rcases fin3_cases3 k with rfl|rfl|rfl <;> rfl

/-- FT IV §4: the permutation of the three pairings induced by `σ`, as a bijection of
`Fin 3`; `σ ↦ quarticPsiEquiv σ` is a homomorphism with kernel `V`. -/
def quarticPsiEquiv (σ : Equiv.Perm (Fin 4)) : Fin 3 ≃ Fin 3 where
  toFun := quarticPsi σ
  invFun := quarticPsi σ⁻¹
  left_inv k := by rw [← quarticPsi_mul_apply σ⁻¹ σ k, inv_mul_cancel, quarticPsi_one]
  right_inv k := by rw [← quarticPsi_mul_apply σ σ⁻¹ k, mul_inv_cancel, quarticPsi_one]

/-- FT IV §4: the homomorphism `S₄ → Sym(pairings) ≅ S₃`; its kernel is the Klein group `V`
(the elements of cycle type `2+2` preserve all three pairings). -/
def quarticSlotHom : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) where
  toFun σ := quarticPsiEquiv σ
  map_one' := Equiv.ext fun k => quarticPsi_one k
  map_mul' σ τ := Equiv.ext fun k => by
    show quarticPsi (σ * τ) k = quarticPsi σ (quarticPsi τ k)
    exact quarticPsi_mul_apply σ τ k

/-- FT IV §4: the induced action of `S₄` on the three pairings. -/
@[reducible]
def quarticSlotAction : MulAction (Equiv.Perm (Fin 4)) (Fin 3) where
  smul σ k := quarticPsi σ k
  one_smul k := quarticPsi_one k
  mul_smul σ τ k := quarticPsi_mul_apply σ τ k

/-- FT IV §4: the three partially symmetric values of a tuple `t`:
`quarticVal 0 t = α = t₀t₁ + t₂t₃`, `quarticVal 1 t = β = t₀t₂ + t₁t₃`,
`quarticVal 2 t = γ = t₀t₃ + t₁t₂`. -/
def quarticVal {K : Type*} [CommRing K] (k : Fin 3) (t : Fin 4 → K) : K :=
  if k = 0 then quarticAlpha (t 0) (t 1) (t 2) (t 3)
  else if k = 1 then quarticBeta (t 0) (t 1) (t 2) (t 3)
  else quarticGamma (t 0) (t 1) (t 2) (t 3)

@[simp] theorem quarticVal_zero {K : Type*} [CommRing K] (t : Fin 4 → K) :
    quarticVal 0 t = quarticAlpha (t 0) (t 1) (t 2) (t 3) := rfl
@[simp] theorem quarticVal_one {K : Type*} [CommRing K] (t : Fin 4 → K) :
    quarticVal 1 t = quarticBeta (t 0) (t 1) (t 2) (t 3) := rfl
@[simp] theorem quarticVal_two {K : Type*} [CommRing K] (t : Fin 4 → K) :
    quarticVal 2 t = quarticGamma (t 0) (t 1) (t 2) (t 3) := rfl

/-- FT IV §4: the sum of the products over any perfect matching of `{0,1,2,3}` equals the
partially symmetric value indexed by the matching: `tᵢtⱼ + tₖtₗ = α, β or γ`. -/
theorem quarticPairingSum {K : Type*} [CommRing K] (t : Fin 4 → K) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    t i * t j + t k * t l = quarticVal (quarticPairingIdx i j) t := by
  fin_cases i <;> fin_cases j <;>
    rcases fin4_cases4 k with rfl|rfl|rfl|rfl <;>
    rcases fin4_cases4 l with rfl|rfl|rfl|rfl <;>
    simp_all [quarticVal, quarticPairingIdx, quarticAlpha, quarticBeta, quarticGamma] <;>
    ring

/-- FT IV §4 (key lemma): relabelling the entries of `t` by `σ ∈ S₄` permutes the three
partially symmetric values `α, β, γ` according to the slot permutation `quarticPsi σ`:
`quarticVal k (t ∘ σ) = quarticVal (quarticPsi σ k) t`. -/
theorem quarticPermVal {K : Type*} [CommRing K] (σ : Equiv.Perm (Fin 4)) (t : Fin 4 → K)
    (k : Fin 3) : quarticVal k (fun i => t (σ i)) = quarticVal (quarticPsi σ k) t := by
  have hσ : ∀ i j : Fin 4, i ≠ j → σ i ≠ σ j := fun i j h hc => h (Equiv.injective σ hc)
  rcases fin3_cases3 k with rfl|rfl|rfl
  · calc quarticVal 0 (fun i => t (σ i))
      = t (σ 0) * t (σ 1) + t (σ 2) * t (σ 3) := rfl
    _ = quarticVal (quarticPairingIdx (σ 0) (σ 1)) t :=
      quarticPairingSum t (σ 0) (σ 1) (σ 2) (σ 3) (hσ 0 1 (by decide)) (hσ 0 2 (by decide))
        (hσ 0 3 (by decide)) (hσ 1 2 (by decide)) (hσ 1 3 (by decide)) (hσ 2 3 (by decide))
    _ = quarticVal (quarticPsi σ 0) t := rfl
  · calc quarticVal 1 (fun i => t (σ i))
      = t (σ 0) * t (σ 2) + t (σ 1) * t (σ 3) := rfl
    _ = quarticVal (quarticPairingIdx (σ 0) (σ 2)) t :=
      quarticPairingSum t (σ 0) (σ 2) (σ 1) (σ 3) (hσ 0 2 (by decide)) (hσ 0 1 (by decide))
        (hσ 0 3 (by decide)) (hσ 2 1 (by decide)) (hσ 2 3 (by decide)) (hσ 1 3 (by decide))
    _ = quarticVal (quarticPsi σ 1) t := rfl
  · calc quarticVal 2 (fun i => t (σ i))
      = t (σ 0) * t (σ 3) + t (σ 1) * t (σ 2) := rfl
    _ = quarticVal (quarticPairingIdx (σ 0) (σ 3)) t :=
      quarticPairingSum t (σ 0) (σ 3) (σ 1) (σ 2) (hσ 0 3 (by decide)) (hσ 0 1 (by decide))
        (hσ 0 2 (by decide)) (hσ 3 1 (by decide)) (hσ 3 2 (by decide)) (hσ 1 2 (by decide))
    _ = quarticVal (quarticPsi σ 2) t := rfl

/-- FT IV §4: for a tuple with pairwise distinct entries, the three partially symmetric
values `α, β, γ` are pairwise distinct (FT: `α − β = (a₁−a₄)(a₂−a₃)` etc.). -/
theorem quarticVal_injective {K : Type*} [CommRing K] {t : Fin 4 → K} [IsDomain K]
    (ht : Function.Injective t) : Function.Injective (fun k : Fin 3 => quarticVal k t) := by
  have h03 : t 0 ≠ t 3 := fun hc => absurd (ht hc) (by decide)
  have h12 : t 1 ≠ t 2 := fun hc => absurd (ht hc) (by decide)
  have h02 : t 0 ≠ t 2 := fun hc => absurd (ht hc) (by decide)
  have h13 : t 1 ≠ t 3 := fun hc => absurd (ht hc) (by decide)
  have h01 : t 0 ≠ t 1 := fun hc => absurd (ht hc) (by decide)
  have h23 : t 2 ≠ t 3 := fun hc => absurd (ht hc) (by decide)
  intro x y hxy
  rcases fin3_cases3 x with rfl|rfl|rfl <;> rcases fin3_cases3 y with rfl|rfl|rfl
  · rfl
  · exact absurd hxy (quarticAlpha_ne_quarticBeta h03 h12)
  · exact absurd hxy (quarticAlpha_ne_quarticGamma h02 h13)
  · exact absurd hxy (Ne.symm (quarticAlpha_ne_quarticBeta h03 h12))
  · rfl
  · exact absurd hxy (quarticBeta_ne_quarticGamma h01 h23)
  · exact absurd hxy (Ne.symm (quarticAlpha_ne_quarticGamma h02 h13))
  · exact absurd hxy (Ne.symm (quarticBeta_ne_quarticGamma h01 h23))
  · rfl

/-- FT IV §4: the stabilizer of the slot of `α` — order 8, a Sylow 2-subgroup of `S₄`. -/
def quarticStabilizerAlpha : Subgroup (Equiv.Perm (Fin 4)) :=
  @MulAction.stabilizer (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 0

/-- FT IV §4: the stabilizer of the slot of `β` — order 8, a Sylow 2-subgroup of `S₄`
(FT: it is `⟨(1234), (13)⟩`). -/
def quarticStabilizerBeta : Subgroup (Equiv.Perm (Fin 4)) :=
  @MulAction.stabilizer (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 1

/-- FT IV §4: the stabilizer of the slot of `γ` — order 8, a Sylow 2-subgroup of `S₄`. -/
def quarticStabilizerGamma : Subgroup (Equiv.Perm (Fin 4)) :=
  @MulAction.stabilizer (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 2

/-- FT IV §4: membership in a slot stabilizer agrees with fixing the corresponding
partially symmetric value (for a tuple of pairwise distinct entries). -/
theorem mem_quarticStabilizer_iff {K : Type*} [CommRing K] {t : Fin 4 → K} [IsDomain K]
    (ht : Function.Injective t) (k : Fin 3) (σ : Equiv.Perm (Fin 4)) :
    σ ∈ @MulAction.stabilizer (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction k ↔
      quarticVal k (fun i => t (σ i)) = quarticVal k t := by
  constructor
  · intro h
    have h' : quarticPsi σ k = k :=
      (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction k σ).mp h
    rw [quarticPermVal σ t k, h']
  · intro h
    have h2 : quarticPsi σ k = k := by
      refine quarticVal_injective ht ?_
      show quarticVal (quarticPsi σ k) t = quarticVal k t
      rw [← quarticPermVal σ t k]; exact h
    exact (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction k
      σ).mpr h2

theorem quarticPsi_swap12_one : quarticPsi (Equiv.swap 1 2) 1 = 0 := by
  show quarticPairingIdx (Equiv.swap 1 2 0) (Equiv.swap 1 2 2) = 0
  rw [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 1 by decide)
    (show (0 : Fin 4) ≠ 2 by decide), Equiv.swap_apply_right, quarticPairingIdx_01]

theorem quarticPsi_swap01_one : quarticPsi (Equiv.swap 0 1) 1 = 2 := by
  show quarticPairingIdx (Equiv.swap 0 1 0) (Equiv.swap 0 1 2) = 2
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 4) ≠ 0 by decide)
    (show (2 : Fin 4) ≠ 1 by decide), quarticPairingIdx_12]

theorem quarticPsi_swap12_zero : quarticPsi (Equiv.swap 1 2) 0 = 1 := by
  show quarticPairingIdx (Equiv.swap 1 2 0) (Equiv.swap 1 2 1) = 1
  rw [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 1 by decide)
    (show (0 : Fin 4) ≠ 2 by decide), Equiv.swap_apply_left, quarticPairingIdx_02]

theorem quarticPsi_swap02_zero : quarticPsi (Equiv.swap 0 2) 0 = 2 := by
  show quarticPairingIdx (Equiv.swap 0 2 0) (Equiv.swap 0 2 1) = 2
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 4) ≠ 0 by decide)
    (show (1 : Fin 4) ≠ 2 by decide), quarticPairingIdx_21]

theorem quarticPsi_swap01_two : quarticPsi (Equiv.swap 0 1) 2 = 1 := by
  show quarticPairingIdx (Equiv.swap 0 1 0) (Equiv.swap 0 1 3) = 1
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (show (3 : Fin 4) ≠ 0 by decide)
    (show (3 : Fin 4) ≠ 1 by decide), quarticPairingIdx_13]

theorem quarticPsi_swap02_two : quarticPsi (Equiv.swap 0 2) 2 = 0 := by
  show quarticPairingIdx (Equiv.swap 0 2 0) (Equiv.swap 0 2 3) = 0
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (show (3 : Fin 4) ≠ 0 by decide)
    (show (3 : Fin 4) ≠ 2 by decide), quarticPairingIdx_23]

theorem quarticPsi_swap23_one : quarticPsi (Equiv.swap 2 3) 1 = 2 := by
  show quarticPairingIdx (Equiv.swap 2 3 0) (Equiv.swap 2 3 2) = 2
  rw [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 2 by decide)
    (show (0 : Fin 4) ≠ 3 by decide), Equiv.swap_apply_left, quarticPairingIdx_03]

theorem quarticPsi_swap23_two : quarticPsi (Equiv.swap 2 3) 2 = 1 := by
  show quarticPairingIdx (Equiv.swap 2 3 0) (Equiv.swap 2 3 3) = 1
  rw [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 2 by decide)
    (show (0 : Fin 4) ≠ 3 by decide), Equiv.swap_apply_right, quarticPairingIdx_02]

attribute [local instance] quarticSlotAction

/-- FT IV §4: the orbit of each slot under `S₄` is all of `{α, β, γ}`. -/
theorem quarticOrbitAlpha_univ :
    MulAction.orbit (Equiv.Perm (Fin 4)) (0 : Fin 3) = Set.univ := by
  ext y
  rw [MulAction.mem_orbit_iff]
  rcases fin3_cases3 y with rfl|rfl|rfl
  · constructor
    · intro _; trivial
    · intro _; exact ⟨1, rfl⟩
  · constructor
    · intro _; trivial
    · intro _; exact ⟨Equiv.swap 1 2, quarticPsi_swap12_zero⟩
  · constructor
    · intro _; trivial
    · intro _; exact ⟨Equiv.swap 0 2, quarticPsi_swap02_zero⟩

theorem quarticOrbitBeta_univ :
    MulAction.orbit (Equiv.Perm (Fin 4)) (1 : Fin 3) = Set.univ := by
  ext y
  rw [MulAction.mem_orbit_iff]
  rcases fin3_cases3 y with rfl|rfl|rfl
  · constructor
    · intro _; trivial
    · intro _; exact ⟨Equiv.swap 1 2, quarticPsi_swap12_one⟩
  · constructor
    · intro _; trivial
    · intro _; exact ⟨1, rfl⟩
  · constructor
    · intro _; trivial
    · intro _; exact ⟨Equiv.swap 0 1, quarticPsi_swap01_one⟩

theorem quarticOrbitGamma_univ :
    MulAction.orbit (Equiv.Perm (Fin 4)) (2 : Fin 3) = Set.univ := by
  ext y
  rw [MulAction.mem_orbit_iff]
  rcases fin3_cases3 y with rfl|rfl|rfl
  · constructor
    · intro _; trivial
    · intro _; exact ⟨Equiv.swap 0 2, quarticPsi_swap02_two⟩
  · constructor
    · intro _; trivial
    · intro _; exact ⟨Equiv.swap 0 1, quarticPsi_swap01_two⟩
  · constructor
    · intro _; trivial
    · intro _; exact ⟨1, rfl⟩

/-- FT IV §4: the stabilizer of β has order 8 (orbit–stabilizer). -/
theorem quarticStabilizerBeta_card : Nat.card ↥quarticStabilizerBeta = 8 := by
  have he := MulAction.orbitProdStabilizerEquivGroup (α := Equiv.Perm (Fin 4)) (1 : Fin 3)
  have hc : Nat.card (↥(MulAction.orbit (Equiv.Perm (Fin 4)) (1 : Fin 3))
      × ↥quarticStabilizerBeta) = Nat.card (Equiv.Perm (Fin 4)) := Nat.card_congr he
  rw [Nat.card_prod] at hc
  have h3 : Nat.card ↥(MulAction.orbit (Equiv.Perm (Fin 4)) (1 : Fin 3)) = 3 := by
    rw [quarticOrbitBeta_univ]; simp
  rw [h3] at hc
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num
  omega

/-- FT IV §4: the stabilizer of α has order 8. -/
theorem quarticStabilizerAlpha_card : Nat.card ↥quarticStabilizerAlpha = 8 := by
  have he := MulAction.orbitProdStabilizerEquivGroup (α := Equiv.Perm (Fin 4)) (0 : Fin 3)
  have hc : Nat.card (↥(MulAction.orbit (Equiv.Perm (Fin 4)) (0 : Fin 3))
      × ↥quarticStabilizerAlpha) = Nat.card (Equiv.Perm (Fin 4)) := Nat.card_congr he
  rw [Nat.card_prod] at hc
  have h3 : Nat.card ↥(MulAction.orbit (Equiv.Perm (Fin 4)) (0 : Fin 3)) = 3 := by
    rw [quarticOrbitAlpha_univ]; simp
  rw [h3] at hc
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num
  omega

/-- FT IV §4: the stabilizer of γ has order 8. -/
theorem quarticStabilizerGamma_card : Nat.card ↥quarticStabilizerGamma = 8 := by
  have he := MulAction.orbitProdStabilizerEquivGroup (α := Equiv.Perm (Fin 4)) (2 : Fin 3)
  have hc : Nat.card (↥(MulAction.orbit (Equiv.Perm (Fin 4)) (2 : Fin 3))
      × ↥quarticStabilizerGamma) = Nat.card (Equiv.Perm (Fin 4)) := Nat.card_congr he
  rw [Nat.card_prod] at hc
  have h3 : Nat.card ↥(MulAction.orbit (Equiv.Perm (Fin 4)) (2 : Fin 3)) = 3 := by
    rw [quarticOrbitGamma_univ]; simp
  rw [h3] at hc
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num
  omega

/-- FT IV §4: the stabilizer of β is a Sylow 2-subgroup of `S₄`. -/
def quarticStabilizerBeta_sylow : Sylow 2 (Equiv.Perm (Fin 4)) :=
  (IsPGroup.of_card (n := 3) (by rw [quarticStabilizerBeta_card]; norm_num)).toSylow (by
    have hci := Subgroup.card_mul_index quarticStabilizerBeta
    rw [quarticStabilizerBeta_card] at hci
    have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num
    omega)

/-- FT IV §4: the stabilizer of α is a Sylow 2-subgroup of `S₄`. -/
def quarticStabilizerAlpha_sylow : Sylow 2 (Equiv.Perm (Fin 4)) :=
  (IsPGroup.of_card (n := 3) (by rw [quarticStabilizerAlpha_card]; norm_num)).toSylow (by
    have hci := Subgroup.card_mul_index quarticStabilizerAlpha
    rw [quarticStabilizerAlpha_card] at hci
    have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num
    omega)

/-- FT IV §4: the stabilizer of γ is a Sylow 2-subgroup of `S₄`. -/
def quarticStabilizerGamma_sylow : Sylow 2 (Equiv.Perm (Fin 4)) :=
  (IsPGroup.of_card (n := 3) (by rw [quarticStabilizerGamma_card]; norm_num)).toSylow (by
    have hci := Subgroup.card_mul_index quarticStabilizerGamma
    rw [quarticStabilizerGamma_card] at hci
    have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num
    omega)

/-- FT IV §4: the pointwise fixer of the three partially symmetric values — the kernel of
the slot-permutation homomorphism `S₄ → S₃`. -/
def quarticFixer : Subgroup (Equiv.Perm (Fin 4)) := MonoidHom.ker quarticSlotHom

theorem quarticPsi_gen01 (k : Fin 3) : quarticPsi quarticKleinGen01 k = k := by
  rcases fin3_cases3 k with rfl|rfl|rfl
  · show quarticPairingIdx (quarticKleinGen01 0) (quarticKleinGen01 1) = 0
    simp [quarticPairingIdx_10]
  · show quarticPairingIdx (quarticKleinGen01 0) (quarticKleinGen01 2) = 1
    simp [quarticPairingIdx_13]
  · show quarticPairingIdx (quarticKleinGen01 0) (quarticKleinGen01 3) = 2
    simp [quarticPairingIdx_12]

theorem quarticPsi_gen02 (k : Fin 3) : quarticPsi quarticKleinGen02 k = k := by
  rcases fin3_cases3 k with rfl|rfl|rfl
  · show quarticPairingIdx (quarticKleinGen02 0) (quarticKleinGen02 1) = 0
    simp [quarticPairingIdx_23]
  · show quarticPairingIdx (quarticKleinGen02 0) (quarticKleinGen02 2) = 1
    simp [quarticPairingIdx_20]
  · show quarticPairingIdx (quarticKleinGen02 0) (quarticKleinGen02 3) = 2
    simp [quarticPairingIdx_21]

theorem quarticPsi_gen03 (k : Fin 3) : quarticPsi quarticKleinGen03 k = k := by
  rcases fin3_cases3 k with rfl|rfl|rfl
  · show quarticPairingIdx (quarticKleinGen03 0) (quarticKleinGen03 1) = 0
    simp [quarticPairingIdx_32]
  · show quarticPairingIdx (quarticKleinGen03 0) (quarticKleinGen03 2) = 1
    simp [quarticPairingIdx_31]
  · show quarticPairingIdx (quarticKleinGen03 0) (quarticKleinGen03 3) = 2
    simp [quarticPairingIdx_30]

/-- FT IV §4: every element of `V` fixes all three pairings, hence all of `α, β, γ`. -/
theorem quarticKlein_le_quarticFixer : quarticKlein ≤ quarticFixer := by
  intro σ hσ
  rcases (quarticKlein_eq σ).mp hσ with rfl|rfl|rfl|rfl
  · exact MonoidHom.mem_ker.mpr (map_one quarticSlotHom)
  · exact MonoidHom.mem_ker.mpr (Equiv.ext fun k => quarticPsi_gen01 k)
  · exact MonoidHom.mem_ker.mpr (Equiv.ext fun k => quarticPsi_gen02 k)
  · exact MonoidHom.mem_ker.mpr (Equiv.ext fun k => quarticPsi_gen03 k)

/-- FT IV §4: conversely, a permutation preserving all three pairings is a double
transposition (FT: each Sylow 2-subgroup fixes exactly one of `α, β, γ`, and their
intersection is `V`). -/
theorem quarticFixer_le_quarticKlein : quarticFixer ≤ quarticKlein := by
  intro σ hσ
  have hp : ∀ k : Fin 3, quarticPsi σ k = k :=
    fun k => DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) k
  have hA : quarticPairingIdx (σ 0) (σ 1) = 0 := hp 0
  have hB : quarticPairingIdx (σ 0) (σ 2) = 1 := hp 1
  have hC : quarticPairingIdx (σ 0) (σ 3) = 2 := hp 2
  rcases fin4_cases4 (σ 0) with h0|h0|h0|h0
  · rw [h0] at hA hB hC
    have h1 : σ 1 = 1 := by
      rcases quarticPairingIdx_eq_zero.mp hA with ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩
      · exact h1
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have h2 : σ 2 = 2 := by
      rcases quarticPairingIdx_eq_one.mp hB with ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
      · exact h2
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have h3 : σ 3 = 3 := by
      rcases quarticPairingIdx_eq_two.mp hC with hc | ⟨h, h3⟩ | ⟨h, h3⟩ | ⟨h, h3⟩ |
          ⟨h, h3⟩  -- FIX: first disjunct σ 0 = σ 3
      · exact absurd (Equiv.injective σ hc).symm (by decide)
      · exact h3
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    exact (quarticKlein_eq σ).mpr (Or.inl (Equiv.ext fun i => by
      fin_cases i <;> simp [h0, h1, h2, h3]))
  · rw [h0] at hA hB hC
    have h1 : σ 1 = 0 := by
      rcases quarticPairingIdx_eq_zero.mp hA with ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩
      · exact absurd h (by decide)
      · exact h1
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have h2 : σ 2 = 3 := by
      rcases quarticPairingIdx_eq_one.mp hB with ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h2
      · exact absurd h (by decide)
    have h3 : σ 3 = 2 := by
      rcases quarticPairingIdx_eq_two.mp hC with hc | ⟨h, h3⟩ | ⟨h, h3⟩ | ⟨h, h3⟩ |
          ⟨h, h3⟩  -- FIX
      · exact absurd (Equiv.injective σ hc).symm (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h3
      · exact absurd h (by decide)
    exact (quarticKlein_eq σ).mpr (Or.inr (Or.inl (Equiv.ext fun i => by
      fin_cases i <;> simp [h0, h1, h2, h3])))
  · rw [h0] at hA hB hC
    have h1 : σ 1 = 3 := by
      rcases quarticPairingIdx_eq_zero.mp hA with ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h1
      · exact absurd h (by decide)
    have h2 : σ 2 = 0 := by
      rcases quarticPairingIdx_eq_one.mp hB with ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
      · exact absurd h (by decide)
      · exact h2
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have h3 : σ 3 = 1 := by
      rcases quarticPairingIdx_eq_two.mp hC with hc | ⟨h, h3⟩ | ⟨h, h3⟩ | ⟨h, h3⟩ |
          ⟨h, h3⟩  -- FIX
      · exact absurd (Equiv.injective σ hc).symm (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h3
    exact (quarticKlein_eq σ).mpr (Or.inr (Or.inr (Or.inl (Equiv.ext fun i => by
      fin_cases i <;> simp [h0, h1, h2, h3]))))
  · rw [h0] at hA hB hC
    have h1 : σ 1 = 2 := by
      rcases quarticPairingIdx_eq_zero.mp hA with ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h1
    have h2 : σ 2 = 1 := by
      rcases quarticPairingIdx_eq_one.mp hB with ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h2
    have h3 : σ 3 = 0 := by
      rcases quarticPairingIdx_eq_two.mp hC with hc | ⟨h, h3⟩ | ⟨h, h3⟩ | ⟨h, h3⟩ |
          ⟨h, h3⟩  -- FIX
      · exact absurd (Equiv.injective σ hc).symm (by decide)
      · exact h3
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    exact (quarticKlein_eq σ).mpr (Or.inr (Or.inr (Or.inr (Equiv.ext fun i => by
      fin_cases i <;> simp [h0, h1, h2, h3]))))

/-- FT IV §4: the pointwise fixer of `{α, β, γ}` is exactly the Klein group `V`. -/
theorem quarticFixer_eq_quarticKlein : quarticFixer = quarticKlein :=
  le_antisymm quarticFixer_le_quarticKlein quarticKlein_le_quarticFixer

/-- FT IV §4: a permutation fixes `α`, `β` and `γ` pointwise iff it lies in the kernel of
the slot action (for a tuple of pairwise distinct entries). -/
theorem mem_quarticFixer_iff {K : Type*} [CommRing K] {t : Fin 4 → K} [IsDomain K]
    (ht : Function.Injective t) (σ : Equiv.Perm (Fin 4)) :
    σ ∈ quarticFixer ↔ ∀ k : Fin 3, quarticVal k (fun i => t (σ i)) = quarticVal k t := by
  constructor
  · intro h k
    have h' : quarticPsi σ k = k := DFunLike.congr_fun (MonoidHom.mem_ker.mp h) k
    rw [quarticPermVal σ t k, h']
  · intro h
    have h2 : ∀ k : Fin 3, quarticPsi σ k = k := fun k => by
      refine quarticVal_injective ht ?_
      show quarticVal (quarticPsi σ k) t = quarticVal k t
      rw [← quarticPermVal σ t k]; exact h k
    exact MonoidHom.mem_ker.mpr (Equiv.ext h2)

/-- FT IV §4: every element of `V` fixes `α, β, γ` (for a tuple of pairwise distinct
entries). -/
theorem quarticKlein_fixes_values {K : Type*} [CommRing K] {t : Fin 4 → K} [IsDomain K]
    (ht : Function.Injective t) {σ : Equiv.Perm (Fin 4)} (hσ : σ ∈ quarticKlein) (k : Fin 3) :
    quarticVal k (fun i => t (σ i)) = quarticVal k t :=
  (mem_quarticFixer_iff ht σ).mp (quarticKlein_le_quarticFixer hσ) k

/-- FT IV §4: the pointwise fixer of `{α, β, γ}` is the intersection of the three slot
stabilizers (FT: each Sylow 2-subgroup fixes exactly one of `α, β, γ`, and their
intersection is `V`). -/
theorem quarticFixer_eq_inf :
    quarticFixer = quarticStabilizerAlpha ⊓ quarticStabilizerBeta ⊓ quarticStabilizerGamma := by
  apply le_antisymm
  · intro σ hσ
    have h' : ∀ k : Fin 3, quarticPsi σ k = k :=
      fun k => DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) k
    exact ⟨⟨(@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 0
        σ).mpr (h' 0),
      (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 1
        σ).mpr (h' 1)⟩,
      (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 2
        σ).mpr (h' 2)⟩
  · intro σ hσ
    have h0 : quarticPsi σ 0 = 0 :=
      (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 0
        σ).mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hσ).1).1
    have h1 : quarticPsi σ 1 = 1 :=
      (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 1
        σ).mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hσ).1).2
    have h2 : quarticPsi σ 2 = 2 :=
      (@MulAction.mem_stabilizer_iff (Equiv.Perm (Fin 4)) (Fin 3) _ quarticSlotAction 2
        σ).mp (Subgroup.mem_inf.mp hσ).2
    refine MonoidHom.mem_ker.mpr (Equiv.ext fun k => ?_)
    rcases fin3_cases3 k with rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2

/-- FT IV §4: `S₄` permutes the three partially symmetric values transitively. -/
theorem quarticSlot_transitive (i j : Fin 3) :
    ∃ σ : Equiv.Perm (Fin 4), quarticPsi σ i = j := by
  rcases fin3_cases3 i with rfl|rfl|rfl <;> rcases fin3_cases3 j with rfl|rfl|rfl
  · exact ⟨1, rfl⟩
  · exact ⟨Equiv.swap 1 2, quarticPsi_swap12_zero⟩
  · exact ⟨Equiv.swap 0 2, quarticPsi_swap02_zero⟩
  · exact ⟨Equiv.swap 1 2, quarticPsi_swap12_one⟩
  · exact ⟨1, rfl⟩
  · exact ⟨Equiv.swap 2 3, quarticPsi_swap23_one⟩
  · exact ⟨Equiv.swap 0 2, quarticPsi_swap02_two⟩
  · exact ⟨Equiv.swap 2 3, quarticPsi_swap23_two⟩
  · exact ⟨1, rfl⟩

/-- FT IV §4: transitivity on the values: for slots `k, l` there is a permutation `σ` of
the roots carrying the `k`-th partially symmetric value to the `l`-th. -/
theorem quarticVal_transitive {K : Type*} [CommRing K] (t : Fin 4 → K) (k l : Fin 3) :
    ∃ σ : Equiv.Perm (Fin 4), quarticVal k (fun i => t (σ i)) = quarticVal l t := by
  obtain ⟨σ, hσ⟩ := quarticSlot_transitive k l
  exact ⟨σ, by rw [quarticPermVal σ t k, hσ]⟩

/-- FT IV §4: the resolvent set is exactly the set of the three partially symmetric
values of the tuple. -/
theorem mem_quarticResolventSet_iff_val {K : Type*} [CommRing K] (t : Fin 4 → K) (x : K) :
    x ∈ quarticResolventSet (t 0) (t 1) (t 2) (t 3) ↔ ∃ k : Fin 3, x = quarticVal k t := by
  constructor
  · intro hx
    simp only [quarticResolventSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl|rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨k, rfl⟩
    rcases fin3_cases3 k with rfl|rfl|rfl <;>
      simp [quarticResolventSet, quarticVal_zero, quarticVal_one, quarticVal_two]

/-- FT IV §4: the action of `S₄` on the resolvent set `{α, β, γ}` is transitive. -/
theorem quarticResolventSet_transitive {K : Type*} [CommRing K] (t : Fin 4 → K)
    (x y : K) (hx : x ∈ quarticResolventSet (t 0) (t 1) (t 2) (t 3))
    (hy : y ∈ quarticResolventSet (t 0) (t 1) (t 2) (t 3)) :
    ∃ σ : Equiv.Perm (Fin 4), ∃ k l : Fin 3, x = quarticVal k t ∧ y = quarticVal l t ∧
      quarticVal k (fun i => t (σ i)) = quarticVal l t := by
  obtain ⟨k, hxk⟩ := (mem_quarticResolventSet_iff_val t x).mp hx
  obtain ⟨l, hyl⟩ := (mem_quarticResolventSet_iff_val t y).mp hy
  obtain ⟨σ, hσ⟩ := quarticSlot_transitive k l
  exact ⟨σ, k, l, hxk, hyl, by rw [quarticPermVal σ t k, hσ]⟩

/-! ## FT IV §4 (V/S₄ theory): classification-table implications -/

/-- FT IV §4 (classification table): a subgroup `G ≤ S₄` with `[G : G ∩ V] = 1` (here
phrased as `|G ∩ V| = |G|`) is contained in `V`. -/
theorem quarticTable_index_one {G : Subgroup (Equiv.Perm (Fin 4))}
    (h : Nat.card ↥(G ⊓ quarticKlein) = Nat.card ↥G) : G ≤ quarticKlein := by
  have hEq : G ⊓ quarticKlein = G :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (h ▸ le_refl _)
  rw [← hEq]; exact inf_le_right

/-- FT IV §4 (classification table): a transitive subgroup `G ≤ S₄` with `[G : G ∩ V] = 1`
equals `V` (transitivity forces `4 ∣ |G|`, and `|G| ≤ |V| = 4`). -/
theorem quarticTable_index_one_transitive {G : Subgroup (Equiv.Perm (Fin 4))}
    (h : Nat.card ↥(G ⊓ quarticKlein) = Nat.card ↥G)
    (htrans : ∀ i j : Fin 4, ∃ g ∈ G, g i = j) : G = quarticKlein := by
  have hGV : G ≤ quarticKlein := quarticTable_index_one h
  refine Subgroup.eq_of_le_of_card_ge hGV ?_
  have horb : MulAction.orbit (↥G) (0 : Fin 4) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨g, hgm, hgy⟩ := htrans 0 y
      exact ⟨⟨g, hgm⟩, hgy⟩
  have he := MulAction.orbitProdStabilizerEquivGroup (α := ↥G) (0 : Fin 4)
  have hc : Nat.card (↥(MulAction.orbit (↥G) (0 : Fin 4)) × ↥(MulAction.stabilizer (↥G)
      (0 : Fin 4))) = Nat.card ↥G := Nat.card_congr he
  rw [Nat.card_prod] at hc
  have h4 : Nat.card ↥(MulAction.orbit (↥G) (0 : Fin 4)) = 4 := by
    rw [horb]; simp
  rw [h4] at hc
  have hpos := Nat.card_pos (α := ↥(MulAction.stabilizer (↥G) (0 : Fin 4)))
  have hle : Nat.card ↥quarticKlein ≤ Nat.card ↥G := by
    rw [quarticKlein_card]
    have : 1 ≤ Nat.card ↥(MulAction.stabilizer (↥G) (0 : Fin 4)) := le_of_lt hpos
    omega
  exact hle

end FT
