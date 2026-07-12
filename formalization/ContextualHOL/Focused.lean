import ContextualHOL.ProvesLift

/-!
# PS2 — analytic propositional search: the two-sided LK substrate

CoreSearch0's propositional search calculus.  The search shape is deliberately
**multi-conclusion** (`Δ ⊢ Θ`, `Θ : List Formula`), because primitive classical
`not` cannot move a negated hypothesis across a single-conclusion turnstile.

We do NOT add a falsity constant to M3.  Instead the succedent is interpreted
into M3's single-conclusion `Proves` by right-nested disjunction, and the empty
succedent is given the ⊥-free meaning "the antecedent is absurd" (proves every
well-typed formula). Empty succedents are permitted internal refutation states;
the PS2 falsifier is reifying one as a new formula inside M3.

This module (increment 1) fixes the representation and proves the soundness
direction `analyticSound : FDeriv → denote`. `FDeriv` is the unfocused analytic
LK substrate; cut/MP admissibility, the K/S/CP completeness direction, the
actual focus discipline, and subformula-boundedness follow.
-/

namespace ContextualHOL
namespace Focused

open ContextualHOL

/-- Right-nested disjunction of a nonempty succedent `φ :: Θ`. -/
def rightOr : Formula -> List Formula -> Formula
  | φ, [] => φ
  | φ, ψ :: Θ => Formula.or φ (rightOr ψ Θ)

/-- Well-typedness of every formula in a list over `Γ`. -/
def LiftsAllF (env : Env) (Γ : Ctx) (Θ : List Formula) : Prop :=
  ∀ φ, φ ∈ Θ -> (liftFormula? env Γ φ).isSome = true

theorem LiftsAllF.nil {env : Env} {Γ : Ctx} : LiftsAllF env Γ [] := by
  intro φ h; cases h

theorem LiftsAllF.head {env : Env} {Γ : Ctx} {φ : Formula} {Θ : List Formula}
    (h : LiftsAllF env Γ (φ :: Θ)) : (liftFormula? env Γ φ).isSome = true :=
  h φ (List.mem_cons_self)

theorem LiftsAllF.tail {env : Env} {Γ : Ctx} {φ : Formula} {Θ : List Formula}
    (h : LiftsAllF env Γ (φ :: Θ)) : LiftsAllF env Γ Θ :=
  fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)

theorem LiftsAllF.cons {env : Env} {Γ : Ctx} {φ : Formula} {Θ : List Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hΘ : LiftsAllF env Γ Θ) :
    LiftsAllF env Γ (φ :: Θ) := by
  intro ψ hψ
  rcases List.mem_cons.1 hψ with h | h
  · subst h; exact hφ
  · exact hΘ ψ h

/-- `rightOr φ Θ` is well-typed when `φ` and every member of `Θ` are. -/
theorem liftFormula?_rightOr_isSome {env : Env} {Γ : Ctx} :
    ∀ (φ : Formula) (Θ : List Formula),
      (liftFormula? env Γ φ).isSome = true -> LiftsAllF env Γ Θ ->
      (liftFormula? env Γ (rightOr φ Θ)).isSome = true
  | φ, [], hφ, _ => hφ
  | φ, ψ :: Θ, hφ, hΘ => by
      have hrest : (liftFormula? env Γ (rightOr ψ Θ)).isSome = true :=
        liftFormula?_rightOr_isSome ψ Θ hΘ.head hΘ.tail
      rcases Option.isSome_iff_exists.1 hφ with ⟨ca, hca⟩
      rcases Option.isSome_iff_exists.1 hrest with ⟨cr, hcr⟩
      simp [rightOr, liftFormula?_or, hca, hcr]

/-! ## Well-typedness helpers for the compound connectives -/

theorem liftFormula?_and_isSome {env : Env} {Γ : Ctx} {a b : Formula} :
    (liftFormula? env Γ (Formula.and a b)).isSome =
      ((liftFormula? env Γ a).isSome && (liftFormula? env Γ b).isSome) := by
  rw [liftFormula?_and]; cases liftFormula? env Γ a <;> cases liftFormula? env Γ b <;> rfl

theorem liftFormula?_or_isSome {env : Env} {Γ : Ctx} {a b : Formula} :
    (liftFormula? env Γ (Formula.or a b)).isSome =
      ((liftFormula? env Γ a).isSome && (liftFormula? env Γ b).isSome) := by
  rw [liftFormula?_or]; cases liftFormula? env Γ a <;> cases liftFormula? env Γ b <;> rfl

theorem liftFormula?_not_isSome {env : Env} {Γ : Ctx} {a : Formula} :
    (liftFormula? env Γ (Formula.not a)).isSome = (liftFormula? env Γ a).isSome := by
  rw [liftFormula?_not]; cases liftFormula? env Γ a <;> rfl

theorem liftFormula?_iff_isSome {env : Env} {Γ : Ctx} {a b : Formula} :
    (liftFormula? env Γ (Formula.iff a b)).isSome =
      ((liftFormula? env Γ a).isSome && (liftFormula? env Γ b).isSome) := by
  rw [liftFormula?_iff]; cases liftFormula? env Γ a <;> cases liftFormula? env Γ b <;> rfl

/-! ## The propositional fragment `ProvesProp`

    Full `Proves` carries quantifier/context rules (`allIntro`, `ctxWeaken`, …)
    whose freshness obligations over the assumption list make arbitrary
    assumption weakening invalid (PS1 structural finding).  PS2's completeness
    target is therefore the propositional fragment: the Hilbert base with no
    quantifier or context rules.  Assumption-monotonicity holds here, and every
    rule injects into `Proves` for the final Core replay. -/

inductive ProvesProp (env : Env) : Ctx -> List Formula -> Formula -> Prop where
  | hyp {Γ Δ φ} : φ ∈ Δ -> ProvesProp env Γ Δ φ
  | impIntro {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      ProvesProp env Γ (φ :: Δ) ψ -> ProvesProp env Γ Δ (Formula.imp φ ψ)
  | mp {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp φ ψ) -> ProvesProp env Γ Δ φ ->
      ProvesProp env Γ Δ ψ
  | axK {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp φ (Formula.imp ψ φ))
  | axS {Γ Δ φ ψ χ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true -> (liftFormula? env Γ χ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.imp φ (Formula.imp ψ χ))
        (Formula.imp (Formula.imp φ ψ) (Formula.imp φ χ)))
  | axCP {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.imp (Formula.not ψ) (Formula.not φ))
        (Formula.imp φ ψ))
  | axAndL {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.and φ ψ) φ)
  | axAndR {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.and φ ψ) ψ)
  | axAndI {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp φ (Formula.imp ψ (Formula.and φ ψ)))
  | axOrL {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp φ (Formula.or φ ψ))
  | axOrR {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp ψ (Formula.or φ ψ))
  | axOrE {Γ Δ φ ψ χ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true -> (liftFormula? env Γ χ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.imp φ χ)
        (Formula.imp (Formula.imp ψ χ) (Formula.imp (Formula.or φ ψ) χ)))
  | axIffI {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.imp φ ψ)
        (Formula.imp (Formula.imp ψ φ) (Formula.iff φ ψ)))
  | axIffL {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.iff φ ψ) (Formula.imp φ ψ))
  | axIffR {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      ProvesProp env Γ Δ (Formula.imp (Formula.iff φ ψ) (Formula.imp ψ φ))

/-- Every propositional rule is a `Proves` rule: the fragment injects into the
    full calculus for Core replay. -/
theorem ProvesProp.toProves {env : Env} {Γ : Ctx} {Δ : List Formula} {φ : Formula}
    (h : ProvesProp env Γ Δ φ) : Proves env Γ Δ φ := by
  induction h with
  | hyp hmem => exact Proves.hyp hmem
  | impIntro hwt _ ih => exact Proves.impIntro hwt ih
  | mp hwt _ _ ih1 ih2 => exact Proves.mp hwt ih1 ih2
  | axK h1 h2 => exact Proves.axK h1 h2
  | axS h1 h2 h3 => exact Proves.axS h1 h2 h3
  | axCP h1 h2 => exact Proves.axCP h1 h2
  | axAndL h1 h2 => exact Proves.axAndL h1 h2
  | axAndR h1 h2 => exact Proves.axAndR h1 h2
  | axAndI h1 h2 => exact Proves.axAndI h1 h2
  | axOrL h1 h2 => exact Proves.axOrL h1 h2
  | axOrR h1 h2 => exact Proves.axOrR h1 h2
  | axOrE h1 h2 h3 => exact Proves.axOrE h1 h2 h3
  | axIffI h1 h2 => exact Proves.axIffI h1 h2
  | axIffL h1 h2 => exact Proves.axIffL h1 h2
  | axIffR h1 h2 => exact Proves.axIffR h1 h2

/-! ## Reified certificates (`PPTerm`)

    `PPTerm` is a `Type`-valued mirror of `ProvesProp` with the identical fifteen
    constructors.  It exists so the *intermediate* formulas and the size of a
    produced certificate — invisible in the erased `Prop` — become first-class
    data.  This is what lets us adjudicate the replay-side falsifiers: that the
    classical compile-back stays within a fixed finite template family
    (`replayClosure`) and grows only by a bounded per-rule amount (`replaySize`).
    `PPTerm.toProvesProp` erases a certificate back to the `Prop` judgement, so
    the search layer stays in `Prop` and soundness is preserved. -/

inductive PPTerm (env : Env) : Ctx -> List Formula -> Formula -> Type where
  | hyp {Γ Δ φ} : φ ∈ Δ -> PPTerm env Γ Δ φ
  | impIntro {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      PPTerm env Γ (φ :: Δ) ψ -> PPTerm env Γ Δ (Formula.imp φ ψ)
  | mp {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp φ ψ) -> PPTerm env Γ Δ φ ->
      PPTerm env Γ Δ ψ
  | axK {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp φ (Formula.imp ψ φ))
  | axS {Γ Δ φ ψ χ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true -> (liftFormula? env Γ χ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.imp φ (Formula.imp ψ χ))
        (Formula.imp (Formula.imp φ ψ) (Formula.imp φ χ)))
  | axCP {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.imp (Formula.not ψ) (Formula.not φ))
        (Formula.imp φ ψ))
  | axAndL {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.and φ ψ) φ)
  | axAndR {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.and φ ψ) ψ)
  | axAndI {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp φ (Formula.imp ψ (Formula.and φ ψ)))
  | axOrL {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp φ (Formula.or φ ψ))
  | axOrR {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp ψ (Formula.or φ ψ))
  | axOrE {Γ Δ φ ψ χ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true -> (liftFormula? env Γ χ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.imp φ χ)
        (Formula.imp (Formula.imp ψ χ) (Formula.imp (Formula.or φ ψ) χ)))
  | axIffI {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.imp φ ψ)
        (Formula.imp (Formula.imp ψ φ) (Formula.iff φ ψ)))
  | axIffL {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.iff φ ψ) (Formula.imp φ ψ))
  | axIffR {Γ Δ φ ψ} : (liftFormula? env Γ φ).isSome = true ->
      (liftFormula? env Γ ψ).isSome = true ->
      PPTerm env Γ Δ (Formula.imp (Formula.iff φ ψ) (Formula.imp ψ φ))

/-- Erase a reified certificate to the `Prop` judgement.  Soundness of a
    `PPTerm` is exactly `ProvesProp` of its conclusion, so the search layer never
    has to leave `Prop`. -/
def PPTerm.toProvesProp {env : Env} : {Γ : Ctx} -> {Δ : List Formula} -> {φ : Formula} ->
    PPTerm env Γ Δ φ -> ProvesProp env Γ Δ φ
  | _, _, _, .hyp hmem => ProvesProp.hyp hmem
  | _, _, _, .impIntro hwt t => ProvesProp.impIntro hwt t.toProvesProp
  | _, _, _, .mp hwt t u => ProvesProp.mp hwt t.toProvesProp u.toProvesProp
  | _, _, _, .axK h1 h2 => ProvesProp.axK h1 h2
  | _, _, _, .axS h1 h2 h3 => ProvesProp.axS h1 h2 h3
  | _, _, _, .axCP h1 h2 => ProvesProp.axCP h1 h2
  | _, _, _, .axAndL h1 h2 => ProvesProp.axAndL h1 h2
  | _, _, _, .axAndR h1 h2 => ProvesProp.axAndR h1 h2
  | _, _, _, .axAndI h1 h2 => ProvesProp.axAndI h1 h2
  | _, _, _, .axOrL h1 h2 => ProvesProp.axOrL h1 h2
  | _, _, _, .axOrR h1 h2 => ProvesProp.axOrR h1 h2
  | _, _, _, .axOrE h1 h2 h3 => ProvesProp.axOrE h1 h2 h3
  | _, _, _, .axIffI h1 h2 => ProvesProp.axIffI h1 h2
  | _, _, _, .axIffL h1 h2 => ProvesProp.axIffL h1 h2
  | _, _, _, .axIffR h1 h2 => ProvesProp.axIffR h1 h2

/-- Certificate size: the number of rule nodes in the reified derivation.  Only
    `impIntro` and `mp` have premises; every axiom node is a leaf. -/
def PPTerm.size {env : Env} : {Γ : Ctx} -> {Δ : List Formula} -> {φ : Formula} ->
    PPTerm env Γ Δ φ -> Nat
  | _, _, _, .hyp _ => 1
  | _, _, _, .impIntro _ t => t.size + 1
  | _, _, _, .mp _ t u => t.size + u.size + 1
  | _, _, _, .axK _ _ => 1
  | _, _, _, .axS _ _ _ => 1
  | _, _, _, .axCP _ _ => 1
  | _, _, _, .axAndL _ _ => 1
  | _, _, _, .axAndR _ _ => 1
  | _, _, _, .axAndI _ _ => 1
  | _, _, _, .axOrL _ _ => 1
  | _, _, _, .axOrR _ _ => 1
  | _, _, _, .axOrE _ _ _ => 1
  | _, _, _, .axIffI _ _ => 1
  | _, _, _, .axIffL _ _ => 1
  | _, _, _, .axIffR _ _ => 1

/-! ## Derived propositional meta-theory over the Hilbert base

    All lemmas are parametric in the assumption list `Δ`; they package the K/S,
    ∨/∧, and classical contraposition axioms into the natural-deduction shapes
    the focused soundness proof consumes. -/

variable {env : Env} {Γ : Ctx} {Δ : List Formula}

/-- `φ ⇒ φ`, derived from K and S. -/
theorem pImpId {φ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true) :
    ProvesProp env Γ Δ (Formula.imp φ φ) := by
  have hkφ : (liftFormula? env Γ (Formula.imp φ φ)).isSome = true := by
    simp [liftFormula?_imp_isSome, hφ]
  have hS := ProvesProp.axS (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := Formula.imp φ φ)
    (χ := φ) hφ hkφ hφ
  have hK1 := ProvesProp.axK (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := Formula.imp φ φ) hφ hkφ
  have hK2 := ProvesProp.axK (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := φ) hφ hφ
  have hwt2 : (liftFormula? env Γ (Formula.imp φ (Formula.imp φ φ))).isSome = true := by
    simp [liftFormula?_imp_isSome, hφ]
  exact ProvesProp.mp hwt2
    (ProvesProp.mp (by simp [liftFormula?_imp_isSome, hφ, hkφ]) hS hK1) hK2

/-- Left disjunction introduction: `φ ⊢ φ ∨ ψ`. -/
theorem pOrInl {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : ProvesProp env Γ Δ φ) :
    ProvesProp env Γ Δ (Formula.or φ ψ) :=
  ProvesProp.mp hφ (ProvesProp.axOrL hφ hψ) h

/-- Right disjunction introduction: `ψ ⊢ φ ∨ ψ`. -/
theorem pOrInr {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : ProvesProp env Γ Δ ψ) :
    ProvesProp env Γ Δ (Formula.or φ ψ) :=
  ProvesProp.mp hψ (ProvesProp.axOrR hφ hψ) h

/-- Disjunction elimination into any goal. -/
theorem pOrElim {φ ψ χ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hχ : (liftFormula? env Γ χ).isSome = true)
    (hor : ProvesProp env Γ Δ (Formula.or φ ψ))
    (hl : ProvesProp env Γ Δ (Formula.imp φ χ))
    (hr : ProvesProp env Γ Δ (Formula.imp ψ χ)) :
    ProvesProp env Γ Δ χ := by
  have hlφχ : (liftFormula? env Γ (Formula.imp φ χ)).isSome = true := by
    simp [liftFormula?_imp_isSome, hφ, hχ]
  have hlψχ : (liftFormula? env Γ (Formula.imp ψ χ)).isSome = true := by
    simp [liftFormula?_imp_isSome, hψ, hχ]
  have horψ : (liftFormula? env Γ (Formula.or φ ψ)).isSome = true := by
    simp [liftFormula?_or_isSome, hφ, hψ]
  exact ProvesProp.mp horψ
    (ProvesProp.mp hlψχ (ProvesProp.mp hlφχ (ProvesProp.axOrE hφ hψ hχ) hl) hr) hor

/-- Assumption-list monotonicity: valid in the propositional fragment because it
    has no freshness-bearing quantifier/context rules.  `impIntro` stays in range
    since `φ :: Δ ⊆ φ :: Δ'`. -/
theorem pMono {Δ Δ' : List Formula} (hsub : ∀ x, x ∈ Δ -> x ∈ Δ')
    {φ : Formula} (h : ProvesProp env Γ Δ φ) : ProvesProp env Γ Δ' φ := by
  induction h generalizing Δ' with
  | hyp hmem => exact ProvesProp.hyp (hsub _ hmem)
  | impIntro hwt _ ih =>
      exact ProvesProp.impIntro hwt (ih (by
        intro x hx
        rcases List.mem_cons.1 hx with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub _ h)))
  | mp hwt _ _ ih1 ih2 => exact ProvesProp.mp hwt (ih1 hsub) (ih2 hsub)
  | axK h1 h2 => exact ProvesProp.axK h1 h2
  | axS h1 h2 h3 => exact ProvesProp.axS h1 h2 h3
  | axCP h1 h2 => exact ProvesProp.axCP h1 h2
  | axAndL h1 h2 => exact ProvesProp.axAndL h1 h2
  | axAndR h1 h2 => exact ProvesProp.axAndR h1 h2
  | axAndI h1 h2 => exact ProvesProp.axAndI h1 h2
  | axOrL h1 h2 => exact ProvesProp.axOrL h1 h2
  | axOrR h1 h2 => exact ProvesProp.axOrR h1 h2
  | axOrE h1 h2 h3 => exact ProvesProp.axOrE h1 h2 h3
  | axIffI h1 h2 => exact ProvesProp.axIffI h1 h2
  | axIffL h1 h2 => exact ProvesProp.axIffL h1 h2
  | axIffR h1 h2 => exact ProvesProp.axIffR h1 h2

/-! ## Well-typedness builders for the compound connectives -/

theorem wtImp {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) :
    (liftFormula? env Γ (Formula.imp a b)).isSome = true := by
  simp [liftFormula?_imp_isSome, ha, hb]

theorem wtOr {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) :
    (liftFormula? env Γ (Formula.or a b)).isSome = true := by
  simp [liftFormula?_or_isSome, ha, hb]

theorem wtAnd {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) :
    (liftFormula? env Γ (Formula.and a b)).isSome = true := by
  simp [liftFormula?_and_isSome, ha, hb]

theorem wtNot {a : Formula} (ha : (liftFormula? env Γ a).isSome = true) :
    (liftFormula? env Γ (Formula.not a)).isSome = true := by
  rw [liftFormula?_not_isSome]; exact ha

theorem wtIff {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) :
    (liftFormula? env Γ (Formula.iff a b)).isSome = true := by
  simp [liftFormula?_iff_isSome, ha, hb]

/-! ## Implicational combinators over the Hilbert base -/

/-- Weakening a proof into an implication: `⊢ b` gives `⊢ a → b`. -/
theorem pImpK {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (h : ProvesProp env Γ Δ b) :
    ProvesProp env Γ Δ (Formula.imp a b) :=
  ProvesProp.mp hb (ProvesProp.axK hb ha) h

/-- Hypothetical syllogism: `⊢ a → b` and `⊢ b → c` give `⊢ a → c`. -/
theorem pImpTrans {a b c : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (hc : (liftFormula? env Γ c).isSome = true)
    (hab : ProvesProp env Γ Δ (Formula.imp a b))
    (hbc : ProvesProp env Γ Δ (Formula.imp b c)) :
    ProvesProp env Γ Δ (Formula.imp a c) := by
  have h1 : ProvesProp env Γ Δ (Formula.imp a (Formula.imp b c)) :=
    pImpK ha (wtImp hb hc) hbc
  have hS := ProvesProp.axS (Δ := Δ) (φ := a) (ψ := b) (χ := c) ha hb hc
  exact ProvesProp.mp (wtImp ha hb) (ProvesProp.mp (wtImp ha (wtImp hb hc)) hS h1) hab

/-! ## The classical negation kernel

    Everything classical is derived from `axCP` `(¬ψ→¬φ)→(φ→ψ)` and the
    deduction theorem (`impIntro`).  The base case is `pCM` (consequentia
    mirabilis), whose derivation nests an `axS` contraction over an `axCP`
    instance — this is what breaks the DNE/DNI mutual circularity.  From `pCM`
    the double-negation and reductio rules follow directly. -/

/-- Ex falso for implication: `⊢ ¬a → (a → b)`.  (No double negation needed.) -/
theorem pEF {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) :
    ProvesProp env Γ Δ (Formula.imp (Formula.not a) (Formula.imp a b)) := by
  have hna := wtNot ha
  have hnb := wtNot hb
  have hbctx : ProvesProp env Γ (a :: Formula.not a :: Δ) b := by
    have hnahyp : ProvesProp env Γ (a :: Formula.not a :: Δ) (Formula.not a) :=
      ProvesProp.hyp (by simp)
    have hahyp : ProvesProp env Γ (a :: Formula.not a :: Δ) a :=
      ProvesProp.hyp (by simp)
    have hc : ProvesProp env Γ (a :: Formula.not a :: Δ)
        (Formula.imp (Formula.not b) (Formula.not a)) := pImpK hnb hna hnahyp
    have himp : ProvesProp env Γ (a :: Formula.not a :: Δ) (Formula.imp a b) :=
      ProvesProp.mp (wtImp hnb hna) (ProvesProp.axCP ha hb) hc
    exact ProvesProp.mp ha himp hahyp
  exact ProvesProp.impIntro hna (ProvesProp.impIntro ha hbctx)

/-- Consequentia mirabilis: `⊢ (¬p → p) → p`.  The classical base case. -/
theorem pCM {p : Formula} (hp : (liftFormula? env Γ p).isSome = true) :
    ProvesProp env Γ Δ (Formula.imp (Formula.imp (Formula.not p) p) p) := by
  -- write Y = ¬p → p, Q = ¬Y inline
  have hnp := wtNot hp
  have hY : (liftFormula? env Γ (Formula.imp (Formula.not p) p)).isSome = true := wtImp hnp hp
  have hQ : (liftFormula? env Γ (Formula.not (Formula.imp (Formula.not p) p))).isSome = true :=
    wtNot hY
  -- F : ¬p → (p → ¬Y)
  have hF : ProvesProp env Γ Δ (Formula.imp (Formula.not p)
      (Formula.imp p (Formula.not (Formula.imp (Formula.not p) p)))) := pEF hp hQ
  -- S1 : (¬p → (p → ¬Y)) → ((¬p → p) → (¬p → ¬Y))
  have hS1 := ProvesProp.axS (Δ := Δ) (φ := Formula.not p) (ψ := p)
    (χ := Formula.not (Formula.imp (Formula.not p) p)) hnp hp hQ
  -- P1 : Y → (¬p → ¬Y)     [since ¬p → p is Y]
  have hP1 : ProvesProp env Γ Δ (Formula.imp (Formula.imp (Formula.not p) p)
      (Formula.imp (Formula.not p) (Formula.not (Formula.imp (Formula.not p) p)))) :=
    ProvesProp.mp (wtImp hnp (wtImp hp hQ)) hS1 hF
  -- P2 : (¬p → ¬Y) → (Y → p)     [axCP with φ:=Y, ψ:=p, ¬Y is ¬φ]
  have hP2 : ProvesProp env Γ Δ (Formula.imp
      (Formula.imp (Formula.not p) (Formula.not (Formula.imp (Formula.not p) p)))
      (Formula.imp (Formula.imp (Formula.not p) p) p)) := ProvesProp.axCP hY hp
  -- P3 : Y → (Y → p)
  have hP3 : ProvesProp env Γ Δ (Formula.imp (Formula.imp (Formula.not p) p)
      (Formula.imp (Formula.imp (Formula.not p) p) p)) :=
    pImpTrans hY (wtImp hnp hQ) (wtImp hY hp) hP1 hP2
  -- contract with axS and Y → Y
  have hS2 := ProvesProp.axS (Δ := Δ) (φ := Formula.imp (Formula.not p) p)
    (ψ := Formula.imp (Formula.not p) p) (χ := p) hY hY hp
  exact ProvesProp.mp (wtImp hY hY)
    (ProvesProp.mp (wtImp hY (wtImp hY hp)) hS2 hP3) (pImpId hY)

/-- Double negation elimination: `⊢ ¬¬p → p`. -/
theorem pDNE {p : Formula} (hp : (liftFormula? env Γ p).isSome = true) :
    ProvesProp env Γ Δ (Formula.imp (Formula.not (Formula.not p)) p) := by
  have hnp := wtNot hp
  have hnnp := wtNot hnp
  -- star : ¬¬p → (¬p → p)
  have hstar : ProvesProp env Γ (Formula.not (Formula.not p) :: Δ)
      (Formula.imp (Formula.not (Formula.not p)) (Formula.imp (Formula.not p) p)) :=
    pEF hnp hp
  have hh : ProvesProp env Γ (Formula.not (Formula.not p) :: Δ) (Formula.not (Formula.not p)) :=
    ProvesProp.hyp (by simp)
  have hd : ProvesProp env Γ (Formula.not (Formula.not p) :: Δ) (Formula.imp (Formula.not p) p) :=
    ProvesProp.mp hnnp hstar hh
  have hres : ProvesProp env Γ (Formula.not (Formula.not p) :: Δ) p :=
    ProvesProp.mp (wtImp hnp hp) (pCM hp) hd
  exact ProvesProp.impIntro hnnp hres

/-- Reductio: from `φ ⊢ ψ` and `φ ⊢ ¬ψ` conclude `⊢ ¬φ`. -/
theorem pRaa {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hp : ProvesProp env Γ (φ :: Δ) ψ) (hn : ProvesProp env Γ (φ :: Δ) (Formula.not ψ)) :
    ProvesProp env Γ Δ (Formula.not φ) := by
  have hnφ := wtNot hφ
  have hnψ := wtNot hψ
  -- φ ⊢ ¬φ via ex falso on the contradiction ψ, ¬ψ
  have hself : ProvesProp env Γ (φ :: Δ) (Formula.not φ) := by
    have hef : ProvesProp env Γ (φ :: Δ)
        (Formula.imp (Formula.not ψ) (Formula.imp ψ (Formula.not φ))) := pEF hψ hnφ
    exact ProvesProp.mp hψ (ProvesProp.mp hnψ hef hn) hp
  -- SR : φ → ¬φ
  have hSR : ProvesProp env Γ Δ (Formula.imp φ (Formula.not φ)) :=
    ProvesProp.impIntro hφ hself
  -- SR' : ¬¬φ → ¬φ    (compose DNE with SR)
  have hSR' : ProvesProp env Γ Δ (Formula.imp (Formula.not (Formula.not φ)) (Formula.not φ)) :=
    pImpTrans (wtNot hnφ) hφ hnφ (pDNE hφ) hSR
  -- CM at ¬φ : (¬¬φ → ¬φ) → ¬φ
  exact ProvesProp.mp (wtImp (wtNot hnφ) hnφ) (pCM hnφ) hSR'

/-- Classical proof by cases: if `χ` follows from `φ` and from `¬φ`, it holds. -/
theorem pByCases {φ χ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hχ : (liftFormula? env Γ χ).isSome = true)
    (h1 : ProvesProp env Γ (φ :: Δ) χ) (h2 : ProvesProp env Γ (Formula.not φ :: Δ) χ) :
    ProvesProp env Γ Δ χ := by
  have hnφ := wtNot hφ
  have hnχ := wtNot hχ
  -- weaken the two premises into the context ¬χ :: Δ
  have h1' : ProvesProp env Γ (φ :: Formula.not χ :: Δ) χ :=
    pMono (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) h1
  have hnχhyp : ProvesProp env Γ (φ :: Formula.not χ :: Δ) (Formula.not χ) :=
    ProvesProp.hyp (by simp)
  have hnφctx : ProvesProp env Γ (Formula.not χ :: Δ) (Formula.not φ) :=
    pRaa hφ hχ h1' hnχhyp
  have h2' : ProvesProp env Γ (Formula.not φ :: Formula.not χ :: Δ) χ :=
    pMono (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) h2
  have hB' : ProvesProp env Γ (Formula.not χ :: Δ) (Formula.imp (Formula.not φ) χ) :=
    ProvesProp.impIntro hnφ h2'
  have hχctx : ProvesProp env Γ (Formula.not χ :: Δ) χ := ProvesProp.mp hnφ hB' hnφctx
  exact ProvesProp.mp (wtImp hnχ hχ) (pCM hχ) (ProvesProp.impIntro hnχ hχctx)

/-! ## Succedent-disjunction algebra

    The succedent `φ :: Θ` denotes `rightOr φ Θ`.  These lemmas realise the
    structural succedent moves (weakening a proved member in, associativity and
    commutativity) needed by the focused right rules. -/

/-- Inject a proved succedent member into the right-nested disjunction. -/
theorem pRightOr_mem {A : List Formula} : ∀ (φ : Formula) (Θ : List Formula) {ψ : Formula},
    ψ ∈ φ :: Θ -> ProvesProp env Γ A ψ -> LiftsAllF env Γ (φ :: Θ) ->
    ProvesProp env Γ A (rightOr φ Θ)
  | φ, [], ψ, hmem, hψ, _ => by
      rcases List.mem_cons.1 hmem with h | h
      · exact h ▸ hψ
      · cases h
  | φ, χ :: Θ', ψ, hmem, hψ, hall => by
      have hφ := hall.head
      have hrest : (liftFormula? env Γ (rightOr χ Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ Θ' hall.tail.head hall.tail.tail
      rcases List.mem_cons.1 hmem with h | h
      · simp only [rightOr]; exact pOrInl hφ hrest (h ▸ hψ)
      · have hrec := pRightOr_mem χ Θ' h hψ hall.tail
        simp only [rightOr]; exact pOrInr hφ hrest hrec

/-- Commutativity of `∨` under provability. -/
theorem pOrComm {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true)
    (h : ProvesProp env Γ Δ (Formula.or a b)) : ProvesProp env Γ Δ (Formula.or b a) :=
  pOrElim ha hb (wtOr hb ha) h (ProvesProp.axOrR hb ha) (ProvesProp.axOrL hb ha)

/-- Left reassociation: `a ∨ (b ∨ c) ⊢ (a ∨ b) ∨ c`. -/
theorem pOrAssocL {a b c : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (hc : (liftFormula? env Γ c).isSome = true)
    (h : ProvesProp env Γ Δ (Formula.or a (Formula.or b c))) :
    ProvesProp env Γ Δ (Formula.or (Formula.or a b) c) := by
  have hab := wtOr ha hb
  have hbc := wtOr hb hc
  have hT := wtOr hab hc
  have iaT : ProvesProp env Γ Δ (Formula.imp a (Formula.or (Formula.or a b) c)) :=
    pImpTrans ha hab hT (ProvesProp.axOrL ha hb) (ProvesProp.axOrL hab hc)
  have ibT : ProvesProp env Γ Δ (Formula.imp b (Formula.or (Formula.or a b) c)) :=
    pImpTrans hb hab hT (ProvesProp.axOrR ha hb) (ProvesProp.axOrL hab hc)
  have icT : ProvesProp env Γ Δ (Formula.imp c (Formula.or (Formula.or a b) c)) :=
    ProvesProp.axOrR hab hc
  have ibcT : ProvesProp env Γ Δ (Formula.imp (Formula.or b c) (Formula.or (Formula.or a b) c)) :=
    ProvesProp.mp (wtImp hc hT)
      (ProvesProp.mp (wtImp hb hT) (ProvesProp.axOrE hb hc hT) ibT) icT
  exact pOrElim ha hbc hT h iaT ibcT

/-! ## The two-sided sequent and its ⊥-free denotation -/

/-- A two-sided analytic search sequent `ante ⊢ succ`. -/
structure FSequent where
  ante : List Formula
  succ : List Formula
  deriving Repr, BEq, DecidableEq

/-- Denotation into the propositional fragment.  A nonempty succedent is read as
    its right-nested disjunction.  The empty succedent is given the ⊥-free
    meaning "the antecedent is absurd" — it proves every well-typed formula — so
    no falsity constant is introduced into M3. -/
def denote (env : Env) (Γ : Ctx) : FSequent -> Prop
  | ⟨ante, []⟩ => ∀ φ, (liftFormula? env Γ φ).isSome = true -> ProvesProp env Γ ante φ
  | ⟨ante, φ :: Θ⟩ => ProvesProp env Γ ante (rightOr φ Θ)

/-! ## The two-sided analytic LK substrate

    This is an unfocused multi-conclusion sequent calculus over `FSequent`.
    Each rule keeps the principal formula at the head of its side; the classical
    `¬` shifts `negR`/
    `negL` are the only genuinely non-analytic rules and compile (via
    `analyticSound`) to the `axCP`-derived kernel.  Well-typedness of principal
    subformulas and of the residual succedent is carried as side conditions so
    that soundness can reconstruct the `ProvesProp` witnesses. -/

inductive FDeriv (env : Env) (Γ : Ctx) : FSequent -> Prop where
  | id {A S : List Formula} {φ : Formula} :
      φ ∈ A -> φ ∈ S -> LiftsAllF env Γ S -> FDeriv env Γ ⟨A, S⟩
  | negR {A Θ : List Formula} {φ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> LiftsAllF env Γ Θ ->
      FDeriv env Γ ⟨φ :: A, Θ⟩ -> FDeriv env Γ ⟨A, Formula.not φ :: Θ⟩
  | negL {A Θ : List Formula} {φ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> LiftsAllF env Γ Θ ->
      FDeriv env Γ ⟨A, φ :: Θ⟩ -> FDeriv env Γ ⟨Formula.not φ :: A, Θ⟩
  | impR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FDeriv env Γ ⟨φ :: A, ψ :: Θ⟩ ->
      FDeriv env Γ ⟨A, Formula.imp φ ψ :: Θ⟩
  | impL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FDeriv env Γ ⟨A, φ :: Θ⟩ -> FDeriv env Γ ⟨ψ :: A, Θ⟩ ->
      FDeriv env Γ ⟨Formula.imp φ ψ :: A, Θ⟩
  | andR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FDeriv env Γ ⟨A, φ :: Θ⟩ -> FDeriv env Γ ⟨A, ψ :: Θ⟩ ->
      FDeriv env Γ ⟨A, Formula.and φ ψ :: Θ⟩
  | andL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      FDeriv env Γ ⟨φ :: ψ :: A, Θ⟩ -> FDeriv env Γ ⟨Formula.and φ ψ :: A, Θ⟩
  | orR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FDeriv env Γ ⟨A, φ :: ψ :: Θ⟩ ->
      FDeriv env Γ ⟨A, Formula.or φ ψ :: Θ⟩
  | orL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FDeriv env Γ ⟨φ :: A, Θ⟩ -> FDeriv env Γ ⟨ψ :: A, Θ⟩ ->
      FDeriv env Γ ⟨Formula.or φ ψ :: A, Θ⟩
  | iffR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ ->
      FDeriv env Γ ⟨A, Formula.imp φ ψ :: Θ⟩ ->
      FDeriv env Γ ⟨A, Formula.imp ψ φ :: Θ⟩ ->
      FDeriv env Γ ⟨A, Formula.iff φ ψ :: Θ⟩
  | iffL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      FDeriv env Γ ⟨Formula.imp φ ψ :: Formula.imp ψ φ :: A, Θ⟩ ->
      FDeriv env Γ ⟨Formula.iff φ ψ :: A, Θ⟩

/-! ## Rule-wise soundness

    Each lemma reconstructs the conclusion's denotation from the premises', using
    only the classical kernel and the succedent algebra.  They are assembled into
    `analyticSound` by a direct induction. -/

theorem soundId {A S : List Formula} {φ : Formula}
    (hA : φ ∈ A) (hS : φ ∈ S) (hall : LiftsAllF env Γ S) : denote env Γ ⟨A, S⟩ := by
  cases S with
  | nil => cases hS
  | cons hd tl =>
      show ProvesProp env Γ A (rightOr hd tl)
      exact pRightOr_mem hd tl hS (ProvesProp.hyp hA) hall

/-- Cut the conjunction hypothesis back to its two components. -/
theorem pAndLcut {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (h : ProvesProp env Γ (φ :: ψ :: A) T) :
    ProvesProp env Γ (Formula.and φ ψ :: A) T := by
  have h1 : ProvesProp env Γ (ψ :: A) (Formula.imp φ T) := ProvesProp.impIntro hφ h
  have h2 : ProvesProp env Γ A (Formula.imp ψ (Formula.imp φ T)) := ProvesProp.impIntro hψ h1
  have h2w : ProvesProp env Γ (Formula.and φ ψ :: A) (Formula.imp ψ (Formula.imp φ T)) :=
    pMono (fun x hx => List.mem_cons_of_mem _ hx) h2
  have hand : ProvesProp env Γ (Formula.and φ ψ :: A) (Formula.and φ ψ) := ProvesProp.hyp (by simp)
  have hφp : ProvesProp env Γ (Formula.and φ ψ :: A) φ :=
    ProvesProp.mp (wtAnd hφ hψ) (ProvesProp.axAndL hφ hψ) hand
  have hψp : ProvesProp env Γ (Formula.and φ ψ :: A) ψ :=
    ProvesProp.mp (wtAnd hφ hψ) (ProvesProp.axAndR hφ hψ) hand
  exact ProvesProp.mp hφ (ProvesProp.mp hψ h2w hψp) hφp

theorem soundAndL {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (ih : denote env Γ ⟨φ :: ψ :: A, Θ⟩) : denote env Γ ⟨Formula.and φ ψ :: A, Θ⟩ := by
  cases Θ with
  | nil => intro χ hχ; exact pAndLcut hφ hψ (ih χ hχ)
  | cons χ0 Θ' =>
      show ProvesProp env Γ (Formula.and φ ψ :: A) (rightOr χ0 Θ')
      exact pAndLcut hφ hψ ih

theorem soundNegR {A Θ : List Formula} {φ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hΘ : LiftsAllF env Γ Θ)
    (ih : denote env Γ ⟨φ :: A, Θ⟩) : denote env Γ ⟨A, Formula.not φ :: Θ⟩ := by
  show ProvesProp env Γ A (rightOr (Formula.not φ) Θ)
  cases Θ with
  | nil =>
      show ProvesProp env Γ A (Formula.not φ)
      exact pRaa hφ hφ (ih φ hφ) (ih (Formula.not φ) (wtNot hφ))
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ A (Formula.or (Formula.not φ) (rightOr χ0 Θ'))
      apply pByCases hφ (wtOr (wtNot hφ) hR)
      · exact pOrInr (wtNot hφ) hR ih
      · exact pOrInl (wtNot hφ) hR (ProvesProp.hyp (by simp))

theorem soundNegL {A Θ : List Formula} {φ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hΘ : LiftsAllF env Γ Θ)
    (ih : denote env Γ ⟨A, φ :: Θ⟩) : denote env Γ ⟨Formula.not φ :: A, Θ⟩ := by
  have ihp : ProvesProp env Γ A (rightOr φ Θ) := ih
  cases Θ with
  | nil =>
      intro χ hχ
      have hφweak : ProvesProp env Γ (Formula.not φ :: A) φ :=
        pMono (fun x hx => List.mem_cons_of_mem _ hx) ihp
      have hnφ : ProvesProp env Γ (Formula.not φ :: A) (Formula.not φ) := ProvesProp.hyp (by simp)
      have hef : ProvesProp env Γ (Formula.not φ :: A)
          (Formula.imp (Formula.not φ) (Formula.imp φ χ)) := pEF hφ hχ
      exact ProvesProp.mp hφ (ProvesProp.mp (wtNot hφ) hef hnφ) hφweak
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ (Formula.not φ :: A) (rightOr χ0 Θ')
      have ihw : ProvesProp env Γ (Formula.not φ :: A) (Formula.or φ (rightOr χ0 Θ')) :=
        pMono (fun x hx => List.mem_cons_of_mem _ hx) ihp
      have hnφ : ProvesProp env Γ (Formula.not φ :: A) (Formula.not φ) := ProvesProp.hyp (by simp)
      have hl : ProvesProp env Γ (Formula.not φ :: A) (Formula.imp φ (rightOr χ0 Θ')) := by
        have hef : ProvesProp env Γ (Formula.not φ :: A)
            (Formula.imp (Formula.not φ) (Formula.imp φ (rightOr χ0 Θ'))) := pEF hφ hR
        exact ProvesProp.mp (wtNot hφ) hef hnφ
      exact pOrElim hφ hR hR ihw hl (pImpId hR)

theorem soundOrR {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hΘ : LiftsAllF env Γ Θ) (ih : denote env Γ ⟨A, φ :: ψ :: Θ⟩) :
    denote env Γ ⟨A, Formula.or φ ψ :: Θ⟩ := by
  have ihp : ProvesProp env Γ A (Formula.or φ (rightOr ψ Θ)) := ih
  cases Θ with
  | nil => show ProvesProp env Γ A (Formula.or φ ψ); exact ihp
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ A (Formula.or (Formula.or φ ψ) (rightOr χ0 Θ'))
      exact pOrAssocL hφ hψ hR ihp

/-- Cut the two case-branches of a disjunction hypothesis into a common goal. -/
theorem pOrLcut {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hT : (liftFormula? env Γ T).isSome = true)
    (h1 : ProvesProp env Γ (φ :: A) T) (h2 : ProvesProp env Γ (ψ :: A) T) :
    ProvesProp env Γ (Formula.or φ ψ :: A) T := by
  have hl : ProvesProp env Γ (Formula.or φ ψ :: A) (Formula.imp φ T) :=
    pMono (fun x hx => List.mem_cons_of_mem _ hx) (ProvesProp.impIntro hφ h1)
  have hr : ProvesProp env Γ (Formula.or φ ψ :: A) (Formula.imp ψ T) :=
    pMono (fun x hx => List.mem_cons_of_mem _ hx) (ProvesProp.impIntro hψ h2)
  have hor : ProvesProp env Γ (Formula.or φ ψ :: A) (Formula.or φ ψ) := ProvesProp.hyp (by simp)
  exact pOrElim hφ hψ hT hor hl hr

theorem soundOrL {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hΘ : LiftsAllF env Γ Θ) (ih1 : denote env Γ ⟨φ :: A, Θ⟩) (ih2 : denote env Γ ⟨ψ :: A, Θ⟩) :
    denote env Γ ⟨Formula.or φ ψ :: A, Θ⟩ := by
  cases Θ with
  | nil => intro χ hχ; exact pOrLcut hφ hψ hχ (ih1 χ hχ) (ih2 χ hχ)
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ (Formula.or φ ψ :: A) (rightOr χ0 Θ')
      exact pOrLcut hφ hψ hR ih1 ih2

theorem soundImpR {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hΘ : LiftsAllF env Γ Θ) (ih : denote env Γ ⟨φ :: A, ψ :: Θ⟩) :
    denote env Γ ⟨A, Formula.imp φ ψ :: Θ⟩ := by
  have ihp : ProvesProp env Γ (φ :: A) (rightOr ψ Θ) := ih
  show ProvesProp env Γ A (rightOr (Formula.imp φ ψ) Θ)
  cases Θ with
  | nil =>
      show ProvesProp env Γ A (Formula.imp φ ψ)
      exact ProvesProp.impIntro hφ ihp
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ A (Formula.or (Formula.imp φ ψ) (rightOr χ0 Θ'))
      apply pByCases hφ (wtOr (wtImp hφ hψ) hR)
      · have hl : ProvesProp env Γ (φ :: A)
            (Formula.imp ψ (Formula.or (Formula.imp φ ψ) (rightOr χ0 Θ'))) := by
          apply ProvesProp.impIntro hψ
          exact pOrInl (wtImp hφ hψ) hR (pImpK hφ hψ (ProvesProp.hyp (by simp)))
        have hr : ProvesProp env Γ (φ :: A)
            (Formula.imp (rightOr χ0 Θ') (Formula.or (Formula.imp φ ψ) (rightOr χ0 Θ'))) :=
          ProvesProp.axOrR (wtImp hφ hψ) hR
        exact pOrElim hψ hR (wtOr (wtImp hφ hψ) hR) ihp hl hr
      · have hφψ : ProvesProp env Γ (Formula.not φ :: A) (Formula.imp φ ψ) := by
          have hef : ProvesProp env Γ (Formula.not φ :: A)
              (Formula.imp (Formula.not φ) (Formula.imp φ ψ)) := pEF hφ hψ
          exact ProvesProp.mp (wtNot hφ) hef (ProvesProp.hyp (by simp))
        exact pOrInl (wtImp hφ hψ) hR hφψ

theorem soundImpL {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hΘ : LiftsAllF env Γ Θ) (ih1 : denote env Γ ⟨A, φ :: Θ⟩) (ih2 : denote env Γ ⟨ψ :: A, Θ⟩) :
    denote env Γ ⟨Formula.imp φ ψ :: A, Θ⟩ := by
  have ih1p : ProvesProp env Γ A (rightOr φ Θ) := ih1
  cases Θ with
  | nil =>
      intro χ hχ
      have hφp : ProvesProp env Γ (Formula.imp φ ψ :: A) φ :=
        pMono (fun x hx => List.mem_cons_of_mem _ hx) ih1p
      have himp : ProvesProp env Γ (Formula.imp φ ψ :: A) (Formula.imp φ ψ) :=
        ProvesProp.hyp (by simp)
      have hψp : ProvesProp env Γ (Formula.imp φ ψ :: A) ψ := ProvesProp.mp hφ himp hφp
      have h2 : ProvesProp env Γ (Formula.imp φ ψ :: A) (Formula.imp ψ χ) :=
        pMono (fun x hx => List.mem_cons_of_mem _ hx) (ProvesProp.impIntro hψ (ih2 χ hχ))
      exact ProvesProp.mp hψ h2 hψp
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ (Formula.imp φ ψ :: A) (rightOr χ0 Θ')
      have ih1w : ProvesProp env Γ (Formula.imp φ ψ :: A) (Formula.or φ (rightOr χ0 Θ')) :=
        pMono (fun x hx => List.mem_cons_of_mem _ hx) ih1p
      have hl : ProvesProp env Γ (Formula.imp φ ψ :: A) (Formula.imp φ (rightOr χ0 Θ')) := by
        apply ProvesProp.impIntro hφ
        have himp : ProvesProp env Γ (φ :: Formula.imp φ ψ :: A) (Formula.imp φ ψ) :=
          ProvesProp.hyp (by simp)
        have hφh : ProvesProp env Γ (φ :: Formula.imp φ ψ :: A) φ := ProvesProp.hyp (by simp)
        have hψp : ProvesProp env Γ (φ :: Formula.imp φ ψ :: A) ψ := ProvesProp.mp hφ himp hφh
        have h2 : ProvesProp env Γ (φ :: Formula.imp φ ψ :: A) (Formula.imp ψ (rightOr χ0 Θ')) :=
          pMono (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
            (ProvesProp.impIntro hψ ih2)
        exact ProvesProp.mp hψ h2 hψp
      exact pOrElim hφ hR hR ih1w hl (pImpId hR)

theorem soundAndR {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hΘ : LiftsAllF env Γ Θ) (ih1 : denote env Γ ⟨A, φ :: Θ⟩) (ih2 : denote env Γ ⟨A, ψ :: Θ⟩) :
    denote env Γ ⟨A, Formula.and φ ψ :: Θ⟩ := by
  have ih1p : ProvesProp env Γ A (rightOr φ Θ) := ih1
  have ih2p : ProvesProp env Γ A (rightOr ψ Θ) := ih2
  show ProvesProp env Γ A (rightOr (Formula.and φ ψ) Θ)
  cases Θ with
  | nil =>
      show ProvesProp env Γ A (Formula.and φ ψ)
      exact ProvesProp.mp hψ (ProvesProp.mp hφ (ProvesProp.axAndI hφ hψ) ih1p) ih2p
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      show ProvesProp env Γ A (Formula.or (Formula.and φ ψ) (rightOr χ0 Θ'))
      have hgoalwt : (liftFormula? env Γ (Formula.or (Formula.and φ ψ) (rightOr χ0 Θ'))).isSome = true :=
        wtOr (wtAnd hφ hψ) hR
      have hlouter : ProvesProp env Γ A
          (Formula.imp φ (Formula.or (Formula.and φ ψ) (rightOr χ0 Θ'))) := by
        apply ProvesProp.impIntro hφ
        have ih2w : ProvesProp env Γ (φ :: A) (Formula.or ψ (rightOr χ0 Θ')) :=
          pMono (fun x hx => List.mem_cons_of_mem _ hx) ih2p
        have hlin : ProvesProp env Γ (φ :: A)
            (Formula.imp ψ (Formula.or (Formula.and φ ψ) (rightOr χ0 Θ'))) := by
          apply ProvesProp.impIntro hψ
          have hφh : ProvesProp env Γ (ψ :: φ :: A) φ := ProvesProp.hyp (by simp)
          have hψh : ProvesProp env Γ (ψ :: φ :: A) ψ := ProvesProp.hyp (by simp)
          have hand : ProvesProp env Γ (ψ :: φ :: A) (Formula.and φ ψ) :=
            ProvesProp.mp hψ (ProvesProp.mp hφ (ProvesProp.axAndI hφ hψ) hφh) hψh
          exact pOrInl (wtAnd hφ hψ) hR hand
        have hrin : ProvesProp env Γ (φ :: A)
            (Formula.imp (rightOr χ0 Θ') (Formula.or (Formula.and φ ψ) (rightOr χ0 Θ'))) :=
          ProvesProp.axOrR (wtAnd hφ hψ) hR
        exact pOrElim hψ hR hgoalwt ih2w hlin hrin
      have hrouter : ProvesProp env Γ A
          (Formula.imp (rightOr χ0 Θ') (Formula.or (Formula.and φ ψ) (rightOr χ0 Θ'))) :=
        ProvesProp.axOrR (wtAnd hφ hψ) hR
      exact pOrElim hφ hR hgoalwt ih1p hlouter hrouter

/-- Cut an iff hypothesis back to its two directional implications. -/
theorem pIffLcut {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (h : ProvesProp env Γ
      (Formula.imp φ ψ :: Formula.imp ψ φ :: A) T) :
    ProvesProp env Γ (Formula.iff φ ψ :: A) T := by
  have hfwd := wtImp hφ hψ
  have hrev := wtImp hψ hφ
  have h1 : ProvesProp env Γ (Formula.imp ψ φ :: A)
      (Formula.imp (Formula.imp φ ψ) T) := ProvesProp.impIntro hfwd h
  have h2 : ProvesProp env Γ A
      (Formula.imp (Formula.imp ψ φ) (Formula.imp (Formula.imp φ ψ) T)) :=
    ProvesProp.impIntro hrev h1
  have h2w := pMono (env := env) (Γ := Γ)
    (Δ := A) (Δ' := Formula.iff φ ψ :: A)
    (fun x hx => List.mem_cons_of_mem _ hx) h2
  have hiff : ProvesProp env Γ (Formula.iff φ ψ :: A) (Formula.iff φ ψ) :=
    ProvesProp.hyp (by simp)
  have hfwdp : ProvesProp env Γ (Formula.iff φ ψ :: A) (Formula.imp φ ψ) :=
    ProvesProp.mp (wtIff hφ hψ) (ProvesProp.axIffL hφ hψ) hiff
  have hrevp : ProvesProp env Γ (Formula.iff φ ψ :: A) (Formula.imp ψ φ) :=
    ProvesProp.mp (wtIff hφ hψ) (ProvesProp.axIffR hφ hψ) hiff
  exact ProvesProp.mp hfwd (ProvesProp.mp hrev h2w hrevp) hfwdp

theorem soundIffL {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (ih : denote env Γ
      ⟨Formula.imp φ ψ :: Formula.imp ψ φ :: A, Θ⟩) :
    denote env Γ ⟨Formula.iff φ ψ :: A, Θ⟩ := by
  cases Θ with
  | nil => intro χ hχ; exact pIffLcut hφ hψ (ih χ hχ)
  | cons χ0 Θ' =>
      show ProvesProp env Γ (Formula.iff φ ψ :: A) (rightOr χ0 Θ')
      exact pIffLcut hφ hψ ih

theorem soundIffR {A Θ : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hΘ : LiftsAllF env Γ Θ)
    (ih1 : denote env Γ ⟨A, Formula.imp φ ψ :: Θ⟩)
    (ih2 : denote env Γ ⟨A, Formula.imp ψ φ :: Θ⟩) :
    denote env Γ ⟨A, Formula.iff φ ψ :: Θ⟩ := by
  let fwd := Formula.imp φ ψ
  let rev := Formula.imp ψ φ
  have hfwd : (liftFormula? env Γ fwd).isSome = true := wtImp hφ hψ
  have hrev : (liftFormula? env Γ rev).isSome = true := wtImp hψ hφ
  have ih1p : ProvesProp env Γ A (rightOr fwd Θ) := ih1
  have ih2p : ProvesProp env Γ A (rightOr rev Θ) := ih2
  show ProvesProp env Γ A (rightOr (Formula.iff φ ψ) Θ)
  cases Θ with
  | nil =>
      exact ProvesProp.mp hrev
        (ProvesProp.mp hfwd (ProvesProp.axIffI hφ hψ) ih1p) ih2p
  | cons χ0 Θ' =>
      have hR : (liftFormula? env Γ (rightOr χ0 Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
      have hgoalwt := wtOr (wtIff hφ hψ) hR
      have hlouter : ProvesProp env Γ A
          (Formula.imp fwd (Formula.or (Formula.iff φ ψ) (rightOr χ0 Θ'))) := by
        apply ProvesProp.impIntro hfwd
        have ih2w : ProvesProp env Γ (fwd :: A) (Formula.or rev (rightOr χ0 Θ')) :=
          pMono (fun x hx => List.mem_cons_of_mem _ hx) ih2p
        have hlin : ProvesProp env Γ (fwd :: A)
            (Formula.imp rev (Formula.or (Formula.iff φ ψ) (rightOr χ0 Θ'))) := by
          apply ProvesProp.impIntro hrev
          have hfwdh : ProvesProp env Γ (rev :: fwd :: A) fwd := ProvesProp.hyp (by simp)
          have hrevh : ProvesProp env Γ (rev :: fwd :: A) rev := ProvesProp.hyp (by simp)
          have hiffp : ProvesProp env Γ (rev :: fwd :: A) (Formula.iff φ ψ) :=
            ProvesProp.mp hrev
              (ProvesProp.mp hfwd (ProvesProp.axIffI hφ hψ) hfwdh) hrevh
          exact pOrInl (wtIff hφ hψ) hR hiffp
        have hrin : ProvesProp env Γ (fwd :: A)
            (Formula.imp (rightOr χ0 Θ')
              (Formula.or (Formula.iff φ ψ) (rightOr χ0 Θ'))) :=
          ProvesProp.axOrR (wtIff hφ hψ) hR
        exact pOrElim hrev hR hgoalwt ih2w hlin hrin
      have hrouter : ProvesProp env Γ A
          (Formula.imp (rightOr χ0 Θ')
            (Formula.or (Formula.iff φ ψ) (rightOr χ0 Θ'))) :=
        ProvesProp.axOrR (wtIff hφ hψ) hR
      exact pOrElim hfwd hR hgoalwt ih1p hlouter hrouter

/-- **Soundness of the analytic LK substrate** (M3-internal): every `FDeriv` derivation
    denotes a `ProvesProp` derivation, i.e. compiles back to M3's own K/S/axCP
    provability with the succedent read as a right-nested disjunction. -/
theorem analyticSound {S : FSequent} (h : FDeriv env Γ S) : denote env Γ S := by
  induction h with
  | id hA hS hall => exact soundId hA hS hall
  | negR hφ hΘ _ ih => exact soundNegR hφ hΘ ih
  | negL hφ hΘ _ ih => exact soundNegL hφ hΘ ih
  | impR hφ hψ hΘ _ ih => exact soundImpR hφ hψ hΘ ih
  | impL hφ hψ hΘ _ _ ih1 ih2 => exact soundImpL hφ hψ hΘ ih1 ih2
  | andR hφ hψ hΘ _ _ ih1 ih2 => exact soundAndR hφ hψ hΘ ih1 ih2
  | andL hφ hψ _ ih => exact soundAndL hφ hψ ih
  | orR hφ hψ hΘ _ ih => exact soundOrR hφ hψ hΘ ih
  | orL hφ hψ hΘ _ _ ih1 ih2 => exact soundOrL hφ hψ hΘ ih1 ih2
  | iffR hφ hψ hΘ _ _ ih1 ih2 => exact soundIffR hφ hψ hΘ ih1 ih2
  | iffL hφ hψ _ ih => exact soundIffL hφ hψ ih

/-- The concrete M3/Core replay boundary for an ordinary single-goal sequent. -/
theorem analyticSoundSingle {A : List Formula} {φ : Formula}
    (h : FDeriv env Γ ⟨A, [φ]⟩) : Proves env Γ A φ :=
  ProvesProp.toProves (analyticSound h)

/-- Regression: primitive iff replay closes an ordinary single-goal theorem. -/
theorem analyticIffRefl {φ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) :
    Proves env Γ [] (Formula.iff φ φ) := by
  apply analyticSoundSingle
  apply FDeriv.iffR hφ hφ LiftsAllF.nil
  · apply FDeriv.impR hφ hφ LiftsAllF.nil
    exact FDeriv.id (env := env) (Γ := Γ) (A := [φ]) (S := [φ]) (φ := φ)
      (by simp) (by simp) (LiftsAllF.cons hφ LiftsAllF.nil)
  · apply FDeriv.impR hφ hφ LiftsAllF.nil
    exact FDeriv.id (env := env) (Γ := Γ) (A := [φ]) (S := [φ]) (φ := φ)
      (by simp) (by simp) (LiftsAllF.cons hφ LiftsAllF.nil)

end Focused
end ContextualHOL
