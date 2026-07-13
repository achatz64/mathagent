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

/-- Every atomic (non-connective) subformula of `φ`.  Defined at `ContextualHOL`
    scope so dot-notation `f.atoms` resolves for `f : Formula` everywhere. -/
def Formula.atoms : Formula -> List Formula
  | .atom n t u => [.atom n t u]
  | .papp n t => [.papp n t]
  | .and q r => q.atoms ++ r.atoms
  | .or q r => q.atoms ++ r.atoms
  | .imp q r => q.atoms ++ r.atoms
  | .iff q r => q.atoms ++ r.atoms
  | .not q => q.atoms
  | .all _ _ q => q.atoms
  | .ex _ _ q => q.atoms

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

/-! ## The `Type`-valued search trace (`FTrace`)

    `FDeriv` is a `Prop` with many constructors, so Lean forbids recursing from it
    into `Type`-valued certificate data (no large elimination).  `FTrace` is the
    identical rule structure carried in `Type`: it is precisely the data a search
    produces.  `FTrace.toFDeriv` erases it to the `Prop` judgement (so search,
    memoization, and `finiteStateProp` stay in `Prop`); a separate `compile`
    (next) turns it into a reified `PPTerm` certificate whose formulas and size
    can be inspected for the replay-closure and size theorems. -/

inductive FTrace (env : Env) (Γ : Ctx) : FSequent -> Type where
  | id {A S : List Formula} {φ : Formula} :
      φ ∈ A -> φ ∈ S -> LiftsAllF env Γ S -> FTrace env Γ ⟨A, S⟩
  | negR {A Θ : List Formula} {φ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> LiftsAllF env Γ Θ ->
      FTrace env Γ ⟨φ :: A, Θ⟩ -> FTrace env Γ ⟨A, Formula.not φ :: Θ⟩
  | negL {A Θ : List Formula} {φ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> LiftsAllF env Γ Θ ->
      FTrace env Γ ⟨A, φ :: Θ⟩ -> FTrace env Γ ⟨Formula.not φ :: A, Θ⟩
  | impR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FTrace env Γ ⟨φ :: A, ψ :: Θ⟩ ->
      FTrace env Γ ⟨A, Formula.imp φ ψ :: Θ⟩
  | impL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FTrace env Γ ⟨A, φ :: Θ⟩ -> FTrace env Γ ⟨ψ :: A, Θ⟩ ->
      FTrace env Γ ⟨Formula.imp φ ψ :: A, Θ⟩
  | andR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FTrace env Γ ⟨A, φ :: Θ⟩ -> FTrace env Γ ⟨A, ψ :: Θ⟩ ->
      FTrace env Γ ⟨A, Formula.and φ ψ :: Θ⟩
  | andL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      FTrace env Γ ⟨φ :: ψ :: A, Θ⟩ -> FTrace env Γ ⟨Formula.and φ ψ :: A, Θ⟩
  | orR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FTrace env Γ ⟨A, φ :: ψ :: Θ⟩ ->
      FTrace env Γ ⟨A, Formula.or φ ψ :: Θ⟩
  | orL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ -> FTrace env Γ ⟨φ :: A, Θ⟩ -> FTrace env Γ ⟨ψ :: A, Θ⟩ ->
      FTrace env Γ ⟨Formula.or φ ψ :: A, Θ⟩
  | iffR {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      LiftsAllF env Γ Θ ->
      FTrace env Γ ⟨A, Formula.imp φ ψ :: Θ⟩ ->
      FTrace env Γ ⟨A, Formula.imp ψ φ :: Θ⟩ ->
      FTrace env Γ ⟨A, Formula.iff φ ψ :: Θ⟩
  | iffL {A Θ : List Formula} {φ ψ : Formula} :
      (liftFormula? env Γ φ).isSome = true -> (liftFormula? env Γ ψ).isSome = true ->
      FTrace env Γ ⟨Formula.imp φ ψ :: Formula.imp ψ φ :: A, Θ⟩ ->
      FTrace env Γ ⟨Formula.iff φ ψ :: A, Θ⟩

/-- Erase a search trace to the `Prop` derivability judgement. -/
def FTrace.toFDeriv {env : Env} {Γ : Ctx} : {S : FSequent} ->
    FTrace env Γ S -> FDeriv env Γ S
  | _, .id hA hS hall => FDeriv.id hA hS hall
  | _, .negR hφ hΘ t => FDeriv.negR hφ hΘ t.toFDeriv
  | _, .negL hφ hΘ t => FDeriv.negL hφ hΘ t.toFDeriv
  | _, .impR hφ hψ hΘ t => FDeriv.impR hφ hψ hΘ t.toFDeriv
  | _, .impL hφ hψ hΘ t u => FDeriv.impL hφ hψ hΘ t.toFDeriv u.toFDeriv
  | _, .andR hφ hψ hΘ t u => FDeriv.andR hφ hψ hΘ t.toFDeriv u.toFDeriv
  | _, .andL hφ hψ t => FDeriv.andL hφ hψ t.toFDeriv
  | _, .orR hφ hψ hΘ t => FDeriv.orR hφ hψ hΘ t.toFDeriv
  | _, .orL hφ hψ hΘ t u => FDeriv.orL hφ hψ hΘ t.toFDeriv u.toFDeriv
  | _, .iffR hφ hψ hΘ t u => FDeriv.iffR hφ hψ hΘ t.toFDeriv u.toFDeriv
  | _, .iffL hφ hψ t => FDeriv.iffL hφ hψ t.toFDeriv

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

/-! ## The `ReplayTemplate` kernel on reified certificates

    These are the `PPTerm` (Type-valued) counterparts of the propositional
    kernel above — the *named* finite template family the compiler draws on
    (so "fixed family" is a statement about *these labels*, not the vacuous
    "uses the 15 primitive `PPTerm` constructors").  Each is the same derivation
    as its `Prop` namesake with `ProvesProp` replaced by `PPTerm`, so it carries
    real certificate structure whose `size` and formulas can be inspected. -/

/-- `φ ⇒ φ` as a certificate. -/
def PPTerm.pImpId {φ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true) :
    PPTerm env Γ Δ (Formula.imp φ φ) := by
  have hkφ : (liftFormula? env Γ (Formula.imp φ φ)).isSome = true := by
    simp [liftFormula?_imp_isSome, hφ]
  have hS := PPTerm.axS (env := env) (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := Formula.imp φ φ)
    (χ := φ) hφ hkφ hφ
  have hK1 := PPTerm.axK (env := env) (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := Formula.imp φ φ) hφ hkφ
  have hK2 := PPTerm.axK (env := env) (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := φ) hφ hφ
  have hwt2 : (liftFormula? env Γ (Formula.imp φ (Formula.imp φ φ))).isSome = true := by
    simp [liftFormula?_imp_isSome, hφ]
  exact PPTerm.mp hwt2
    (PPTerm.mp (by simp [liftFormula?_imp_isSome, hφ, hkφ]) hS hK1) hK2

/-- Left disjunction introduction certificate. -/
def PPTerm.pOrInl {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : PPTerm env Γ Δ φ) :
    PPTerm env Γ Δ (Formula.or φ ψ) :=
  PPTerm.mp hφ (PPTerm.axOrL hφ hψ) h

/-- Right disjunction introduction certificate. -/
def PPTerm.pOrInr {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : PPTerm env Γ Δ ψ) :
    PPTerm env Γ Δ (Formula.or φ ψ) :=
  PPTerm.mp hψ (PPTerm.axOrR hφ hψ) h

/-- Disjunction elimination certificate. -/
def PPTerm.pOrElim {φ ψ χ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hχ : (liftFormula? env Γ χ).isSome = true)
    (hor : PPTerm env Γ Δ (Formula.or φ ψ))
    (hl : PPTerm env Γ Δ (Formula.imp φ χ))
    (hr : PPTerm env Γ Δ (Formula.imp ψ χ)) :
    PPTerm env Γ Δ χ := by
  have hlφχ : (liftFormula? env Γ (Formula.imp φ χ)).isSome = true := by
    simp [liftFormula?_imp_isSome, hφ, hχ]
  have hlψχ : (liftFormula? env Γ (Formula.imp ψ χ)).isSome = true := by
    simp [liftFormula?_imp_isSome, hψ, hχ]
  have horψ : (liftFormula? env Γ (Formula.or φ ψ)).isSome = true := by
    simp [liftFormula?_or_isSome, hφ, hψ]
  exact PPTerm.mp horψ
    (PPTerm.mp hlψχ (PPTerm.mp hlφχ (PPTerm.axOrE hφ hψ hχ) hl) hr) hor

/-- Weakening a certificate into an implication: `⊢ b` gives `⊢ a → b`. -/
def PPTerm.pImpK {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (h : PPTerm env Γ Δ b) :
    PPTerm env Γ Δ (Formula.imp a b) :=
  PPTerm.mp hb (PPTerm.axK hb ha) h

/-- Hypothetical syllogism certificate. -/
def PPTerm.pImpTrans {a b c : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (hc : (liftFormula? env Γ c).isSome = true)
    (hab : PPTerm env Γ Δ (Formula.imp a b))
    (hbc : PPTerm env Γ Δ (Formula.imp b c)) :
    PPTerm env Γ Δ (Formula.imp a c) := by
  have h1 : PPTerm env Γ Δ (Formula.imp a (Formula.imp b c)) :=
    PPTerm.pImpK ha (wtImp hb hc) hbc
  have hS := PPTerm.axS (Δ := Δ) (φ := a) (ψ := b) (χ := c) ha hb hc
  exact PPTerm.mp (wtImp ha hb) (PPTerm.mp (wtImp ha (wtImp hb hc)) hS h1) hab

/-- Ex-falso certificate: `⊢ ¬a → (a → b)`. -/
def PPTerm.pEF {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) :
    PPTerm env Γ Δ (Formula.imp (Formula.not a) (Formula.imp a b)) := by
  have hna := wtNot ha
  have hnb := wtNot hb
  have hbctx : PPTerm env Γ (a :: Formula.not a :: Δ) b := by
    have hnahyp : PPTerm env Γ (a :: Formula.not a :: Δ) (Formula.not a) :=
      PPTerm.hyp (by simp)
    have hahyp : PPTerm env Γ (a :: Formula.not a :: Δ) a :=
      PPTerm.hyp (by simp)
    have hc : PPTerm env Γ (a :: Formula.not a :: Δ)
        (Formula.imp (Formula.not b) (Formula.not a)) := PPTerm.pImpK hnb hna hnahyp
    have himp : PPTerm env Γ (a :: Formula.not a :: Δ) (Formula.imp a b) :=
      PPTerm.mp (wtImp hnb hna) (PPTerm.axCP ha hb) hc
    exact PPTerm.mp ha himp hahyp
  exact PPTerm.impIntro hna (PPTerm.impIntro ha hbctx)

/-- Consequentia mirabilis certificate: `⊢ (¬p → p) → p`. -/
def PPTerm.pCM {p : Formula} (hp : (liftFormula? env Γ p).isSome = true) :
    PPTerm env Γ Δ (Formula.imp (Formula.imp (Formula.not p) p) p) := by
  have hnp := wtNot hp
  have hY : (liftFormula? env Γ (Formula.imp (Formula.not p) p)).isSome = true := wtImp hnp hp
  have hQ : (liftFormula? env Γ (Formula.not (Formula.imp (Formula.not p) p))).isSome = true :=
    wtNot hY
  have hF : PPTerm env Γ Δ (Formula.imp (Formula.not p)
      (Formula.imp p (Formula.not (Formula.imp (Formula.not p) p)))) := PPTerm.pEF hp hQ
  have hS1 := PPTerm.axS (Δ := Δ) (φ := Formula.not p) (ψ := p)
    (χ := Formula.not (Formula.imp (Formula.not p) p)) hnp hp hQ
  have hP1 : PPTerm env Γ Δ (Formula.imp (Formula.imp (Formula.not p) p)
      (Formula.imp (Formula.not p) (Formula.not (Formula.imp (Formula.not p) p)))) :=
    PPTerm.mp (wtImp hnp (wtImp hp hQ)) hS1 hF
  have hP2 : PPTerm env Γ Δ (Formula.imp
      (Formula.imp (Formula.not p) (Formula.not (Formula.imp (Formula.not p) p)))
      (Formula.imp (Formula.imp (Formula.not p) p) p)) := PPTerm.axCP hY hp
  have hP3 : PPTerm env Γ Δ (Formula.imp (Formula.imp (Formula.not p) p)
      (Formula.imp (Formula.imp (Formula.not p) p) p)) :=
    PPTerm.pImpTrans hY (wtImp hnp hQ) (wtImp hY hp) hP1 hP2
  have hS2 := PPTerm.axS (Δ := Δ) (φ := Formula.imp (Formula.not p) p)
    (ψ := Formula.imp (Formula.not p) p) (χ := p) hY hY hp
  exact PPTerm.mp (wtImp hY hY)
    (PPTerm.mp (wtImp hY (wtImp hY hp)) hS2 hP3) (PPTerm.pImpId hY)

/-- Double-negation elimination certificate: `⊢ ¬¬p → p`. -/
def PPTerm.pDNE {p : Formula} (hp : (liftFormula? env Γ p).isSome = true) :
    PPTerm env Γ Δ (Formula.imp (Formula.not (Formula.not p)) p) := by
  have hnp := wtNot hp
  have hnnp := wtNot hnp
  have hstar : PPTerm env Γ (Formula.not (Formula.not p) :: Δ)
      (Formula.imp (Formula.not (Formula.not p)) (Formula.imp (Formula.not p) p)) :=
    PPTerm.pEF hnp hp
  have hh : PPTerm env Γ (Formula.not (Formula.not p) :: Δ) (Formula.not (Formula.not p)) :=
    PPTerm.hyp (by simp)
  have hd : PPTerm env Γ (Formula.not (Formula.not p) :: Δ) (Formula.imp (Formula.not p) p) :=
    PPTerm.mp hnnp hstar hh
  have hres : PPTerm env Γ (Formula.not (Formula.not p) :: Δ) p :=
    PPTerm.mp (wtImp hnp hp) (PPTerm.pCM hp) hd
  exact PPTerm.impIntro hnnp hres

/-- Reductio certificate: from `φ ⊢ ψ` and `φ ⊢ ¬ψ` conclude `⊢ ¬φ`. -/
def PPTerm.pRaa {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hp : PPTerm env Γ (φ :: Δ) ψ) (hn : PPTerm env Γ (φ :: Δ) (Formula.not ψ)) :
    PPTerm env Γ Δ (Formula.not φ) := by
  have hnφ := wtNot hφ
  have hnψ := wtNot hψ
  have hself : PPTerm env Γ (φ :: Δ) (Formula.not φ) := by
    have hef : PPTerm env Γ (φ :: Δ)
        (Formula.imp (Formula.not ψ) (Formula.imp ψ (Formula.not φ))) := PPTerm.pEF hψ hnφ
    exact PPTerm.mp hψ (PPTerm.mp hnψ hef hn) hp
  have hSR : PPTerm env Γ Δ (Formula.imp φ (Formula.not φ)) :=
    PPTerm.impIntro hφ hself
  have hSR' : PPTerm env Γ Δ (Formula.imp (Formula.not (Formula.not φ)) (Formula.not φ)) :=
    PPTerm.pImpTrans (wtNot hnφ) hφ hnφ (PPTerm.pDNE hφ) hSR
  exact PPTerm.mp (wtImp (wtNot hnφ) hnφ) (PPTerm.pCM hnφ) hSR'

/-- Assumption-list monotonicity for certificates, by structural recursion so it
    stays computable (the `induction` tactic would emit `PPTerm.rec`, which the
    code generator rejects for `Type`-valued targets). -/
def PPTerm.pMono : {Δ Δ' : List Formula} -> (∀ x, x ∈ Δ -> x ∈ Δ') ->
    {φ : Formula} -> PPTerm env Γ Δ φ -> PPTerm env Γ Δ' φ
  | _, _, hsub, _, .hyp hmem => PPTerm.hyp (hsub _ hmem)
  | _, _, hsub, _, .impIntro hwt t =>
      PPTerm.impIntro hwt (PPTerm.pMono (fun x hx => by
        rcases List.mem_cons.1 hx with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub _ h)) t)
  | _, _, hsub, _, .mp hwt t u => PPTerm.mp hwt (PPTerm.pMono hsub t) (PPTerm.pMono hsub u)
  | _, _, _, _, .axK h1 h2 => PPTerm.axK h1 h2
  | _, _, _, _, .axS h1 h2 h3 => PPTerm.axS h1 h2 h3
  | _, _, _, _, .axCP h1 h2 => PPTerm.axCP h1 h2
  | _, _, _, _, .axAndL h1 h2 => PPTerm.axAndL h1 h2
  | _, _, _, _, .axAndR h1 h2 => PPTerm.axAndR h1 h2
  | _, _, _, _, .axAndI h1 h2 => PPTerm.axAndI h1 h2
  | _, _, _, _, .axOrL h1 h2 => PPTerm.axOrL h1 h2
  | _, _, _, _, .axOrR h1 h2 => PPTerm.axOrR h1 h2
  | _, _, _, _, .axOrE h1 h2 h3 => PPTerm.axOrE h1 h2 h3
  | _, _, _, _, .axIffI h1 h2 => PPTerm.axIffI h1 h2
  | _, _, _, _, .axIffL h1 h2 => PPTerm.axIffL h1 h2
  | _, _, _, _, .axIffR h1 h2 => PPTerm.axIffR h1 h2

/-- Proof-by-cases certificate: if `χ` follows from `φ` and from `¬φ`, it holds. -/
def PPTerm.pByCases {φ χ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hχ : (liftFormula? env Γ χ).isSome = true)
    (h1 : PPTerm env Γ (φ :: Δ) χ) (h2 : PPTerm env Γ (Formula.not φ :: Δ) χ) :
    PPTerm env Γ Δ χ := by
  have hnφ := wtNot hφ
  have hnχ := wtNot hχ
  have h1' : PPTerm env Γ (φ :: Formula.not χ :: Δ) χ :=
    PPTerm.pMono (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) h1
  have hnχhyp : PPTerm env Γ (φ :: Formula.not χ :: Δ) (Formula.not χ) :=
    PPTerm.hyp (by simp)
  have hnφctx : PPTerm env Γ (Formula.not χ :: Δ) (Formula.not φ) :=
    PPTerm.pRaa hφ hχ h1' hnχhyp
  have h2' : PPTerm env Γ (Formula.not φ :: Formula.not χ :: Δ) χ :=
    PPTerm.pMono (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) h2
  have hB' : PPTerm env Γ (Formula.not χ :: Δ) (Formula.imp (Formula.not φ) χ) :=
    PPTerm.impIntro hnφ h2'
  have hχctx : PPTerm env Γ (Formula.not χ :: Δ) χ := PPTerm.mp hnφ hB' hnφctx
  exact PPTerm.mp (wtImp hnχ hχ) (PPTerm.pCM hχ) (PPTerm.impIntro hnχ hχctx)

/-- Inject a proved succedent member into the right-nested disjunction.  The
    branch is chosen by `DecidableEq Formula` (a `dite`), not by eliminating the
    `∈`-proof — an `Or` may not be cased into `Type`. -/
def PPTerm.pRightOr_mem {A : List Formula} : (φ : Formula) -> (Θ : List Formula) -> {ψ : Formula} ->
    ψ ∈ φ :: Θ -> PPTerm env Γ A ψ -> LiftsAllF env Γ (φ :: Θ) ->
    PPTerm env Γ A (rightOr φ Θ)
  | _, [], _, hmem, hψ, _ => List.mem_singleton.1 hmem ▸ hψ
  | φ, χ :: Θ', ψ, hmem, hψ, hall =>
      if hφeq : ψ = φ then
        PPTerm.pOrInl hall.head
          (liftFormula?_rightOr_isSome χ Θ' hall.tail.head hall.tail.tail) (hφeq ▸ hψ)
      else
        PPTerm.pOrInr hall.head
          (liftFormula?_rightOr_isSome χ Θ' hall.tail.head hall.tail.tail)
          (PPTerm.pRightOr_mem χ Θ' ((List.mem_cons.1 hmem).resolve_left hφeq) hψ hall.tail)

/-- Commutativity of `∨` for certificates. -/
def PPTerm.pOrComm {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true)
    (h : PPTerm env Γ Δ (Formula.or a b)) : PPTerm env Γ Δ (Formula.or b a) :=
  PPTerm.pOrElim ha hb (wtOr hb ha) h (PPTerm.axOrR hb ha) (PPTerm.axOrL hb ha)

/-- Left reassociation certificate: `a ∨ (b ∨ c) ⊢ (a ∨ b) ∨ c`. -/
def PPTerm.pOrAssocL {a b c : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (hc : (liftFormula? env Γ c).isSome = true)
    (h : PPTerm env Γ Δ (Formula.or a (Formula.or b c))) :
    PPTerm env Γ Δ (Formula.or (Formula.or a b) c) := by
  have hab := wtOr ha hb
  have hbc := wtOr hb hc
  have hT := wtOr hab hc
  have iaT : PPTerm env Γ Δ (Formula.imp a (Formula.or (Formula.or a b) c)) :=
    PPTerm.pImpTrans ha hab hT (PPTerm.axOrL ha hb) (PPTerm.axOrL hab hc)
  have ibT : PPTerm env Γ Δ (Formula.imp b (Formula.or (Formula.or a b) c)) :=
    PPTerm.pImpTrans hb hab hT (PPTerm.axOrR ha hb) (PPTerm.axOrL hab hc)
  have icT : PPTerm env Γ Δ (Formula.imp c (Formula.or (Formula.or a b) c)) :=
    PPTerm.axOrR hab hc
  have ibcT : PPTerm env Γ Δ (Formula.imp (Formula.or b c) (Formula.or (Formula.or a b) c)) :=
    PPTerm.mp (wtImp hc hT)
      (PPTerm.mp (wtImp hb hT) (PPTerm.axOrE hb hc hT) ibT) icT
  exact PPTerm.pOrElim ha hbc hT h iaT ibcT

/-- Cut an `∧` hypothesis to its two components (certificate). -/
def PPTerm.pAndLcut {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (h : PPTerm env Γ (φ :: ψ :: A) T) :
    PPTerm env Γ (Formula.and φ ψ :: A) T := by
  have h1 : PPTerm env Γ (ψ :: A) (Formula.imp φ T) := PPTerm.impIntro hφ h
  have h2 : PPTerm env Γ A (Formula.imp ψ (Formula.imp φ T)) := PPTerm.impIntro hψ h1
  have h2w : PPTerm env Γ (Formula.and φ ψ :: A) (Formula.imp ψ (Formula.imp φ T)) :=
    PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) h2
  have hand : PPTerm env Γ (Formula.and φ ψ :: A) (Formula.and φ ψ) := PPTerm.hyp (by simp)
  have hφp : PPTerm env Γ (Formula.and φ ψ :: A) φ :=
    PPTerm.mp (wtAnd hφ hψ) (PPTerm.axAndL hφ hψ) hand
  have hψp : PPTerm env Γ (Formula.and φ ψ :: A) ψ :=
    PPTerm.mp (wtAnd hφ hψ) (PPTerm.axAndR hφ hψ) hand
  exact PPTerm.mp hφ (PPTerm.mp hψ h2w hψp) hφp

/-- Cut the two case-branches of an `∨` hypothesis into a common goal (certificate). -/
def PPTerm.pOrLcut {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hT : (liftFormula? env Γ T).isSome = true)
    (h1 : PPTerm env Γ (φ :: A) T) (h2 : PPTerm env Γ (ψ :: A) T) :
    PPTerm env Γ (Formula.or φ ψ :: A) T := by
  have hl : PPTerm env Γ (Formula.or φ ψ :: A) (Formula.imp φ T) :=
    PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) (PPTerm.impIntro hφ h1)
  have hr : PPTerm env Γ (Formula.or φ ψ :: A) (Formula.imp ψ T) :=
    PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) (PPTerm.impIntro hψ h2)
  have hor : PPTerm env Γ (Formula.or φ ψ :: A) (Formula.or φ ψ) := PPTerm.hyp (by simp)
  exact PPTerm.pOrElim hφ hψ hT hor hl hr

/-- Cut an `iff` hypothesis to its two directional implications (certificate). -/
def PPTerm.pIffLcut {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (h : PPTerm env Γ (Formula.imp φ ψ :: Formula.imp ψ φ :: A) T) :
    PPTerm env Γ (Formula.iff φ ψ :: A) T := by
  have hfwd := wtImp hφ hψ
  have hrev := wtImp hψ hφ
  have h1 : PPTerm env Γ (Formula.imp ψ φ :: A)
      (Formula.imp (Formula.imp φ ψ) T) := PPTerm.impIntro hfwd h
  have h2 : PPTerm env Γ A
      (Formula.imp (Formula.imp ψ φ) (Formula.imp (Formula.imp φ ψ) T)) :=
    PPTerm.impIntro hrev h1
  have h2w := PPTerm.pMono (env := env) (Γ := Γ)
    (Δ := A) (Δ' := Formula.iff φ ψ :: A)
    (fun x hx => List.mem_cons_of_mem _ hx) h2
  have hiff : PPTerm env Γ (Formula.iff φ ψ :: A) (Formula.iff φ ψ) :=
    PPTerm.hyp (by simp)
  have hfwdp : PPTerm env Γ (Formula.iff φ ψ :: A) (Formula.imp φ ψ) :=
    PPTerm.mp (wtIff hφ hψ) (PPTerm.axIffL hφ hψ) hiff
  have hrevp : PPTerm env Γ (Formula.iff φ ψ :: A) (Formula.imp ψ φ) :=
    PPTerm.mp (wtIff hφ hψ) (PPTerm.axIffR hφ hψ) hiff
  exact PPTerm.mp hfwd (PPTerm.mp hrev h2w hrevp) hfwdp

/-! ## The reified compile target and the witness-based refuted branch

    `ReifiedDenote` is the `Type`-valued analogue of `denote`.  The crucial design
    point (see `proof_search.md`): the refuted branch (empty succedent) is *not* a
    "prove-any-query" function — that representation makes `negR` instantiate its
    premise at both `φ` and `¬φ`, compounding to an exponential certificate.  It
    is instead an **explicit contradiction witness** `Contradiction`, from which
    `negR` reads off `pRaa` directly (each cert used once, `negR` linear) and any
    query is `explode`d in `O(1)` — and the witness formula is always an
    antecedent-subformula, so it stays inside `SearchClosure(G)`. -/

/-- An explicit contradiction in context `A`: a witness formula and certificates
    of both it and its negation.  This is the `Type`-valued meaning of the
    ⊥-free refuted branch. -/
structure Contradiction (env : Env) (Γ : Ctx) (A : List Formula) : Type where
  witness : Formula
  wwt : (liftFormula? env Γ witness).isSome = true
  pos : PPTerm env Γ A witness
  neg : PPTerm env Γ A (Formula.not witness)

/-- Explode a contradiction to any well-typed query, in `O(1)` over the witness. -/
def Contradiction.explode {A : List Formula} (c : Contradiction env Γ A)
    {χ : Formula} (hχ : (liftFormula? env Γ χ).isSome = true) : PPTerm env Γ A χ :=
  PPTerm.mp c.wwt (PPTerm.mp (wtNot c.wwt) (PPTerm.pEF c.wwt hχ) c.neg) c.pos

/-- Reified denotation: a certificate for a nonempty succedent, an explicit
    contradiction for the refuted (empty) branch. -/
def ReifiedDenote (env : Env) (Γ : Ctx) : FSequent -> Type
  | ⟨A, []⟩ => Contradiction env Γ A
  | ⟨A, φ :: Θ⟩ => PPTerm env Γ A (rightOr φ Θ)

/-- Compile a search trace to a reified certificate.  Mirrors `analyticSound`
    rule-for-rule, but produces certificate data and uses the contradiction
    witness for the refuted branch. -/
def compile {env : Env} {Γ : Ctx} : {S : FSequent} -> FTrace env Γ S -> ReifiedDenote env Γ S
  | _, .id (S := S) (φ := φ) hA hS hall =>
      match S, hS, hall with
      | s0 :: S', hS, hall => PPTerm.pRightOr_mem s0 S' hS (PPTerm.hyp hA) hall
  | _, .negR (Θ := Θ) (φ := φ) hφ hΘ t =>
      match Θ, hΘ with
      | [], _ => let c := compile t; PPTerm.pRaa hφ c.wwt c.pos c.neg
      | χ0 :: Θ', hΘ =>
          let ih := compile t
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          PPTerm.pByCases hφ (wtOr (wtNot hφ) hR)
            (PPTerm.pOrInr (wtNot hφ) hR ih)
            (PPTerm.pOrInl (wtNot hφ) hR (PPTerm.hyp (by simp)))
  | _, .negL (Θ := Θ) (φ := φ) hφ hΘ t =>
      match Θ, hΘ with
      | [], _ =>
          let ih := compile t
          ⟨φ, hφ, PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) ih, PPTerm.hyp (by simp)⟩
      | χ0 :: Θ', hΘ =>
          let ih := compile t
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          let ihw := PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) ih
          let hl := PPTerm.mp (wtNot hφ) (PPTerm.pEF hφ hR) (PPTerm.hyp (by simp))
          PPTerm.pOrElim hφ hR hR ihw hl (PPTerm.pImpId hR)
  | _, .impR (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ hΘ t =>
      match Θ, hΘ with
      | [], _ => let ihp := compile t; PPTerm.impIntro hφ ihp
      | χ0 :: Θ', hΘ =>
          let ihp := compile t
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          PPTerm.pByCases hφ (wtOr (wtImp hφ hψ) hR)
            (let hl := PPTerm.impIntro hψ
                (PPTerm.pOrInl (wtImp hφ hψ) hR (PPTerm.pImpK hφ hψ (PPTerm.hyp (by simp))))
             let hr := PPTerm.axOrR (wtImp hφ hψ) hR
             PPTerm.pOrElim hψ hR (wtOr (wtImp hφ hψ) hR) ihp hl hr)
            (PPTerm.pOrInl (wtImp hφ hψ) hR
              (PPTerm.mp (wtNot hφ) (PPTerm.pEF hφ hψ) (PPTerm.hyp (by simp))))
  | _, .impL (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ hΘ t u =>
      match Θ, hΘ with
      | [], _ =>
          let ih1 := compile t
          let cu := compile u
          let dφ := PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) ih1
          let dψ := PPTerm.mp hφ (PPTerm.hyp (by simp)) dφ
          let posρ := PPTerm.mp hψ
            (PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) (PPTerm.impIntro hψ cu.pos)) dψ
          let negρ := PPTerm.mp hψ
            (PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) (PPTerm.impIntro hψ cu.neg)) dψ
          ⟨cu.witness, cu.wwt, posρ, negρ⟩
      | χ0 :: Θ', hΘ =>
          let ih1 := compile t
          let ih2 := compile u
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          let ih1w := PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) ih1
          let hl := PPTerm.impIntro hφ
            (let hψp := PPTerm.mp hφ (PPTerm.hyp (by simp)) (PPTerm.hyp (by simp))
             let h2 := PPTerm.pMono
               (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
               (PPTerm.impIntro hψ ih2)
             PPTerm.mp hψ h2 hψp)
          PPTerm.pOrElim hφ hR hR ih1w hl (PPTerm.pImpId hR)
  | _, .andR (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ hΘ t u =>
      match Θ, hΘ with
      | [], _ =>
          let ih1p := compile t
          let ih2p := compile u
          PPTerm.mp hψ (PPTerm.mp hφ (PPTerm.axAndI hφ hψ) ih1p) ih2p
      | χ0 :: Θ', hΘ =>
          let ih1p := compile t
          let ih2p := compile u
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          let hgoalwt := wtOr (wtAnd hφ hψ) hR
          let hlouter := PPTerm.impIntro hφ
            (let ih2w := PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) ih2p
             let hlin := PPTerm.impIntro hψ
               (let hand := PPTerm.mp hψ
                   (PPTerm.mp hφ (PPTerm.axAndI hφ hψ) (PPTerm.hyp (by simp))) (PPTerm.hyp (by simp))
                PPTerm.pOrInl (wtAnd hφ hψ) hR hand)
             let hrin := PPTerm.axOrR (wtAnd hφ hψ) hR
             PPTerm.pOrElim hψ hR hgoalwt ih2w hlin hrin)
          let hrouter := PPTerm.axOrR (wtAnd hφ hψ) hR
          PPTerm.pOrElim hφ hR hgoalwt ih1p hlouter hrouter
  | _, .andL (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ t =>
      match Θ with
      | [] =>
          let c := compile t
          ⟨c.witness, c.wwt, PPTerm.pAndLcut hφ hψ c.pos, PPTerm.pAndLcut hφ hψ c.neg⟩
      | _ :: _ => let ih := compile t; PPTerm.pAndLcut hφ hψ ih
  | _, .orR (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ hΘ t =>
      match Θ, hΘ with
      | [], _ => (compile t : PPTerm env Γ _ (Formula.or φ ψ))
      | χ0 :: Θ', hΘ =>
          let ihp := compile t
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          PPTerm.pOrAssocL hφ hψ hR ihp
  | _, .orL (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ hΘ t u =>
      match Θ, hΘ with
      | [], _ =>
          let c1 := compile t
          let c2 := compile u
          ⟨c1.witness, c1.wwt,
           PPTerm.pOrLcut hφ hψ c1.wwt c1.pos (c2.explode c1.wwt),
           PPTerm.pOrLcut hφ hψ (wtNot c1.wwt) c1.neg (c2.explode (wtNot c1.wwt))⟩
      | χ0 :: Θ', hΘ =>
          let ih1 := compile t
          let ih2 := compile u
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          PPTerm.pOrLcut hφ hψ hR ih1 ih2
  | _, .iffR (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ hΘ t u =>
      match Θ, hΘ with
      | [], _ =>
          let ih1p := compile t
          let ih2p := compile u
          PPTerm.mp (wtImp hψ hφ)
            (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ) ih1p) ih2p
      | χ0 :: Θ', hΘ =>
          let ih1p := compile t
          let ih2p := compile u
          let hR := liftFormula?_rightOr_isSome χ0 Θ' hΘ.head hΘ.tail
          let hgoalwt := wtOr (wtIff hφ hψ) hR
          let hlouter := PPTerm.impIntro (wtImp hφ hψ)
            (let ih2w := PPTerm.pMono (fun x hx => List.mem_cons_of_mem _ hx) ih2p
             let hlin := PPTerm.impIntro (wtImp hψ hφ)
               (let hiffp := PPTerm.mp (wtImp hψ hφ)
                   (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ) (PPTerm.hyp (by simp)))
                   (PPTerm.hyp (by simp))
                PPTerm.pOrInl (wtIff hφ hψ) hR hiffp)
             let hrin := PPTerm.axOrR (wtIff hφ hψ) hR
             PPTerm.pOrElim (wtImp hψ hφ) hR hgoalwt ih2w hlin hrin)
          let hrouter := PPTerm.axOrR (wtIff hφ hψ) hR
          PPTerm.pOrElim (wtImp hφ hψ) hR hgoalwt ih1p hlouter hrouter
  | _, .iffL (Θ := Θ) (φ := φ) (ψ := ψ) hφ hψ t =>
      match Θ with
      | [] =>
          let c := compile t
          ⟨c.witness, c.wwt, PPTerm.pIffLcut hφ hψ c.pos, PPTerm.pIffLcut hφ hψ c.neg⟩
      | _ :: _ => let ih := compile t; PPTerm.pIffLcut hφ hψ ih

/-- The reified compiler is sound: a singleton-succedent trace compiles to a
    `PPTerm` certificate that erases to genuine M3 `Proves` evidence.  This is the
    certificate-carrying analogue of `analyticSoundSingle`. -/
theorem compileSoundSingle {A : List Formula} {φ : Formula}
    (t : FTrace env Γ ⟨A, [φ]⟩) : Proves env Γ A φ :=
  ProvesProp.toProves (PPTerm.toProvesProp (compile t : PPTerm env Γ A φ))

/-! ## Assumption discharge — making key reuse a real, checked operation

    The replay cache key of a node `PPTerm Γ Δ φ` is the *assumption-discharged*
    conclusion `dischargeKey Δ φ` (the deduction-theorem normal form; still open
    over the fixed contextual variables in `Γ`, hence "closed w.r.t. assumptions",
    not absolutely closed).  For that key to certify genuine reuse we must exhibit
    the two transport operations, so that a memoizing replayer can prove the key
    once and re-apply it in any context where the node recurs:

    * `discharge`   : `LiftsAllF Γ Δ → PPTerm Γ Δ φ → PPTerm Γ [] (dischargeKey Δ φ)`
    * `instantiate` : `LiftsAllF Γ Δ → PPTerm Γ [] (dischargeKey Δ φ) → PPTerm Γ Δ φ`

    Both are `sorry`-free structural functions.  `discharge` iterates `impIntro`
    (needing each antecedent well typed — `PPTerm` does *not* itself enforce that
    unused antecedents lift, which is exactly what `LiftsAllF Γ Δ` supplies).
    `instantiate` weakens the closed proof back under `Δ` and re-applies the
    hypotheses by `mp`. -/

/-- Assumption-discharged conclusion: the deduction-theorem normal form of
    `Δ ⊢ φ`, folding each assumption into an implication.  Matching iterated
    `impIntro` (which peels the list *head* first), the head — the
    most-recently-added assumption — ends up *innermost*: e.g.
    `dischargeKey [a, b] φ = b → (a → φ)`. -/
def dischargeKey : List Formula -> Formula -> Formula
  | [], φ => φ
  | a :: as, φ => dischargeKey as (Formula.imp a φ)

/-- Type-level assumption weakening (the `PPTerm` analogue of `pMono`): a
    certificate valid under `Δ` is valid under any `Δ'` containing `Δ`. -/
def PPTerm.weaken {env : Env} {Γ : Ctx} : {Δ Δ' : List Formula} -> {φ : Formula} ->
    (∀ x, x ∈ Δ -> x ∈ Δ') -> PPTerm env Γ Δ φ -> PPTerm env Γ Δ' φ
  | _, _, _, hsub, .hyp hmem => .hyp (hsub _ hmem)
  | _, _, _, hsub, .impIntro hwt t =>
      .impIntro hwt (t.weaken (fun x hx => by
        rcases List.mem_cons.1 hx with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub _ h)))
  | _, _, _, hsub, .mp hwt t u => .mp hwt (t.weaken hsub) (u.weaken hsub)
  | _, _, _, _, .axK h1 h2 => .axK h1 h2
  | _, _, _, _, .axS h1 h2 h3 => .axS h1 h2 h3
  | _, _, _, _, .axCP h1 h2 => .axCP h1 h2
  | _, _, _, _, .axAndL h1 h2 => .axAndL h1 h2
  | _, _, _, _, .axAndR h1 h2 => .axAndR h1 h2
  | _, _, _, _, .axAndI h1 h2 => .axAndI h1 h2
  | _, _, _, _, .axOrL h1 h2 => .axOrL h1 h2
  | _, _, _, _, .axOrR h1 h2 => .axOrR h1 h2
  | _, _, _, _, .axOrE h1 h2 h3 => .axOrE h1 h2 h3
  | _, _, _, _, .axIffI h1 h2 => .axIffI h1 h2
  | _, _, _, _, .axIffL h1 h2 => .axIffL h1 h2
  | _, _, _, _, .axIffR h1 h2 => .axIffR h1 h2

/-- Discharge every assumption of a certificate into the closed key, by iterated
    `impIntro`.  `LiftsAllF Γ Δ` provides the per-antecedent well-typedness that
    `impIntro` demands. -/
def PPTerm.discharge {env : Env} {Γ : Ctx} : (Δ : List Formula) -> {φ : Formula} ->
    LiftsAllF env Γ Δ -> PPTerm env Γ Δ φ -> PPTerm env Γ [] (dischargeKey Δ φ)
  | [], _, _, t => t
  | _ :: as, _, hwt, t =>
      PPTerm.discharge as hwt.tail (PPTerm.impIntro hwt.head t)

/-- Re-instantiate a discharged (closed-w.r.t.-assumptions) certificate back
    under its assumption list `Δ`: weaken the closed proof into `Δ` and re-apply
    each hypothesis by `mp`.  The inverse direction to `discharge`, so together
    they make cache-key reuse a type-checked round trip. -/
def PPTerm.instantiate {env : Env} {Γ : Ctx} : (Δ : List Formula) -> {φ : Formula} ->
    LiftsAllF env Γ Δ -> PPTerm env Γ [] (dischargeKey Δ φ) -> PPTerm env Γ Δ φ
  | [], _, _, t => t
  | a :: as, φ, hwt, t =>
      let inner : PPTerm env Γ as (Formula.imp a φ) :=
        PPTerm.instantiate as hwt.tail t
      PPTerm.mp hwt.head
        (inner.weaken (fun _ hx => List.mem_cons_of_mem _ hx))
        (PPTerm.hyp List.mem_cons_self)

/-! ## Antecedent well-typedness invariant — every node key is dischargeable

    `discharge`/`instantiate` need `LiftsAllF Γ Δ` at the node's context `Δ`.  A
    bare `PPTerm` does not carry a *global* antecedent invariant, so to certify
    that `replayCost (compile t)` counts genuinely reusable keys — not just keys
    for which someone manually supplied typing evidence — we must show that a
    well-typed *root* context forces every node's context to be well typed.

    This is purely structural: the only context-growing constructor, `impIntro`,
    already carries the `isSome` witness for the formula it adds (line 194), so a
    node's context is always the root context extended by certified formulas.
    `PPTerm.ctxsWT` propagates `LiftsAllF` from the root to every node; because it
    quantifies over *all* `PPTerm` values it applies verbatim to certificates
    built through `pMono`/`pRightOr_mem` — no need to unfold those combinators,
    only to know the resulting node's context lifts.  `compileCtxsWT` then hands
    the search layer the invariant for actual traces, given the (search-supplied,
    trivial at the empty top goal) root antecedent typing `LiftsAllF Γ A`. -/

/-- Every node context in the certificate is `LiftsAllF`-well-typed.  Leaves
    assert it for their own context; `impIntro`/`mp` additionally require it of
    their children. -/
def PPTerm.CtxsWT {env : Env} {Γ : Ctx} : {Δ : List Formula} -> {φ : Formula} ->
    PPTerm env Γ Δ φ -> Prop
  | Δ, _, .hyp _ => LiftsAllF env Γ Δ
  | Δ, _, .impIntro _ t => LiftsAllF env Γ Δ ∧ t.CtxsWT
  | Δ, _, .mp _ t u => LiftsAllF env Γ Δ ∧ t.CtxsWT ∧ u.CtxsWT
  | Δ, _, .axK _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axS _ _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axCP _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axAndL _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axAndR _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axAndI _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axOrL _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axOrR _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axOrE _ _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axIffI _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axIffL _ _ => LiftsAllF env Γ Δ
  | Δ, _, .axIffR _ _ => LiftsAllF env Γ Δ

/-- A well-typed root context propagates to every node.  Structural on the term:
    `impIntro` extends the context by a formula whose `isSome` witness the
    constructor already carries, so `LiftsAllF.cons` re-establishes the invariant
    for the child; `mp` reuses the same context for both children. -/
theorem PPTerm.ctxsWT {env : Env} {Γ : Ctx} : {Δ : List Formula} -> {φ : Formula} ->
    (t : PPTerm env Γ Δ φ) -> LiftsAllF env Γ Δ -> t.CtxsWT := by
  intro Δ φ t
  induction t with
  | impIntro hwt t ih => intro h; exact ⟨h, ih (LiftsAllF.cons hwt h)⟩
  | mp hwt t u iht ihu => intro h; exact ⟨h, iht h, ihu h⟩
  | _ => intro h; exact h

/-- The invariant for actual compiled search traces: a well-typed root antecedent
    list makes every node context of `compile t` well typed — hence every node key
    is genuinely dischargeable (and instantiable).  At the top-level goal `A = []`
    the hypothesis is `LiftsAllF.nil`. -/
theorem compileCtxsWT {A : List Formula} {φ : Formula}
    (t : FTrace env Γ ⟨A, [φ]⟩) (hA : LiftsAllF env Γ A) :
    (compile t : PPTerm env Γ A φ).CtxsWT :=
  PPTerm.ctxsWT _ hA

/-! ## Replay cost under sharing (the context-discharged memoized model)

    The naive tree measure `PPTerm.size` is *not* polynomial: the empty-succedent
    `impL` and `orL` branches of `compile` embed one child certificate in both the
    positive and negative halves of the produced `Contradiction`, so a chain of
    such rules doubles the tree at every level (`S(d) = 2·S(d-1)+O(1) = 2^d`).

    Sharing rescues this only under an **honest, checked** cost model — a Lean
    `let` that shares a value at *evaluation* time gives neither shared Core proof
    syntax nor a memoizing replayer, so on its own it does not discharge the
    tree bound.  The correct model is a memoizing replay whose cache key is the
    *fully context-discharged* conclusion of each node: a node `PPTerm Γ Δ φ`
    replays the closed theorem `Δ ⊢ φ` in deduction-theorem normal form, i.e. the
    single closed formula `dischargeKey Δ φ`.  Two nodes are the same replayable
    sub-theorem exactly when this closed formula agrees — so keying on the bare
    conclusion `φ` (ignoring `Δ`) is *unsound* (it conflates `a ⊢ φ` with `⊢ φ`).
    Reuse of this key is a real, checked operation: `PPTerm.discharge` /
    `PPTerm.instantiate` transport a certificate to its closed key and back.
    `PPTerm.nodeKeys` records the discharged conclusion of every node.
    `replayCost` is the number of distinct keys and is the checked target metric
    for a future memoizing replayer. It is not yet an achieved replay cost because
    no memo table or shared Core-emission graph has been implemented.

    The context-transport gate is now proved using root-relative `ReplayShape`
    values (introduced assumptions plus node conclusion). `nodeKeys` is exactly
    those shapes rendered against the root assumption context. `pMono` preserves
    the complete shape list, hence also `shapeCost`, exactly. `pRightOr_mem`
    never duplicates its input certificate and adds at most two nodes/shapes per
    inspected succedent position. Thus these two transport operations are not an
    exponential multiplier.

    Polynomial `replayCost (compile tr)` remains open at the compiler level. It
    now requires a deduplicated recurrence over all compile templates together
    with a search-trace size bound, followed by an actual memoizing replayer.
    An atom-vocabulary bound is necessary but not sufficient: discharged keys can
    carry deep administrative implication/disjunction shapes, so the remaining
    theorem must bound context-aware keys themselves. -/

/-- The list of *context-discharged* conclusion keys of every node in a
    certificate.  A node `PPTerm Γ Δ φ` contributes the closed formula
    `dischargeKey Δ φ` — the deduction-theorem normal form of the sub-theorem it
    proves — so that the key faithfully distinguishes `a ⊢ φ` from `⊢ φ`.  A
    memoizing replayer proves each *distinct* key once.  Constructor arguments are
    named so the conclusion is rebuilt explicitly (matching the index directly
    breaks the motive). -/
def PPTerm.nodeKeys {env : Env} : {Γ : Ctx} -> {Δ : List Formula} -> {φ : Formula} ->
    PPTerm env Γ Δ φ -> List Formula
  | _, Δ, _, .hyp (φ := φ) _ => [dischargeKey Δ φ]
  | _, Δ, _, .impIntro (φ := a) (ψ := b) _ t =>
      dischargeKey Δ (Formula.imp a b) :: t.nodeKeys
  | _, Δ, _, .mp (ψ := b) _ t u => dischargeKey Δ b :: (t.nodeKeys ++ u.nodeKeys)
  | _, Δ, _, .axK (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp a (Formula.imp b a))]
  | _, Δ, _, .axS (φ := a) (ψ := b) (χ := c) _ _ _ =>
      [dischargeKey Δ (Formula.imp (Formula.imp a (Formula.imp b c))
        (Formula.imp (Formula.imp a b) (Formula.imp a c)))]
  | _, Δ, _, .axCP (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ
        (Formula.imp (Formula.imp (Formula.not b) (Formula.not a)) (Formula.imp a b))]
  | _, Δ, _, .axAndL (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp (Formula.and a b) a)]
  | _, Δ, _, .axAndR (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp (Formula.and a b) b)]
  | _, Δ, _, .axAndI (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp a (Formula.imp b (Formula.and a b)))]
  | _, Δ, _, .axOrL (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp a (Formula.or a b))]
  | _, Δ, _, .axOrR (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp b (Formula.or a b))]
  | _, Δ, _, .axOrE (φ := a) (ψ := b) (χ := c) _ _ _ =>
      [dischargeKey Δ (Formula.imp (Formula.imp a c)
        (Formula.imp (Formula.imp b c) (Formula.imp (Formula.or a b) c)))]
  | _, Δ, _, .axIffI (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ
        (Formula.imp (Formula.imp a b) (Formula.imp (Formula.imp b a) (Formula.iff a b)))]
  | _, Δ, _, .axIffL (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp (Formula.iff a b) (Formula.imp a b))]
  | _, Δ, _, .axIffR (φ := a) (ψ := b) _ _ =>
      [dischargeKey Δ (Formula.imp (Formula.iff a b) (Formula.imp b a))]

/-! ## Exact context transport for replay keys -/

abbrev ReplayShape := Prod (List Formula) Formula

def pushReplayShape (a : Formula) (s : ReplayShape) : ReplayShape :=
  (s.1 ++ [a], s.2)

/-- Root-relative assumptions introduced by impIntro, paired with each conclusion. -/
def PPTerm.nodeShapes {env : Env} : {G : Ctx} -> {D : List Formula} ->
    {f : Formula} -> PPTerm env G D f -> List ReplayShape
  | _, _, _, @PPTerm.hyp _ _ _ f _ => [([], f)]
  | _, _, _, @PPTerm.impIntro _ _ _ a b _ t =>
      ([], Formula.imp a b) :: t.nodeShapes.map (pushReplayShape a)
  | _, _, _, @PPTerm.mp _ _ _ a b _ t u =>
      ([], b) :: (t.nodeShapes ++ u.nodeShapes)
  | _, _, _, @PPTerm.axK _ _ _ a b _ _ =>
      [([], Formula.imp a (Formula.imp b a))]
  | _, _, _, @PPTerm.axS _ _ _ a b c _ _ _ =>
      [([], Formula.imp (Formula.imp a (Formula.imp b c))
        (Formula.imp (Formula.imp a b) (Formula.imp a c)))]
  | _, _, _, @PPTerm.axCP _ _ _ a b _ _ =>
      [([], Formula.imp (Formula.imp (Formula.not b) (Formula.not a)) (Formula.imp a b))]
  | _, _, _, @PPTerm.axAndL _ _ _ a b _ _ => [([], Formula.imp (Formula.and a b) a)]
  | _, _, _, @PPTerm.axAndR _ _ _ a b _ _ => [([], Formula.imp (Formula.and a b) b)]
  | _, _, _, @PPTerm.axAndI _ _ _ a b _ _ =>
      [([], Formula.imp a (Formula.imp b (Formula.and a b)))]
  | _, _, _, @PPTerm.axOrL _ _ _ a b _ _ => [([], Formula.imp a (Formula.or a b))]
  | _, _, _, @PPTerm.axOrR _ _ _ a b _ _ => [([], Formula.imp b (Formula.or a b))]
  | _, _, _, @PPTerm.axOrE _ _ _ a b c _ _ _ =>
      [([], Formula.imp (Formula.imp a c)
        (Formula.imp (Formula.imp b c) (Formula.imp (Formula.or a b) c)))]
  | _, _, _, @PPTerm.axIffI _ _ _ a b _ _ =>
      [([], Formula.imp (Formula.imp a b)
        (Formula.imp (Formula.imp b a) (Formula.iff a b)))]
  | _, _, _, @PPTerm.axIffL _ _ _ a b _ _ =>
      [([], Formula.imp (Formula.iff a b) (Formula.imp a b))]
  | _, _, _, @PPTerm.axIffR _ _ _ a b _ _ =>
      [([], Formula.imp (Formula.iff a b) (Formula.imp b a))]

def renderReplayShape (base : List Formula) (s : ReplayShape) : Formula :=
  dischargeKey (s.1 ++ base) s.2

/-- Node keys are exactly root-relative shapes rendered over the root context. -/
theorem PPTerm.nodeKeys_eq_renderShapes {env : Env} {G : Ctx} {D : List Formula}
    {f : Formula} (t : PPTerm env G D f) :
    t.nodeKeys = t.nodeShapes.map (renderReplayShape D) := by
  induction t with
  | impIntro hwt t ih =>
      simp [PPTerm.nodeKeys, PPTerm.nodeShapes, renderReplayShape, pushReplayShape,
        ih, List.map_map, Function.comp_def, List.append_assoc]
  | mp hwt t u iht ihu =>
      simp [PPTerm.nodeKeys, PPTerm.nodeShapes, renderReplayShape, iht, ihu,
        List.map_append]
  | _ => simp [PPTerm.nodeKeys, PPTerm.nodeShapes, renderReplayShape]

/-- Assumption weakening preserves every root-relative shape exactly. -/
theorem PPTerm.nodeShapes_pMono {env : Env} {G : Ctx} {D D2 : List Formula}
    (hsub : (x : Formula) -> List.Mem x D -> List.Mem x D2)
    {f : Formula} (t : PPTerm env G D f) :
    (PPTerm.pMono hsub t).nodeShapes = t.nodeShapes := by
  induction t generalizing D2 with
  | impIntro hwt t ih =>
      simp [PPTerm.pMono, PPTerm.nodeShapes, ih]
  | mp hwt t u iht ihu =>
      simp [PPTerm.pMono, PPTerm.nodeShapes, iht, ihu]
  | _ => simp [PPTerm.pMono, PPTerm.nodeShapes]

/-- The root-relative shape list has one entry per certificate node. -/
theorem PPTerm.nodeShapes_length_eq_size {env : Env} {G : Ctx} {D : List Formula}
    {f : Formula} (t : PPTerm env G D f) :
    t.nodeShapes.length = t.size := by
  induction t with
  | impIntro hwt t ih =>
      simp [PPTerm.nodeShapes, PPTerm.size, ih]
  | mp hwt t u iht ihu =>
      simp [PPTerm.nodeShapes, PPTerm.size, iht, ihu]
  | _ => simp [PPTerm.nodeShapes, PPTerm.size]

@[simp] theorem PPTerm.size_pOrInl {env : Env} {G : Ctx} {D : List Formula}
    {a b : Formula} (ha : (liftFormula? env G a).isSome = true)
    (hb : (liftFormula? env G b).isSome = true) (t : PPTerm env G D a) :
    (PPTerm.pOrInl ha hb t).size = 1 + t.size + 1 := by
  unfold PPTerm.pOrInl
  simp [PPTerm.size]

@[simp] theorem PPTerm.size_pOrInr {env : Env} {G : Ctx} {D : List Formula}
    {a b : Formula} (ha : (liftFormula? env G a).isSome = true)
    (hb : (liftFormula? env G b).isSome = true) (t : PPTerm env G D b) :
    (PPTerm.pOrInr ha hb t).size = 1 + t.size + 1 := by
  unfold PPTerm.pOrInr
  simp [PPTerm.size]

@[simp] theorem PPTerm.size_cast {env : Env} {G : Ctx} {D : List Formula}
    {f g : Formula} (h : f = g) (t : PPTerm env G D f) :
    (h ▸ t).size = t.size := by
  cases h
  rfl

/-- Right-disjunction packing adds at most two certificate nodes per inspected
    succedent position; it never duplicates the input certificate. -/
theorem PPTerm.size_pRightOr_mem_le {env : Env} {G : Ctx} {A : List Formula} :
    (head : Formula) -> (tail : List Formula) -> {q : Formula} ->
    (hm : List.Mem q (head :: tail)) -> (t : PPTerm env G A q) ->
    (hall : LiftsAllF env G (head :: tail)) ->
    (PPTerm.pRightOr_mem head tail hm t hall).size <=
      t.size + 2 * (tail.length + 1)
  | head, [], q, hm, t, hall => by
      have hq : q = head := List.mem_singleton.1 hm
      cases hq
      change (List.mem_singleton.1 hm ▸ t).size <= t.size + 2
      have hp : List.mem_singleton.1 hm = Eq.refl head := Subsingleton.elim _ _
      cases hp
      simp
  | head, next :: tail, q, hm, t, hall => by
      simp only [PPTerm.pRightOr_mem]
      split
      case isTrue heq =>
        cases heq
        simp [rightOr, PPTerm.size_pOrInl]
        omega
      case isFalse hne =>
        have ih := PPTerm.size_pRightOr_mem_le
          (env := env) (G := G) (A := A) next tail
          ((List.mem_cons.1 hm).resolve_left hne) t hall.tail
        simp [rightOr, PPTerm.size_pOrInr]
        omega

/-- The same linear bound stated on stable replay shapes. -/
theorem PPTerm.nodeShapes_pRightOr_mem_length_le {env : Env} {G : Ctx}
    {A : List Formula} (head : Formula) (tail : List Formula) {q : Formula}
    (hm : List.Mem q (head :: tail)) (t : PPTerm env G A q)
    (hall : LiftsAllF env G (head :: tail)) :
    (PPTerm.pRightOr_mem head tail hm t hall).nodeShapes.length <=
      t.nodeShapes.length + 2 * (tail.length + 1) := by
  rw [PPTerm.nodeShapes_length_eq_size, PPTerm.nodeShapes_length_eq_size]
  exact PPTerm.size_pRightOr_mem_le head tail hm t hall

/-- Exact transport: pMono changes only the root suffix used to render shapes. -/
theorem PPTerm.nodeKeys_pMono {env : Env} {G : Ctx} {D D2 : List Formula}
    (hsub : (x : Formula) -> List.Mem x D -> List.Mem x D2)
    {f : Formula} (t : PPTerm env G D f) :
    (PPTerm.pMono hsub t).nodeKeys =
      t.nodeShapes.map (renderReplayShape D2) := by
  rw [PPTerm.nodeKeys_eq_renderShapes, PPTerm.nodeShapes_pMono]

/-- Local deduplication (no Mathlib/Batteries in this repo).  Structural on the
    list; keeps the first occurrence of each element. -/
def dedup {α : Type} [DecidableEq α] : List α -> List α
  | [] => []
  | a :: as => let d := dedup as; if a ∈ d then d else a :: d

/-- Number of distinct root-relative replay shapes. -/
def PPTerm.shapeCost {env : Env} {G : Ctx} {D : List Formula} {f : Formula}
    (t : PPTerm env G D f) : Nat :=
  (dedup t.nodeShapes).length

theorem dedup_length_le {alpha : Type} [DecidableEq alpha] (xs : List alpha) :
    (dedup xs).length <= xs.length := by
  induction xs with
  | nil => simp [dedup]
  | cons x xs ih =>
      simp only [dedup]
      split <;> simp_all
      omega

/-- `dedup` preserves membership, in both directions. -/
theorem mem_dedup {alpha : Type} [DecidableEq alpha] :
    (xs : List alpha) -> (a : alpha) -> (a ∈ dedup xs ↔ a ∈ xs)
  | [], a => by simp [dedup]
  | x :: xs, a => by
      simp only [dedup]
      have ih := mem_dedup xs
      split
      · rename_i hx
        rw [List.mem_cons]
        constructor
        · intro ha; exact Or.inr ((ih a).1 ha)
        · rintro (rfl | ha)
          · exact hx
          · exact (ih a).2 ha
      · rw [List.mem_cons, List.mem_cons]
        constructor
        · rintro (rfl | ha)
          · exact Or.inl rfl
          · exact Or.inr ((ih a).1 ha)
        · rintro (rfl | ha)
          · exact Or.inl rfl
          · exact Or.inr ((ih a).2 ha)

/-- Mapping cannot increase the number of *distinct* elements: `f` may merge
    distinct inputs but never splits them.  Hence `dedup` of the image is no
    longer than `dedup` of the source. -/
theorem dedup_map_length_le {alpha beta : Type} [DecidableEq alpha] [DecidableEq beta]
    (f : alpha -> beta) : (xs : List alpha) ->
    (dedup (xs.map f)).length <= (dedup xs).length
  | [] => by simp [dedup]
  | x :: xs => by
      simp only [List.map, dedup]
      have ih := dedup_map_length_le f xs
      by_cases hx : x ∈ dedup xs
      · rw [if_pos hx]
        have hfx : f x ∈ dedup (xs.map f) :=
          (mem_dedup (xs.map f) (f x)).2 (List.mem_map.2 ⟨x, (mem_dedup xs x).1 hx, rfl⟩)
        rw [if_pos hfx]; exact ih
      · rw [if_neg hx]
        by_cases hfx : f x ∈ dedup (xs.map f)
        · rw [if_pos hfx, List.length_cons]; omega
        · rw [if_neg hfx, List.length_cons, List.length_cons]; omega

/-! ### Distinct-count is set-determined

    The step-2(a) collapse rests on one fact: `(dedup _).length` counts a *set*,
    so duplicating a sublist (the empty-succedent double `explode`) cannot increase
    it, and an injective relabelling (the uniform `pushReplayShape` suffix push under
    `impIntro`) preserves it exactly.  These are the reusable tools; the per-rule
    `compile` recurrence below feeds subset/duplication/relabelling facts into them. -/

/-- Injective map preserves `Nodup`. -/
theorem nodup_map_of_injective {α β : Type} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) :
    (l : List α) → l.Nodup → (l.map f).Nodup
  | [], _ => by simp
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_of_injective f hf l h.2⟩
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨x, hx, hfx⟩ := hmem
      exact h.1 (hf x a hfx ▸ hx)

/-- `dedup` produces a duplicate-free list. -/
theorem dedup_nodup {α : Type} [DecidableEq α] :
    (l : List α) → (dedup l).Nodup
  | [] => by simp [dedup]
  | a :: l => by
      simp only [dedup]
      split
      · exact dedup_nodup l
      · rename_i hnm
        rw [List.nodup_cons]
        exact ⟨hnm, dedup_nodup l⟩

/-- Pigeonhole: a `Nodup` list embedded (elementwise) in another list is no longer. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    (l1 l2 : List α) → l1.Nodup → (∀ a, a ∈ l1 → a ∈ l2) →
    l1.length ≤ l2.length
  | [], l2, _, _ => by simp
  | a :: l1, l2, hnd, hsub => by
      rw [List.nodup_cons] at hnd
      have hal2 : a ∈ l2 := hsub a (by simp)
      have hsub' : ∀ x, x ∈ l1 → x ∈ l2.erase a := by
        intro x hx
        have hxa : x ≠ a := by
          intro h; exact hnd.1 (h ▸ hx)
        exact (List.mem_erase_of_ne hxa).2 (hsub x (by simp [hx]))
      have ih := nodup_length_le l1 (l2.erase a) hnd.2 hsub'
      rw [List.length_erase_of_mem hal2] at ih
      have h1 : 0 < l2.length := List.length_pos_of_mem hal2
      simp only [List.length_cons]
      omega

/-- Distinct-element count is monotone under elementwise inclusion. -/
theorem dedup_length_le_of_subset {α : Type} [DecidableEq α]
    (l1 l2 : List α) (h : ∀ a, a ∈ l1 → a ∈ l2) :
    (dedup l1).length ≤ (dedup l2).length := by
  apply nodup_length_le (dedup l1) (dedup l2) (dedup_nodup l1)
  intro a ha
  exact (mem_dedup l2 a).2 (h a ((mem_dedup l1 a).1 ha))

/-- Distinct-element count depends only on the element set. -/
theorem dedup_length_congr {α : Type} [DecidableEq α]
    (l1 l2 : List α) (h : ∀ a, a ∈ l1 ↔ a ∈ l2) :
    (dedup l1).length = (dedup l2).length :=
  Nat.le_antisymm
    (dedup_length_le_of_subset l1 l2 (fun a => (h a).1))
    (dedup_length_le_of_subset l2 l1 (fun a => (h a).2))

/-- Subadditivity of the distinct-element count over concatenation. -/
theorem dedup_append_length_le {α : Type} [DecidableEq α]
    (xs ys : List α) :
    (dedup (xs ++ ys)).length ≤ (dedup xs).length + (dedup ys).length := by
  have hsub : ∀ a, a ∈ dedup (xs ++ ys) → a ∈ dedup xs ++ dedup ys := by
    intro a ha
    have : a ∈ xs ++ ys := (mem_dedup _ a).1 ha
    rw [List.mem_append] at this ⊢
    cases this with
    | inl h => exact Or.inl ((mem_dedup xs a).2 h)
    | inr h => exact Or.inr ((mem_dedup ys a).2 h)
  have := nodup_length_le (dedup (xs ++ ys)) (dedup xs ++ dedup ys)
    (dedup_nodup _) hsub
  rw [List.length_append] at this
  exact this

/-- Duplicating a sublist does not change the distinct-element count. -/
theorem dedup_append_self_length {α : Type} [DecidableEq α] (xs : List α) :
    (dedup (xs ++ xs)).length = (dedup xs).length :=
  dedup_length_congr _ _ (fun a => by
    rw [List.mem_append]; exact ⟨fun h => h.elim id id, Or.inl⟩)

/-- An injective map preserves the distinct-element count exactly. -/
theorem dedup_map_length_of_injective {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : ∀ a b, f a = f b → a = b) (xs : List α) :
    (dedup (xs.map f)).length = (dedup xs).length := by
  refine Nat.le_antisymm (dedup_map_length_le f xs) ?_
  have hnd : ((dedup xs).map f).Nodup :=
    nodup_map_of_injective f hf _ (dedup_nodup xs)
  have hsub : ∀ b, b ∈ (dedup xs).map f → b ∈ dedup (xs.map f) := by
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact (mem_dedup (xs.map f) (f a)).2 (List.mem_map.2 ⟨a, (mem_dedup xs a).1 ha, rfl⟩)
  have := nodup_length_le ((dedup xs).map f) (dedup (xs.map f)) hnd hsub
  rw [List.length_map] at this
  exact this

/-- `dedup` grows by at most one under a cons. -/
theorem dedup_cons_length_le {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    (dedup (x :: xs)).length ≤ 1 + (dedup xs).length := by
  simp only [dedup]
  split
  · omega
  · simp [List.length_cons]; omega

/-- `pushReplayShape a` is injective. -/
theorem pushReplayShape_injective (a : Formula) :
    ∀ s s', pushReplayShape a s = pushReplayShape a s' → s = s' := by
  intro s s' h
  simp only [pushReplayShape, Prod.mk.injEq] at h
  have h1 := List.append_cancel_right h.1
  exact Prod.ext h1 h.2

/-- Generic structural bound for `impIntro`: introducing an assumption adds a
    single local shape and relabels every child shape by an *injective* suffix
    push, so the distinct-shape count grows by at most one. -/
theorem PPTerm.shapeCost_impIntro_le {env : Env} {G : Ctx} {D : List Formula}
    {a b : Formula} (hwt : (liftFormula? env G a).isSome = true)
    (t : PPTerm env G (a :: D) b) :
    (PPTerm.impIntro hwt t).shapeCost ≤ 1 + t.shapeCost := by
  unfold PPTerm.shapeCost
  simp only [PPTerm.nodeShapes]
  refine Nat.le_trans (dedup_cons_length_le _ _) ?_
  rw [dedup_map_length_of_injective (pushReplayShape a) (pushReplayShape_injective a)]
  omega

/-- Generic structural bound for `mp`: the node contributes one local shape and
    the (deduplicated) union of its two premises' shapes. -/
theorem PPTerm.shapeCost_mp_le {env : Env} {G : Ctx} {D : List Formula}
    {a b : Formula} (hwt : (liftFormula? env G a).isSome = true)
    (t : PPTerm env G D (Formula.imp a b)) (u : PPTerm env G D a) :
    (PPTerm.mp hwt t u).shapeCost ≤ 1 + t.shapeCost + u.shapeCost := by
  unfold PPTerm.shapeCost
  simp only [PPTerm.nodeShapes]
  refine Nat.le_trans (dedup_cons_length_le _ _) ?_
  have := dedup_append_length_le t.nodeShapes u.nodeShapes
  omega

/-! ### The anti-doubling collapse core

    These two lemmas are the mathematical heart of step 2(a): they say that a shape
    list contained in an admin family plus some shared children is bounded by the
    admin size plus each child counted **once, deduplicated** — even when a child
    appears inside several parents.  The empty-succedent `orL`/`impL` arms embed the
    compiled second premise `c2` in *both* the positive and negative certificate (the
    double `explode`), which doubles `size`; feeding those two occurrences in as the
    shared children `X3, X4` of `collapse4` charges them once, so `shapeCost` does not
    double.  The per-arm membership plumbing that instantiates `collapse4` against the
    concrete `compile` cases is the remaining mechanical work. -/

/-- **Shared-subterm collapse** (raw-admin form).  `P`, `N` each live inside a
    bounded local family (`Apos`, `Aneg`) together with a *common* shared list `S`;
    the distinct-shape count of `P ++ N` charges `S` once, never twice. -/
theorem shared_collapse {α : Type} [DecidableEq α]
    (P N Apos Aneg S : List α)
    (hp : ∀ a, a ∈ P → a ∈ Apos ++ S)
    (hn : ∀ a, a ∈ N → a ∈ Aneg ++ S) :
    (dedup (P ++ N)).length ≤ Apos.length + Aneg.length + (dedup S).length := by
  have hsub : ∀ a, a ∈ P ++ N → a ∈ (Apos ++ Aneg) ++ S := by
    intro a ha
    rw [List.mem_append] at ha
    cases ha with
    | inl h =>
        have := hp a h
        rw [List.mem_append] at this ⊢
        rw [List.mem_append]
        cases this with
        | inl h2 => exact Or.inl (Or.inl h2)
        | inr h2 => exact Or.inr h2
    | inr h =>
        have := hn a h
        rw [List.mem_append] at this ⊢
        rw [List.mem_append]
        cases this with
        | inl h2 => exact Or.inl (Or.inr h2)
        | inr h2 => exact Or.inr h2
  have h1 := dedup_length_le_of_subset (P ++ N) ((Apos ++ Aneg) ++ S) hsub
  have h2 := dedup_append_length_le (Apos ++ Aneg) S
  have h3 := dedup_append_length_le Apos Aneg
  have h4 := dedup_length_le Apos
  have h5 := dedup_length_le Aneg
  omega

/-- **Deduped multi-child collapse.**  A shape list `L` contained in an admin family
    `A` together with four child families (each possibly of exponential raw length,
    but here counted **deduplicated**) has distinct-shape count bounded by the admin
    size plus the four deduped child counts.  When `L = pos ++ neg` and the shared
    `c2` children `X3, X4` appear inside *both* halves, they are listed once on the
    right — the anti-doubling bound for the empty-succedent arms.  `andL` is the
    `X3 = X4 = []` case. -/
theorem collapse4 {α : Type} [DecidableEq α] (L A X1 X2 X3 X4 : List α)
    (h : ∀ a, a ∈ L → a ∈ A ++ X1 ++ X2 ++ X3 ++ X4) :
    (dedup L).length ≤ A.length + (dedup X1).length + (dedup X2).length
      + (dedup X3).length + (dedup X4).length := by
  have h1 := dedup_length_le_of_subset L (A ++ X1 ++ X2 ++ X3 ++ X4) h
  have hA := dedup_length_le A
  have e1 := dedup_append_length_le (A ++ X1 ++ X2 ++ X3) X4
  have e2 := dedup_append_length_le (A ++ X1 ++ X2) X3
  have e3 := dedup_append_length_le (A ++ X1) X2
  have e4 := dedup_append_length_le A X1
  omega

/-- pMono introduces no new distinct relative replay shapes. -/
theorem PPTerm.shapeCost_pMono {env : Env} {G : Ctx} {D D2 : List Formula}
    (hsub : (x : Formula) -> List.Mem x D -> List.Mem x D2)
    {f : Formula} (t : PPTerm env G D f) :
    (PPTerm.pMono hsub t).shapeCost = t.shapeCost := by
  simp [PPTerm.shapeCost, PPTerm.nodeShapes_pMono]

/-- Conservative distinct-shape bound for right-disjunction packing. -/
theorem PPTerm.shapeCost_pRightOr_mem_le {env : Env} {G : Ctx}
    {A : List Formula} (head : Formula) (tail : List Formula) {q : Formula}
    (hm : List.Mem q (head :: tail)) (t : PPTerm env G A q)
    (hall : LiftsAllF env G (head :: tail)) :
    (PPTerm.pRightOr_mem head tail hm t hall).shapeCost <=
      t.nodeShapes.length + 2 * (tail.length + 1) := by
  unfold PPTerm.shapeCost
  exact Nat.le_trans (dedup_length_le _)
    (PPTerm.nodeShapes_pRightOr_mem_length_le head tail hm t hall)

/-- The honest memoized replay cost: the number of *distinct* context-discharged
    node keys.  This collapses the `let`-shared duplicate branches (identical
    `(Γ, Δ, φ)`, hence identical discharged key) that make `size` exponential,
    while keeping distinct-context nodes distinct.  Bounding this is the open
    replay gate (`replayClosure`). -/
def PPTerm.replayCost {env : Env} {Γ : Ctx} {Δ : List Formula} {φ : Formula}
    (t : PPTerm env Γ Δ φ) : Nat :=
  (dedup t.nodeKeys).length

/-- The advertised metric is dominated by the root-relative shape metric: within a
    single certificate every node key is `renderReplayShape D` of its shape, so
    rendering can only *merge* distinct shapes, never split them.  Hence any bound
    on `shapeCost` (which the context-transport lemmas establish — `pMono` leaves
    it exactly fixed, `pRightOr_mem` grows it only additively) transfers to
    `replayCost`. -/
theorem PPTerm.replayCost_le_shapeCost {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ : Formula} (t : PPTerm env Γ Δ φ) : t.replayCost <= t.shapeCost := by
  unfold PPTerm.replayCost PPTerm.shapeCost
  rw [PPTerm.nodeKeys_eq_renderShapes]
  exact dedup_map_length_le (renderReplayShape Δ) t.nodeShapes

/-! ### Step 2(a): the empty-succedent `orL` anti-doubling bound, concretely

    The collapse core (`collapse4`) says duplicated shape families are charged once.
    Here we *instantiate* it against the real compiler output for the empty-succedent
    `orL` arm — the arm whose double `explode` doubles `PPTerm.size` (the `2^d`
    falsifier (d)).  The payoff is a **coefficient-one** recurrence
    `shapeCost(result) ≤ 36 + shapeCost c1 + shapeCost c2`: the joint distinct-shape
    count adds only a fixed constant per node, so `shapeCost` is linear in the search
    trace even though `size` is exponential in it.  The mechanism is that the shared
    second premise `c2` is embedded in *both* certificates under the **same** injective
    `pushReplayShape ψ` transport, so its shapes form one set counted once. -/

/-- The 7 child-free admin shapes contributed by `pOrLcut` itself. -/
def orLcutAdmin (φ ψ T : Formula) : List ReplayShape :=
  [([], T), ([], (φ.or ψ).imp T), ([], (ψ.imp T).imp ((φ.or ψ).imp T)),
   ([], (φ.imp T).imp ((ψ.imp T).imp ((φ.or ψ).imp T))), ([], φ.imp T),
   ([], ψ.imp T), ([], φ.or ψ)]

/-- Every relative shape of a `pOrLcut` node lands in its fixed admin family or in a
    `push`-transported copy of one of the two premise families. -/
theorem pOrLcut_nodeShapes_subset {env : Env} {Γ : Ctx} {A : List Formula} {T φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hT : (liftFormula? env Γ T).isSome = true)
    (h1 : PPTerm env Γ (φ :: A) T) (h2 : PPTerm env Γ (ψ :: A) T) :
    (PPTerm.pOrLcut hφ hψ hT h1 h2).nodeShapes ⊆
      orLcutAdmin φ ψ T ++ h1.nodeShapes.map (pushReplayShape φ)
        ++ h2.nodeShapes.map (pushReplayShape ψ) := by
  simp only [PPTerm.pOrLcut, PPTerm.pOrElim, PPTerm.nodeShapes, PPTerm.nodeShapes_pMono,
    orLcutAdmin]
  intro a ha
  simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
  grind

/-- The child-free admin shapes of `Contradiction.explode` at query `χ`. -/
def explodeAdmin {env : Env} {Γ : Ctx} {A : List Formula}
    (c : Contradiction env Γ A) {χ : Formula} (hχ : (liftFormula? env Γ χ).isSome = true) :
    List ReplayShape :=
  ([], χ) :: ([], c.witness.imp χ) :: (PPTerm.pEF (Δ := A) c.wwt hχ).nodeShapes

/-- Every relative shape of an `explode` node lands in its fixed admin family or in the
    contradiction's own `pos`/`neg` families (no `push`, same context). -/
theorem explode_nodeShapes_subset {env : Env} {Γ : Ctx} {A : List Formula}
    (c : Contradiction env Γ A) {χ : Formula} (hχ : (liftFormula? env Γ χ).isSome = true) :
    (c.explode hχ).nodeShapes ⊆
      explodeAdmin c hχ ++ c.neg.nodeShapes ++ c.pos.nodeShapes := by
  simp only [Contradiction.explode, PPTerm.nodeShapes, explodeAdmin]
  intro a ha
  simp only [List.mem_append, List.mem_cons] at ha ⊢
  grind

/-- The honest joint distinct-shape count of a contradiction: the number of distinct
    relative replay shapes across *both* certificates deduped together.  Deduping
    `pos` and `neg` jointly is what lets the shared, identically-transported second
    premise be counted once (not once per certificate). -/
def Contradiction.shapeCost {env : Env} {Γ : Ctx} {A : List Formula}
    (c : Contradiction env Γ A) : Nat :=
  (dedup (c.pos.nodeShapes ++ c.neg.nodeShapes)).length

/-- **The single distinct-shape measure on a reified certificate.**  It dispatches on
    the succedent so that the eventual compiler induction `shapeCost (compile tr) ≤ K *
    trSize` has *one* statement covering both the refuted (empty-succedent, a
    `Contradiction` scored jointly) and the derived (nonempty-succedent, a single
    `PPTerm`) branches. -/
def ReifiedDenote.shapeCost {env : Env} {Γ : Ctx} :
    {S : FSequent} -> ReifiedDenote env Γ S -> Nat
  | ⟨_, []⟩, c => Contradiction.shapeCost c
  | ⟨_, _ :: _⟩, t => PPTerm.shapeCost t

/-- **Empty-succedent `orL` anti-doubling bound.**  The compiled contradiction's joint
    distinct-shape count is bounded by a fixed local admin family plus the joint shape
    counts of the two premises, **each with coefficient one** — the double `explode` of
    the second premise `c2` does not double its shape contribution. -/
theorem orL_empty_shapeCost_le
    {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (c1 : Contradiction env Γ (φ :: A)) (c2 : Contradiction env Γ (ψ :: A)) :
    Contradiction.shapeCost
      (⟨c1.witness, c1.wwt,
        PPTerm.pOrLcut hφ hψ c1.wwt c1.pos (c2.explode c1.wwt),
        PPTerm.pOrLcut hφ hψ (wtNot c1.wwt) c1.neg (c2.explode (wtNot c1.wwt))⟩ :
        Contradiction env Γ (Formula.or φ ψ :: A))
      ≤ (orLcutAdmin φ ψ c1.witness ++ (explodeAdmin c2 c1.wwt).map (pushReplayShape ψ)
          ++ orLcutAdmin φ ψ (Formula.not c1.witness)
          ++ (explodeAdmin c2 (wtNot c1.wwt)).map (pushReplayShape ψ)).length
        + c1.shapeCost + c2.shapeCost := by
  -- Membership routing: every shape of both certificates lands in admin, C1, or C2.
  have hsub : (PPTerm.pOrLcut hφ hψ c1.wwt c1.pos (c2.explode c1.wwt)).nodeShapes
        ++ (PPTerm.pOrLcut hφ hψ (wtNot c1.wwt) c1.neg (c2.explode (wtNot c1.wwt))).nodeShapes
      ⊆ (orLcutAdmin φ ψ c1.witness ++ (explodeAdmin c2 c1.wwt).map (pushReplayShape ψ)
          ++ orLcutAdmin φ ψ (Formula.not c1.witness)
          ++ (explodeAdmin c2 (wtNot c1.wwt)).map (pushReplayShape ψ))
        ++ (c1.pos.nodeShapes ++ c1.neg.nodeShapes).map (pushReplayShape φ)
        ++ (c2.pos.nodeShapes ++ c2.neg.nodeShapes).map (pushReplayShape ψ) := by
    simp only [PPTerm.pOrLcut, PPTerm.pOrElim, Contradiction.explode, PPTerm.nodeShapes,
      PPTerm.nodeShapes_pMono, orLcutAdmin, explodeAdmin, List.map_cons, List.map_append]
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
    grind
  -- Length collapse: joint dedup + injective push preserves each premise's count.
  simp only [Contradiction.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hAB := dedup_append_length_le
    (orLcutAdmin φ ψ c1.witness ++ (explodeAdmin c2 c1.wwt).map (pushReplayShape ψ)
      ++ orLcutAdmin φ ψ (Formula.not c1.witness)
      ++ (explodeAdmin c2 (wtNot c1.wwt)).map (pushReplayShape ψ)
      ++ (c1.pos.nodeShapes ++ c1.neg.nodeShapes).map (pushReplayShape φ))
    ((c2.pos.nodeShapes ++ c2.neg.nodeShapes).map (pushReplayShape ψ))
  have hA := dedup_append_length_le
    (orLcutAdmin φ ψ c1.witness ++ (explodeAdmin c2 c1.wwt).map (pushReplayShape ψ)
      ++ orLcutAdmin φ ψ (Formula.not c1.witness)
      ++ (explodeAdmin c2 (wtNot c1.wwt)).map (pushReplayShape ψ))
    ((c1.pos.nodeShapes ++ c1.neg.nodeShapes).map (pushReplayShape φ))
  have hbadmin := dedup_length_le
    (orLcutAdmin φ ψ c1.witness ++ (explodeAdmin c2 c1.wwt).map (pushReplayShape ψ)
      ++ orLcutAdmin φ ψ (Formula.not c1.witness)
      ++ (explodeAdmin c2 (wtNot c1.wwt)).map (pushReplayShape ψ))
  have hc1 : (dedup ((c1.pos.nodeShapes ++ c1.neg.nodeShapes).map (pushReplayShape φ))).length
      = (dedup (c1.pos.nodeShapes ++ c1.neg.nodeShapes)).length :=
    dedup_map_length_of_injective (pushReplayShape φ) (pushReplayShape_injective φ) _
  have hc2 : (dedup ((c2.pos.nodeShapes ++ c2.neg.nodeShapes).map (pushReplayShape ψ))).length
      = (dedup (c2.pos.nodeShapes ++ c2.neg.nodeShapes)).length :=
    dedup_map_length_of_injective (pushReplayShape ψ) (pushReplayShape_injective ψ) _
  omega

/-- Numeral form: the empty-succedent `orL` arm adds at most the fixed constant `36`
    distinct shapes on top of its two premises' joint shape counts.  This is the
    concrete refutation of the "exponential replay cost" falsifier (d) for this arm:
    the additive term is a constant independent of the (possibly exponential) subtree
    sizes. -/
theorem orL_empty_shapeCost_le_const
    {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (c1 : Contradiction env Γ (φ :: A)) (c2 : Contradiction env Γ (ψ :: A)) :
    Contradiction.shapeCost
      (⟨c1.witness, c1.wwt,
        PPTerm.pOrLcut hφ hψ c1.wwt c1.pos (c2.explode c1.wwt),
        PPTerm.pOrLcut hφ hψ (wtNot c1.wwt) c1.neg (c2.explode (wtNot c1.wwt))⟩ :
        Contradiction env Γ (Formula.or φ ψ :: A))
      ≤ 36 + c1.shapeCost + c2.shapeCost := by
  have h := orL_empty_shapeCost_le hφ hψ c1 c2
  have hlen : (orLcutAdmin φ ψ c1.witness ++ (explodeAdmin c2 c1.wwt).map (pushReplayShape ψ)
      ++ orLcutAdmin φ ψ (Formula.not c1.witness)
      ++ (explodeAdmin c2 (wtNot c1.wwt)).map (pushReplayShape ψ)).length = 36 := by
    simp only [orLcutAdmin, explodeAdmin, PPTerm.pEF, PPTerm.pImpK, PPTerm.nodeShapes,
      List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

/-! ### Step 2(a), continued: the empty-succedent `impL` arm

    The other double-embedding arm.  Here the `φ`-side premise compiles to a *single*
    certificate `ih1 : PPTerm A φ` (its succedent `[φ]` is nonempty) while the `ψ`-side
    premise compiles to a `Contradiction` `cu` on `ψ :: A`.  The compiled node shares
    `ih1` between both output certificates via the common `dψ = mp hφ hyp (pMono ih1)`
    node.  Kept as set-containment, that shared `ih1` (and the joint `cu`) is charged
    once, giving the same **coefficient-one** recurrence as `orL`. -/

/-- The 8 child-free admin shapes contributed by the empty-succedent `impL` arm
    (four per certificate; the shared `ψ` and `φ.imp ψ` shapes are listed in both). -/
def impLcutAdmin (φ ψ W : Formula) : List ReplayShape :=
  [([], W), ([], ψ.imp W), ([], ψ), ([], φ.imp ψ),
   ([], W.not), ([], ψ.imp W.not), ([], ψ), ([], φ.imp ψ)]

/-- **Empty-succedent `impL` anti-doubling bound.**  The compiled contradiction's joint
    distinct-shape count is bounded by a fixed local admin family plus the joint shape
    count of the `ψ`-side contradiction `cu` and the single `φ`-side certificate `ih1`,
    **each with coefficient one** — the shared `ih1` (embedded in both certificates via
    the common `dψ` node) does not double its shape contribution. -/
theorem impL_empty_shapeCost_le
    {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (ih1 : PPTerm env Γ A φ) (cu : Contradiction env Γ (ψ :: A)) :
    Contradiction.shapeCost
      (⟨cu.witness, cu.wwt,
        PPTerm.mp hψ
          (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) (PPTerm.impIntro hψ cu.pos))
          (PPTerm.mp hφ (PPTerm.hyp (List.mem_cons_self))
            (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1)),
        PPTerm.mp hψ
          (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) (PPTerm.impIntro hψ cu.neg))
          (PPTerm.mp hφ (PPTerm.hyp (List.mem_cons_self))
            (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1))⟩ :
        Contradiction env Γ (Formula.imp φ ψ :: A))
      ≤ (impLcutAdmin φ ψ cu.witness).length + cu.shapeCost + ih1.shapeCost := by
  have hsub :
      (PPTerm.mp hψ
          (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) (PPTerm.impIntro hψ cu.pos))
          (PPTerm.mp hφ (PPTerm.hyp (List.mem_cons_self))
            (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1))).nodeShapes
        ++ (PPTerm.mp hψ
          (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) (PPTerm.impIntro hψ cu.neg))
          (PPTerm.mp hφ (PPTerm.hyp (List.mem_cons_self))
            (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1))).nodeShapes
      ⊆ impLcutAdmin φ ψ cu.witness
        ++ (cu.pos.nodeShapes ++ cu.neg.nodeShapes).map (pushReplayShape ψ)
        ++ ih1.nodeShapes := by
    simp only [PPTerm.nodeShapes, PPTerm.nodeShapes_pMono, impLcutAdmin,
      List.map_append]
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
    grind
  simp only [Contradiction.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hAB := dedup_append_length_le
    (impLcutAdmin φ ψ cu.witness
      ++ (cu.pos.nodeShapes ++ cu.neg.nodeShapes).map (pushReplayShape ψ))
    ih1.nodeShapes
  have hA := dedup_append_length_le
    (impLcutAdmin φ ψ cu.witness)
    ((cu.pos.nodeShapes ++ cu.neg.nodeShapes).map (pushReplayShape ψ))
  have hbadmin := dedup_length_le (impLcutAdmin φ ψ cu.witness)
  have hcu : (dedup ((cu.pos.nodeShapes ++ cu.neg.nodeShapes).map (pushReplayShape ψ))).length
      = (dedup (cu.pos.nodeShapes ++ cu.neg.nodeShapes)).length :=
    dedup_map_length_of_injective (pushReplayShape ψ) (pushReplayShape_injective ψ) _
  have hih1 : (dedup ih1.nodeShapes).length = ih1.shapeCost := rfl
  omega

/-- Numeral form: the empty-succedent `impL` arm adds at most the fixed constant `8`
    distinct shapes on top of the `ψ`-side contradiction's joint shape count and the
    `φ`-side certificate's shape count. -/
theorem impL_empty_shapeCost_le_const
    {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (ih1 : PPTerm env Γ A φ) (cu : Contradiction env Γ (ψ :: A)) :
    Contradiction.shapeCost
      (⟨cu.witness, cu.wwt,
        PPTerm.mp hψ
          (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) (PPTerm.impIntro hψ cu.pos))
          (PPTerm.mp hφ (PPTerm.hyp (List.mem_cons_self))
            (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1)),
        PPTerm.mp hψ
          (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) (PPTerm.impIntro hψ cu.neg))
          (PPTerm.mp hφ (PPTerm.hyp (List.mem_cons_self))
            (PPTerm.pMono (fun _ hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1))⟩ :
        Contradiction env Γ (Formula.imp φ ψ :: A))
      ≤ 8 + cu.shapeCost + ih1.shapeCost := by
  have h := impL_empty_shapeCost_le hφ hψ ih1 cu
  have hlen : (impLcutAdmin φ ψ cu.witness).length = 8 := by
    simp only [impLcutAdmin, List.length_cons, List.length_nil]
  omega

/-! ### Step 2(a), continued: the single-child (coefficient-one) arms

    Every compile arm other than the two double-embedding ones (`orL`/`impL` empty)
    uses each recursive `compile` child *once* (a contradiction's `pos`/`neg` counted
    jointly).  So each such arm satisfies a coefficient-one recurrence
    `shapeCost(arm) ≤ Kᵢ + Σ shapeCost(children)`, proved by the same membership-routing
    + joint-dedup technique: every relative shape lands in a fixed admin family or in an
    injective-`push` copy of a child's shape family.  These are the per-combinator bounds
    the global weighted-cost induction composes. -/

/-- General leaf bound: a certificate's distinct-shape count never exceeds its node
    count.  Used to charge the fixed axiom/`hyp` leaves of a combinator skeleton. -/
theorem PPTerm.shapeCost_le_size {env : Env} {G : Ctx} {D : List Formula}
    {f : Formula} (t : PPTerm env G D f) : t.shapeCost ≤ t.size := by
  unfold PPTerm.shapeCost
  rw [← PPTerm.nodeShapes_length_eq_size]
  exact dedup_length_le _

/-- The child-free admin shapes of `pAndLcut`. -/
def pAndLcutAdmin (φ ψ T : Formula) : List ReplayShape :=
  [([], T), ([], φ.imp T), ([], ψ.imp (φ.imp T)), ([ψ], φ.imp T),
   ([], ψ), ([], (φ.and ψ).imp ψ), ([], φ.and ψ),
   ([], φ), ([], (φ.and ψ).imp φ)]

/-- **`pAndLcut` coefficient-one bound.**  The single hypothesis `h` is embedded once,
    under the injective double `push [φ,ψ]`, so its shapes are counted once. -/
theorem PPTerm.shapeCost_pAndLcut_le {env : Env} {Γ : Ctx} {A : List Formula}
    {T φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : PPTerm env Γ (φ :: ψ :: A) T) :
    (PPTerm.pAndLcut hφ hψ h).shapeCost ≤ (pAndLcutAdmin φ ψ T).length + h.shapeCost := by
  have hsub : (PPTerm.pAndLcut hφ hψ h).nodeShapes ⊆
      pAndLcutAdmin φ ψ T ++ (h.nodeShapes.map (pushReplayShape φ)).map (pushReplayShape ψ) := by
    simp only [PPTerm.pAndLcut, PPTerm.nodeShapes, PPTerm.nodeShapes_pMono, pAndLcutAdmin,
      List.map_cons, pushReplayShape, List.nil_append]
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hA := dedup_append_length_le (pAndLcutAdmin φ ψ T)
    ((h.nodeShapes.map (pushReplayShape φ)).map (pushReplayShape ψ))
  have hadmin := dedup_length_le (pAndLcutAdmin φ ψ T)
  have hchild : (dedup ((h.nodeShapes.map (pushReplayShape φ)).map (pushReplayShape ψ))).length
      = (dedup h.nodeShapes).length := by
    rw [dedup_map_length_of_injective (pushReplayShape ψ) (pushReplayShape_injective ψ),
        dedup_map_length_of_injective (pushReplayShape φ) (pushReplayShape_injective φ)]
  omega

/-- The child-free admin shapes of `pIffLcut`. -/
def pIffLcutAdmin (φ ψ T : Formula) : List ReplayShape :=
  [([], T), ([], (φ.imp ψ).imp T), ([], (ψ.imp φ).imp ((φ.imp ψ).imp T)),
   ([ψ.imp φ], (φ.imp ψ).imp T), ([], ψ.imp φ), ([], (φ.iff ψ).imp (ψ.imp φ)),
   ([], φ.iff ψ), ([], φ.imp ψ), ([], (φ.iff ψ).imp (φ.imp ψ))]

/-- **`pIffLcut` coefficient-one bound.**  The single hypothesis `h` is embedded once,
    under the injective double `push [φ→ψ, ψ→φ]`, so its shapes are counted once. -/
theorem PPTerm.shapeCost_pIffLcut_le {env : Env} {Γ : Ctx} {A : List Formula}
    {T φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (h : PPTerm env Γ (Formula.imp φ ψ :: Formula.imp ψ φ :: A) T) :
    (PPTerm.pIffLcut hφ hψ h).shapeCost ≤ (pIffLcutAdmin φ ψ T).length + h.shapeCost := by
  have hsub : (PPTerm.pIffLcut hφ hψ h).nodeShapes ⊆
      pIffLcutAdmin φ ψ T
        ++ (h.nodeShapes.map (pushReplayShape (φ.imp ψ))).map (pushReplayShape (ψ.imp φ)) := by
    simp only [PPTerm.pIffLcut, PPTerm.nodeShapes, PPTerm.nodeShapes_pMono, pIffLcutAdmin,
      List.map_cons, pushReplayShape, List.nil_append]
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hA := dedup_append_length_le (pIffLcutAdmin φ ψ T)
    ((h.nodeShapes.map (pushReplayShape (φ.imp ψ))).map (pushReplayShape (ψ.imp φ)))
  have hadmin := dedup_length_le (pIffLcutAdmin φ ψ T)
  have hchild : (dedup ((h.nodeShapes.map (pushReplayShape (φ.imp ψ))).map
        (pushReplayShape (ψ.imp φ)))).length = (dedup h.nodeShapes).length := by
    rw [dedup_map_length_of_injective (pushReplayShape (ψ.imp φ))
          (pushReplayShape_injective (ψ.imp φ)),
        dedup_map_length_of_injective (pushReplayShape (φ.imp ψ))
          (pushReplayShape_injective (φ.imp ψ))]
  omega

/-- **`pOrLcut` coefficient-one bound.**  Reuses the existing `pOrLcut_nodeShapes_subset`
    routing: the two hypotheses land under injective single `push`es (`φ` and `ψ`), each
    counted once. -/
theorem PPTerm.shapeCost_pOrLcut_le {env : Env} {Γ : Ctx} {A : List Formula}
    {T φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (hT : (liftFormula? env Γ T).isSome = true)
    (h1 : PPTerm env Γ (φ :: A) T) (h2 : PPTerm env Γ (ψ :: A) T) :
    (PPTerm.pOrLcut hφ hψ hT h1 h2).shapeCost
      ≤ (orLcutAdmin φ ψ T).length + h1.shapeCost + h2.shapeCost := by
  have hsub := pOrLcut_nodeShapes_subset hφ hψ hT h1 h2
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hAB := dedup_append_length_le
    (orLcutAdmin φ ψ T ++ h1.nodeShapes.map (pushReplayShape φ))
    (h2.nodeShapes.map (pushReplayShape ψ))
  have hA := dedup_append_length_le (orLcutAdmin φ ψ T) (h1.nodeShapes.map (pushReplayShape φ))
  have hadmin := dedup_length_le (orLcutAdmin φ ψ T)
  have hc1 := dedup_map_length_of_injective (pushReplayShape φ) (pushReplayShape_injective φ)
    h1.nodeShapes
  have hc2 := dedup_map_length_of_injective (pushReplayShape ψ) (pushReplayShape_injective ψ)
    h2.nodeShapes
  omega

/-- The child-free admin shapes of `pOrElim` (all three hypotheses are direct `mp`
    arguments, so no `push`). -/
def pOrElimAdmin (φ ψ χ : Formula) : List ReplayShape :=
  [([], χ), ([], (φ.or ψ).imp χ), ([], (ψ.imp χ).imp ((φ.or ψ).imp χ)),
   ([], (φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))]

/-- **`pOrElim` coefficient-one bound.**  Each of the three hypotheses is counted once
    (unpushed). -/
theorem PPTerm.shapeCost_pOrElim_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ ψ χ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (hχ : (liftFormula? env Γ χ).isSome = true)
    (hor : PPTerm env Γ Δ (Formula.or φ ψ)) (hl : PPTerm env Γ Δ (Formula.imp φ χ))
    (hr : PPTerm env Γ Δ (Formula.imp ψ χ)) :
    (PPTerm.pOrElim hφ hψ hχ hor hl hr).shapeCost
      ≤ (pOrElimAdmin φ ψ χ).length + hor.shapeCost + hl.shapeCost + hr.shapeCost := by
  have hsub : (PPTerm.pOrElim hφ hψ hχ hor hl hr).nodeShapes ⊆
      pOrElimAdmin φ ψ χ ++ hor.nodeShapes ++ hl.nodeShapes ++ hr.nodeShapes := by
    simp only [PPTerm.pOrElim, PPTerm.nodeShapes, pOrElimAdmin]
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have h1 := dedup_append_length_le
    (pOrElimAdmin φ ψ χ ++ hor.nodeShapes ++ hl.nodeShapes) hr.nodeShapes
  have h2 := dedup_append_length_le (pOrElimAdmin φ ψ χ ++ hor.nodeShapes) hl.nodeShapes
  have h3 := dedup_append_length_le (pOrElimAdmin φ ψ χ) hor.nodeShapes
  have hadmin := dedup_length_le (pOrElimAdmin φ ψ χ)
  omega

/-- The child-free admin shapes of `pOrInl`. -/
def pOrInlAdmin (φ ψ : Formula) : List ReplayShape :=
  [([], φ.or ψ), ([], φ.imp (φ.or ψ))]

/-- **`pOrInl` coefficient-one bound.** -/
theorem PPTerm.shapeCost_pOrInl_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : PPTerm env Γ Δ φ) :
    (PPTerm.pOrInl hφ hψ h).shapeCost ≤ (pOrInlAdmin φ ψ).length + h.shapeCost := by
  have hsub : (PPTerm.pOrInl hφ hψ h).nodeShapes ⊆ pOrInlAdmin φ ψ ++ h.nodeShapes := by
    simp only [PPTerm.pOrInl, PPTerm.nodeShapes, pOrInlAdmin]
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have h1 := dedup_append_length_le (pOrInlAdmin φ ψ) h.nodeShapes
  have hadmin := dedup_length_le (pOrInlAdmin φ ψ)
  omega

/-- The child-free admin shapes of `pOrInr`. -/
def pOrInrAdmin (φ ψ : Formula) : List ReplayShape :=
  [([], φ.or ψ), ([], ψ.imp (φ.or ψ))]

/-- **`pOrInr` coefficient-one bound.** -/
theorem PPTerm.shapeCost_pOrInr_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true) (h : PPTerm env Γ Δ ψ) :
    (PPTerm.pOrInr hφ hψ h).shapeCost ≤ (pOrInrAdmin φ ψ).length + h.shapeCost := by
  have hsub : (PPTerm.pOrInr hφ hψ h).nodeShapes ⊆ pOrInrAdmin φ ψ ++ h.nodeShapes := by
    simp only [PPTerm.pOrInr, PPTerm.nodeShapes, pOrInrAdmin]
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have h1 := dedup_append_length_le (pOrInrAdmin φ ψ) h.nodeShapes
  have hadmin := dedup_length_le (pOrInrAdmin φ ψ)
  omega

/-- The child-free admin shapes of `pImpK`. -/
def pImpKAdmin (a b : Formula) : List ReplayShape :=
  [([], a.imp b), ([], b.imp (a.imp b))]

/-- **`pImpK` coefficient-one bound.** -/
theorem PPTerm.shapeCost_pImpK_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {a b : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (h : PPTerm env Γ Δ b) :
    (PPTerm.pImpK ha hb h).shapeCost ≤ (pImpKAdmin a b).length + h.shapeCost := by
  have hsub : (PPTerm.pImpK ha hb h).nodeShapes ⊆ pImpKAdmin a b ++ h.nodeShapes := by
    simp only [PPTerm.pImpK, PPTerm.nodeShapes, pImpKAdmin]
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have h1 := dedup_append_length_le (pImpKAdmin a b) h.nodeShapes
  have hadmin := dedup_length_le (pImpKAdmin a b)
  omega

/-- The child-free admin shapes of `pImpTrans` (both hypotheses are direct `mp`
    arguments, so no `push`). -/
def pImpTransAdmin (a b c : Formula) : List ReplayShape :=
  [([], a.imp c), ([], (a.imp b).imp (a.imp c)),
   ([], (a.imp (b.imp c)).imp ((a.imp b).imp (a.imp c))),
   ([], a.imp (b.imp c)), ([], (b.imp c).imp (a.imp (b.imp c)))]

/-- **`pImpTrans` coefficient-one bound.** -/
theorem PPTerm.shapeCost_pImpTrans_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {a b c : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (hc : (liftFormula? env Γ c).isSome = true)
    (hab : PPTerm env Γ Δ (Formula.imp a b)) (hbc : PPTerm env Γ Δ (Formula.imp b c)) :
    (PPTerm.pImpTrans ha hb hc hab hbc).shapeCost
      ≤ (pImpTransAdmin a b c).length + hab.shapeCost + hbc.shapeCost := by
  have hsub : (PPTerm.pImpTrans ha hb hc hab hbc).nodeShapes ⊆
      pImpTransAdmin a b c ++ hab.nodeShapes ++ hbc.nodeShapes := by
    simp only [PPTerm.pImpTrans, PPTerm.pImpK, PPTerm.nodeShapes, pImpTransAdmin]
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    grind
  simp only [PPTerm.shapeCost]
  have hstep := dedup_length_le_of_subset _ _ hsub
  have h1 := dedup_append_length_le (pImpTransAdmin a b c ++ hab.nodeShapes) hbc.nodeShapes
  have h2 := dedup_append_length_le (pImpTransAdmin a b c) hab.nodeShapes
  have hadmin := dedup_length_le (pImpTransAdmin a b c)
  omega

/-- Leaf axioms have distinct-shape count one; used to charge the closed cert pieces of
    a combinator skeleton via `omega`. -/
theorem PPTerm.shapeCost_le_size' {env : Env} {G : Ctx} {D : List Formula}
    {f : Formula} (t : PPTerm env G D f) (n : Nat) (h : t.size ≤ n) : t.shapeCost ≤ n :=
  Nat.le_trans (PPTerm.shapeCost_le_size t) h

/-- **`pOrAssocL` coefficient-one bound.**  A single `pOrElim` whose two implication
    hypotheses (`iaT`, `ibcT`) are closed certificates; only the disjunction hypothesis
    `h` carries a compiled subtree. -/
theorem PPTerm.shapeCost_pOrAssocL_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {a b c : Formula} (ha : (liftFormula? env Γ a).isSome = true)
    (hb : (liftFormula? env Γ b).isSome = true) (hc : (liftFormula? env Γ c).isSome = true)
    (h : PPTerm env Γ Δ (Formula.or a (Formula.or b c))) :
    (PPTerm.pOrAssocL ha hb hc h).shapeCost ≤ 24 + h.shapeCost := by
  unfold PPTerm.pOrAssocL
  refine Nat.le_trans (PPTerm.shapeCost_pOrElim_le _ _ _ _ _ _) ?_
  have hia := PPTerm.shapeCost_pImpTrans_le ha (wtOr ha hb) (wtOr (wtOr ha hb) hc)
    (PPTerm.axOrL (Δ := Δ) ha hb) (PPTerm.axOrL (Δ := Δ) (wtOr ha hb) hc)
  have hib := PPTerm.shapeCost_pImpTrans_le hb (wtOr ha hb) (wtOr (wtOr ha hb) hc)
    (PPTerm.axOrR (Δ := Δ) ha hb) (PPTerm.axOrL (Δ := Δ) (wtOr ha hb) hc)
  have hmp := PPTerm.shapeCost_mp_le (wtImp hc (wtOr (wtOr ha hb) hc))
    (PPTerm.mp (wtImp hb (wtOr (wtOr ha hb) hc)) (PPTerm.axOrE (Δ := Δ) hb hc (wtOr (wtOr ha hb) hc))
      (PPTerm.pImpTrans hb (wtOr ha hb) (wtOr (wtOr ha hb) hc)
        (PPTerm.axOrR (Δ := Δ) ha hb) (PPTerm.axOrL (Δ := Δ) (wtOr ha hb) hc)))
    (PPTerm.axOrR (Δ := Δ) (wtOr ha hb) hc)
  have hmp2 := PPTerm.shapeCost_mp_le (wtImp hb (wtOr (wtOr ha hb) hc))
    (PPTerm.axOrE (Δ := Δ) hb hc (wtOr (wtOr ha hb) hc))
    (PPTerm.pImpTrans hb (wtOr ha hb) (wtOr (wtOr ha hb) hc)
      (PPTerm.axOrR (Δ := Δ) ha hb) (PPTerm.axOrL (Δ := Δ) (wtOr ha hb) hc))
  have hoe := PPTerm.shapeCost_le_size' (PPTerm.axOrE (Δ := Δ) hb hc (wtOr (wtOr ha hb) hc)) 1 (by simp [PPTerm.size])
  have hor1 := PPTerm.shapeCost_le_size' (PPTerm.axOrL (Δ := Δ) ha hb) 1 (by simp [PPTerm.size])
  have hor2 := PPTerm.shapeCost_le_size' (PPTerm.axOrL (Δ := Δ) (wtOr ha hb) hc) 1 (by simp [PPTerm.size])
  have hor3 := PPTerm.shapeCost_le_size' (PPTerm.axOrR (Δ := Δ) ha hb) 1 (by simp [PPTerm.size])
  have hor4 := PPTerm.shapeCost_le_size' (PPTerm.axOrR (Δ := Δ) (wtOr ha hb) hc) 1 (by simp [PPTerm.size])
  simp only [pImpTransAdmin, pOrElimAdmin, List.length_cons, List.length_nil] at *
  omega

/-- **`pRaa` coefficient-one bound.**  Reductio: the two hypotheses `hp`, `hn` appear once
    each (both inside the single `impIntro φ` that forms `⊢ φ → ¬φ`), the rest being the
    closed `pCM`/`pDNE`/`pEF` skeleton. -/
theorem PPTerm.shapeCost_pRaa_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hp : PPTerm env Γ (φ :: Δ) ψ) (hn : PPTerm env Γ (φ :: Δ) (Formula.not ψ)) :
    (PPTerm.pRaa hφ hψ hp hn).shapeCost ≤ 100 + hp.shapeCost + hn.shapeCost := by
  simp only [PPTerm.pRaa]
  refine Nat.le_trans (PPTerm.shapeCost_mp_le _ _ _) ?_
  have hcm := PPTerm.shapeCost_le_size' (PPTerm.pCM (Δ := Δ) (wtNot hφ)) 30
    (by simp [PPTerm.pCM, PPTerm.pEF, PPTerm.pImpTrans, PPTerm.pImpK, PPTerm.pImpId, PPTerm.size])
  have htrans := PPTerm.shapeCost_pImpTrans_le (wtNot (wtNot hφ)) hφ (wtNot hφ)
    (PPTerm.pDNE (Δ := Δ) hφ)
    (PPTerm.impIntro hφ (PPTerm.mp hψ (PPTerm.mp (wtNot hψ) (PPTerm.pEF hψ (wtNot hφ)) hn) hp))
  have hdne := PPTerm.shapeCost_le_size' (PPTerm.pDNE (Δ := Δ) hφ) 40
    (by simp [PPTerm.pDNE, PPTerm.pCM, PPTerm.pEF, PPTerm.pImpTrans, PPTerm.pImpK, PPTerm.pImpId,
      PPTerm.size])
  have himp := PPTerm.shapeCost_impIntro_le hφ
    (PPTerm.mp hψ (PPTerm.mp (wtNot hψ) (PPTerm.pEF hψ (wtNot hφ)) hn) hp)
  have hself1 := PPTerm.shapeCost_mp_le hψ
    (PPTerm.mp (wtNot hψ) (PPTerm.pEF hψ (wtNot hφ)) hn) hp
  have hself2 := PPTerm.shapeCost_mp_le (wtNot hψ) (PPTerm.pEF hψ (wtNot hφ)) hn
  have hef := PPTerm.shapeCost_le_size' (PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)) 10
    (by simp [PPTerm.pEF, PPTerm.pImpK, PPTerm.size])
  have hb : (pImpTransAdmin (Formula.not (Formula.not φ)) φ (Formula.not φ)).length = 5 := rfl
  rw [hb] at htrans
  omega

/-- **`pByCases` coefficient-one bound.**  Case split: the two hypotheses `h1`, `h2`
    (each weakened once by `pMono`) appear once each — `h1` inside the reductio `pRaa`
    forming `¬χ ⊢ ¬φ`, `h2` inside the `¬φ → χ` implication — with a closed
    `pCM`/`pRaa` skeleton around them. -/
theorem PPTerm.shapeCost_pByCases_le {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ χ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hχ : (liftFormula? env Γ χ).isSome = true)
    (h1 : PPTerm env Γ (φ :: Δ) χ) (h2 : PPTerm env Γ (Formula.not φ :: Δ) χ) :
    (PPTerm.pByCases hφ hχ h1 h2).shapeCost ≤ 200 + h1.shapeCost + h2.shapeCost := by
  simp only [PPTerm.pByCases]
  refine Nat.le_trans (PPTerm.shapeCost_mp_le _ _ _) ?_
  have hcm := PPTerm.shapeCost_le_size' (PPTerm.pCM (Δ := Δ) hχ) 30
    (by simp [PPTerm.pCM, PPTerm.pEF, PPTerm.pImpTrans, PPTerm.pImpK, PPTerm.pImpId, PPTerm.size])
  have lam1 : ∀ x, x ∈ φ :: Δ → x ∈ φ :: Formula.not χ :: Δ := by
    intro x hx
    rcases List.mem_cons.1 hx with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have lam2 : ∀ x, x ∈ Formula.not φ :: Δ → x ∈ Formula.not φ :: Formula.not χ :: Δ := by
    intro x hx
    rcases List.mem_cons.1 hx with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have hii := PPTerm.shapeCost_impIntro_le (wtNot hχ)
    (PPTerm.mp (wtNot hφ) (PPTerm.impIntro (wtNot hφ) (PPTerm.pMono lam2 h2))
      (PPTerm.pRaa hφ hχ (PPTerm.pMono lam1 h1)
        (PPTerm.hyp (Δ := φ :: Formula.not χ :: Δ) (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hctx := PPTerm.shapeCost_mp_le (wtNot hφ) (PPTerm.impIntro (wtNot hφ) (PPTerm.pMono lam2 h2))
    (PPTerm.pRaa hφ hχ (PPTerm.pMono lam1 h1)
      (PPTerm.hyp (Δ := φ :: Formula.not χ :: Δ) (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hB := PPTerm.shapeCost_impIntro_le (wtNot hφ) (PPTerm.pMono lam2 h2)
  have hraa := PPTerm.shapeCost_pRaa_le hφ hχ (PPTerm.pMono lam1 h1)
    (PPTerm.hyp (Δ := φ :: Formula.not χ :: Δ) (List.mem_cons_of_mem _ List.mem_cons_self))
  have hhyp := PPTerm.shapeCost_le_size'
    (PPTerm.hyp (env := env) (Γ := Γ) (Δ := φ :: Formula.not χ :: Δ) (φ := Formula.not χ)
      (List.mem_cons_of_mem _ List.mem_cons_self)) 1 (by simp [PPTerm.size])
  simp only [PPTerm.shapeCost_pMono] at *
  omega

/-! ### Step 2(a), continued: the joint empty-succedent arms

    The compile arms whose *result* succedent is empty produce a `Contradiction`
    scored by the **joint** `Contradiction.shapeCost = dedup(pos ++ neg)`.  For the
    arms that embed both the child's `pos` and `neg` (or a single child's `pos`/`neg`
    together), the bound must be **joint** — `≤ Kᵢ + Contradiction.shapeCost child`,
    never the sum `sc(pos) + sc(neg)` (up to `2×`, which would reintroduce the
    `2^depth` blow-up since empty-succedent arms chain).  `orL`/`impL` empty are
    above; here are the remaining four (`negR`, `negL`, `andL`, `iffL`). -/

/-- **Joint `hself` bound for `pRaa`.**  The single node `⊢ ¬φ` that `pRaa` forms in
    context `φ :: Δ` embeds *both* premises `hp`, `hn` (via `mp hψ (mp _ (pEF) hn) hp`).
    Its distinct-shape count is charged against a fixed 11-shape admin family plus the
    **joint** deduped count of `hp` and `hn` — the anti-doubling heart of the `negR`
    empty arm. -/
theorem PPTerm.shapeCost_pRaa_hself_joint {env : Env} {Γ : Ctx} {Δ : List Formula}
    {φ ψ : Formula} (hφ : (liftFormula? env Γ φ).isSome = true)
    (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hp : PPTerm env Γ (φ :: Δ) ψ) (hn : PPTerm env Γ (φ :: Δ) (Formula.not ψ)) :
    (PPTerm.mp hψ (PPTerm.mp (wtNot hψ) (PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)) hn) hp).shapeCost
      ≤ 11 + (dedup (hp.nodeShapes ++ hn.nodeShapes)).length := by
  simp only [PPTerm.shapeCost, PPTerm.nodeShapes]
  have hsub : (([], Formula.not φ) ::
        (([], Formula.imp ψ (Formula.not φ)) ::
          ((PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)).nodeShapes ++ hn.nodeShapes) ++ hp.nodeShapes))
      ⊆ (([], Formula.not φ) :: ([], Formula.imp ψ (Formula.not φ)) ::
          (PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)).nodeShapes)
        ++ (hp.nodeShapes ++ hn.nodeShapes) := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    grind
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hA := dedup_append_length_le
    (([], Formula.not φ) :: ([], Formula.imp ψ (Formula.not φ)) ::
      (PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)).nodeShapes)
    (hp.nodeShapes ++ hn.nodeShapes)
  have hadmin := dedup_length_le
    (([], Formula.not φ) :: ([], Formula.imp ψ (Formula.not φ)) ::
      (PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)).nodeShapes)
  have hlen : (([], Formula.not φ) :: ([], Formula.imp ψ (Formula.not φ)) ::
      (PPTerm.pEF (Δ := φ :: Δ) hψ (wtNot hφ)).nodeShapes).length = 11 := by
    simp only [List.length_cons, PPTerm.nodeShapes_length_eq_size]
    simp [PPTerm.pEF, PPTerm.pImpK, PPTerm.size]
  omega

/-- **`negR` empty arm — the joint `pRaa` bound.**  The refuted child `c` on `φ :: A`
    is turned into a single `⊢ ¬φ` certificate by `pRaa c.pos c.neg`; its distinct-shape
    count is at most a fixed constant plus the child's **joint** `Contradiction.shapeCost`,
    **not** `sc(c.pos) + sc(c.neg)`.  This coefficient-one joint bound is what keeps the
    empty-succedent chain linear (it was the one genuine subtlety of the global induction). -/
theorem negR_empty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (c : Contradiction env Γ (φ :: A)) :
    (PPTerm.pRaa hφ c.wwt c.pos c.neg).shapeCost ≤ 100 + Contradiction.shapeCost c := by
  simp only [PPTerm.pRaa, Contradiction.shapeCost]
  refine Nat.le_trans (PPTerm.shapeCost_mp_le _ _ _) ?_
  have hcm := PPTerm.shapeCost_le_size' (PPTerm.pCM (Δ := A) (wtNot hφ)) 30
    (by simp [PPTerm.pCM, PPTerm.pEF, PPTerm.pImpTrans, PPTerm.pImpK, PPTerm.pImpId, PPTerm.size])
  have htrans := PPTerm.shapeCost_pImpTrans_le (wtNot (wtNot hφ)) hφ (wtNot hφ)
    (PPTerm.pDNE (Δ := A) hφ)
    (PPTerm.impIntro hφ
      (PPTerm.mp c.wwt (PPTerm.mp (wtNot c.wwt) (PPTerm.pEF c.wwt (wtNot hφ)) c.neg) c.pos))
  have hdne := PPTerm.shapeCost_le_size' (PPTerm.pDNE (Δ := A) hφ) 40
    (by simp [PPTerm.pDNE, PPTerm.pCM, PPTerm.pEF, PPTerm.pImpTrans, PPTerm.pImpK, PPTerm.pImpId,
      PPTerm.size])
  have himp := PPTerm.shapeCost_impIntro_le hφ
    (PPTerm.mp c.wwt (PPTerm.mp (wtNot c.wwt) (PPTerm.pEF c.wwt (wtNot hφ)) c.neg) c.pos)
  have hself := PPTerm.shapeCost_pRaa_hself_joint hφ c.wwt c.pos c.neg
  have hb : (pImpTransAdmin (Formula.not (Formula.not φ)) φ (Formula.not φ)).length = 5 := rfl
  rw [hb] at htrans
  omega

/-- **`negL` empty arm.**  The refuted-below child `ih : ⊢ φ` becomes the `pos` half of a
    contradiction whose `neg` half is the bare hypothesis `¬φ`; its joint shape count is
    at most `1 + ih.shapeCost`. -/
theorem negL_empty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (ih : PPTerm env Γ A φ) :
    Contradiction.shapeCost
      (⟨φ, hφ, PPTerm.pMono (fun _x hx => List.mem_cons_of_mem (Formula.not φ) hx) ih,
        PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self⟩ :
        Contradiction env Γ (Formula.not φ :: A))
      ≤ 1 + ih.shapeCost := by
  simp only [Contradiction.shapeCost, PPTerm.shapeCost, PPTerm.nodeShapes,
    PPTerm.nodeShapes_pMono]
  have h1 := dedup_append_length_le ih.nodeShapes ([([], Formula.not φ)] : List ReplayShape)
  have h2 : (dedup ([([], Formula.not φ)] : List ReplayShape)).length ≤ 1 := dedup_length_le _
  omega

/-- **`andL` empty arm.**  Both certificates `pAndLcut c.pos` / `pAndLcut c.neg` share the
    same double-`push [φ,ψ]` embedding, so the joint deduped child count `c.shapeCost` is
    charged once; the arm adds at most the fixed constant `18`. -/
theorem andL_empty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (c : Contradiction env Γ (φ :: ψ :: A)) :
    Contradiction.shapeCost
      (⟨c.witness, c.wwt, PPTerm.pAndLcut hφ hψ c.pos, PPTerm.pAndLcut hφ hψ c.neg⟩ :
        Contradiction env Γ (Formula.and φ ψ :: A))
      ≤ 18 + Contradiction.shapeCost c := by
  simp only [Contradiction.shapeCost]
  have hsub : (PPTerm.pAndLcut hφ hψ c.pos).nodeShapes ++ (PPTerm.pAndLcut hφ hψ c.neg).nodeShapes
      ⊆ (pAndLcutAdmin φ ψ c.witness ++ pAndLcutAdmin φ ψ (Formula.not c.witness))
        ++ ((c.pos.nodeShapes ++ c.neg.nodeShapes).map (pushReplayShape φ)).map
            (pushReplayShape ψ) := by
    simp only [PPTerm.pAndLcut, PPTerm.nodeShapes, PPTerm.nodeShapes_pMono, pAndLcutAdmin,
      List.map_cons, List.map_append, pushReplayShape, List.nil_append]
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
    grind
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hA := dedup_append_length_le
    (pAndLcutAdmin φ ψ c.witness ++ pAndLcutAdmin φ ψ (Formula.not c.witness))
    (((c.pos.nodeShapes ++ c.neg.nodeShapes).map (pushReplayShape φ)).map (pushReplayShape ψ))
  have hadmin := dedup_length_le
    (pAndLcutAdmin φ ψ c.witness ++ pAndLcutAdmin φ ψ (Formula.not c.witness))
  have hchild : (dedup (((c.pos.nodeShapes ++ c.neg.nodeShapes).map (pushReplayShape φ)).map
        (pushReplayShape ψ))).length = (dedup (c.pos.nodeShapes ++ c.neg.nodeShapes)).length := by
    rw [dedup_map_length_of_injective (pushReplayShape ψ) (pushReplayShape_injective ψ),
        dedup_map_length_of_injective (pushReplayShape φ) (pushReplayShape_injective φ)]
  have hlen : (pAndLcutAdmin φ ψ c.witness ++ pAndLcutAdmin φ ψ (Formula.not c.witness)).length
      = 18 := by
    simp only [pAndLcutAdmin, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **`iffL` empty arm.**  As `andL`, but the shared embedding is the double-`push
    [φ→ψ, ψ→φ]`; the arm adds at most the fixed constant `18`. -/
theorem iffL_empty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (c : Contradiction env Γ (Formula.imp φ ψ :: Formula.imp ψ φ :: A)) :
    Contradiction.shapeCost
      (⟨c.witness, c.wwt, PPTerm.pIffLcut hφ hψ c.pos, PPTerm.pIffLcut hφ hψ c.neg⟩ :
        Contradiction env Γ (Formula.iff φ ψ :: A))
      ≤ 18 + Contradiction.shapeCost c := by
  simp only [Contradiction.shapeCost]
  have hsub : (PPTerm.pIffLcut hφ hψ c.pos).nodeShapes ++ (PPTerm.pIffLcut hφ hψ c.neg).nodeShapes
      ⊆ (pIffLcutAdmin φ ψ c.witness ++ pIffLcutAdmin φ ψ (Formula.not c.witness))
        ++ ((c.pos.nodeShapes ++ c.neg.nodeShapes).map (pushReplayShape (φ.imp ψ))).map
            (pushReplayShape (ψ.imp φ)) := by
    simp only [PPTerm.pIffLcut, PPTerm.nodeShapes, PPTerm.nodeShapes_pMono, pIffLcutAdmin,
      List.map_cons, List.map_append, pushReplayShape, List.nil_append]
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha ⊢
    grind
  have hstep := dedup_length_le_of_subset _ _ hsub
  have hA := dedup_append_length_le
    (pIffLcutAdmin φ ψ c.witness ++ pIffLcutAdmin φ ψ (Formula.not c.witness))
    (((c.pos.nodeShapes ++ c.neg.nodeShapes).map (pushReplayShape (φ.imp ψ))).map
      (pushReplayShape (ψ.imp φ)))
  have hadmin := dedup_length_le
    (pIffLcutAdmin φ ψ c.witness ++ pIffLcutAdmin φ ψ (Formula.not c.witness))
  have hchild : (dedup (((c.pos.nodeShapes ++ c.neg.nodeShapes).map (pushReplayShape (φ.imp ψ))).map
        (pushReplayShape (ψ.imp φ)))).length
      = (dedup (c.pos.nodeShapes ++ c.neg.nodeShapes)).length := by
    rw [dedup_map_length_of_injective (pushReplayShape (ψ.imp φ))
          (pushReplayShape_injective (ψ.imp φ)),
        dedup_map_length_of_injective (pushReplayShape (φ.imp ψ))
          (pushReplayShape_injective (φ.imp ψ))]
  have hlen : (pIffLcutAdmin φ ψ c.witness ++ pIffLcutAdmin φ ψ (Formula.not c.witness)).length
      = 18 := by
    simp only [pIffLcutAdmin, List.length_append, List.length_cons, List.length_nil]
  omega

/-! ### Step 2(a), continued: the nonempty-succedent arms and the two-premise `mp` arms

    The remaining `compile` arms produce a single `PPTerm` (nonempty succedent) built by
    composing the per-combinator skeletons around one or two recursive certificates.  Each
    satisfies a coefficient-one recurrence `sc(arm) ≤ Kᵢ + Σ ihⱼ.shapeCost`, proved by
    chaining the combinator bounds and charging the closed skeleton pieces by
    `shapeCost ≤ size`.  These are the last inputs the global weighted-cost induction needs. -/

/-- **`andR` empty arm** — `∧`-introduction of two derived premises. -/
theorem andR_empty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (ih1p : PPTerm env Γ A φ) (ih2p : PPTerm env Γ A ψ) :
    (PPTerm.mp hψ (PPTerm.mp hφ (PPTerm.axAndI hφ hψ) ih1p) ih2p).shapeCost
      ≤ 3 + ih1p.shapeCost + ih2p.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_mp_le _ _ _) ?_
  have hinner := PPTerm.shapeCost_mp_le hφ (PPTerm.axAndI hφ hψ) ih1p
  have hax := PPTerm.shapeCost_le_size' (PPTerm.axAndI (Δ := A) hφ hψ) 1 (by simp [PPTerm.size])
  omega

/-- **`iffR` empty arm** — `↔`-introduction of the two directions. -/
theorem iffR_empty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (ih1p : PPTerm env Γ A (Formula.imp φ ψ)) (ih2p : PPTerm env Γ A (Formula.imp ψ φ)) :
    (PPTerm.mp (wtImp hψ hφ) (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ) ih1p) ih2p).shapeCost
      ≤ 3 + ih1p.shapeCost + ih2p.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_mp_le _ _ _) ?_
  have hinner := PPTerm.shapeCost_mp_le (wtImp hφ hψ) (PPTerm.axIffI hφ hψ) ih1p
  have hax := PPTerm.shapeCost_le_size' (PPTerm.axIffI (Δ := A) hφ hψ) 1 (by simp [PPTerm.size])
  omega

/-- **`negR` nonempty arm** — a case split `pByCases` whose two branches inject the derived
    premise `ih` (right) and the hypothesis `¬φ` (left) into the disjunction. -/
theorem negR_nonempty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ χR : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true)
    (hR : (liftFormula? env Γ χR).isSome = true) (ih : PPTerm env Γ (φ :: A) χR) :
    (PPTerm.pByCases hφ (wtOr (wtNot hφ) hR)
      (PPTerm.pOrInr (wtNot hφ) hR ih)
      (PPTerm.pOrInl (wtNot hφ) hR
        (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self))).shapeCost
      ≤ 205 + ih.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_pByCases_le _ _ _ _) ?_
  have h1 := PPTerm.shapeCost_pOrInr_le (wtNot hφ) hR ih
  have h2 := PPTerm.shapeCost_pOrInl_le (wtNot hφ) hR
    (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self)
  have h3 := PPTerm.shapeCost_le_size'
    (PPTerm.hyp (env := env) (Γ := Γ) (Δ := Formula.not φ :: A) (φ := Formula.not φ)
      List.mem_cons_self) 1 (by simp [PPTerm.size])
  simp only [pOrInrAdmin, pOrInlAdmin, List.length_cons, List.length_nil] at h1 h2
  omega

/-- **`negL` nonempty arm** — a `pOrElim` on `φ ∨ χR`: the `φ` branch is the ex-falso
    `¬φ → φ → χR` applied to the hypothesis, the `χR` branch is the identity. -/
theorem negL_nonempty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ χR : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true)
    (hR : (liftFormula? env Γ χR).isSome = true) (ih : PPTerm env Γ A (Formula.or φ χR)) :
    (PPTerm.pOrElim hφ hR hR
      (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem (Formula.not φ) hx) ih)
      (PPTerm.mp (wtNot hφ) (PPTerm.pEF hφ hR)
        (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self))
      (PPTerm.pImpId hR)).shapeCost ≤ 30 + ih.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_pOrElim_le _ _ _ _ _ _) ?_
  have hpm := PPTerm.shapeCost_pMono (fun _x hx => List.mem_cons_of_mem (Formula.not φ) hx) ih
  have hl := PPTerm.shapeCost_le_size'
    (PPTerm.mp (wtNot hφ) (PPTerm.pEF (Δ := Formula.not φ :: A) hφ hR)
      (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self)) 12
    (by simp [PPTerm.pEF, PPTerm.pImpK, PPTerm.size])
  have hr := PPTerm.shapeCost_le_size' (PPTerm.pImpId (Δ := Formula.not φ :: A) hR) 10
    (by simp [PPTerm.pImpId, PPTerm.size])
  simp only [pOrElimAdmin, List.length_cons, List.length_nil] at *
  omega

/-- **`impL` nonempty arm** — a `pOrElim` on `φ ∨ χR`: the `φ` branch applies the derived
    `⊢ ψ → χR` (weakened `ih2`) after discharging `φ → ψ` from the hypotheses, the `χR`
    branch is the identity. -/
theorem impL_nonempty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ χR : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hR : (liftFormula? env Γ χR).isSome = true)
    (ih1 : PPTerm env Γ A (Formula.or φ χR)) (ih2 : PPTerm env Γ (ψ :: A) χR) :
    (PPTerm.pOrElim hφ hR hR
      (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1)
      (PPTerm.impIntro hφ
        (PPTerm.mp hψ
          (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem φ
              (List.mem_cons_of_mem (Formula.imp φ ψ) hx)) (PPTerm.impIntro hψ ih2))
          (PPTerm.mp hφ
            (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := Formula.imp φ ψ)
              (List.mem_cons_of_mem _ List.mem_cons_self))
            (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := φ) List.mem_cons_self))))
      (PPTerm.pImpId hR)).shapeCost ≤ 30 + ih1.shapeCost + ih2.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_pOrElim_le _ _ _ _ _ _) ?_
  have hih1w := PPTerm.shapeCost_pMono
    (fun _x hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih1
  have hhr := PPTerm.shapeCost_le_size' (PPTerm.pImpId (Δ := Formula.imp φ ψ :: A) hR) 10
    (by simp [PPTerm.pImpId, PPTerm.size])
  have hhl := PPTerm.shapeCost_impIntro_le hφ
    (PPTerm.mp hψ
      (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem φ
          (List.mem_cons_of_mem (Formula.imp φ ψ) hx)) (PPTerm.impIntro hψ ih2))
      (PPTerm.mp hφ
        (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := Formula.imp φ ψ)
          (List.mem_cons_of_mem _ List.mem_cons_self))
        (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := φ) List.mem_cons_self)))
  have hinner := PPTerm.shapeCost_mp_le hψ
    (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem φ
        (List.mem_cons_of_mem (Formula.imp φ ψ) hx)) (PPTerm.impIntro hψ ih2))
    (PPTerm.mp hφ
      (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := Formula.imp φ ψ)
        (List.mem_cons_of_mem _ List.mem_cons_self))
      (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := φ) List.mem_cons_self))
  have hh2 := PPTerm.shapeCost_pMono
    (fun _x hx => List.mem_cons_of_mem φ (List.mem_cons_of_mem (Formula.imp φ ψ) hx))
    (PPTerm.impIntro hψ ih2)
  have hii2 := PPTerm.shapeCost_impIntro_le hψ ih2
  have hhψp := PPTerm.shapeCost_le_size'
    (PPTerm.mp hφ
      (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := Formula.imp φ ψ)
        (List.mem_cons_of_mem _ List.mem_cons_self))
      (PPTerm.hyp (Δ := φ :: Formula.imp φ ψ :: A) (φ := φ) List.mem_cons_self)) 3
    (by simp [PPTerm.size])
  simp only [pOrElimAdmin, List.length_cons, List.length_nil] at *
  omega

/-- **`impR` nonempty arm** — a `pByCases`: the `φ` branch elininates `ψ ∨ χR`, packing
    `φ → ψ` (from `pImpK` on the hypothesis) into the goal disjunction; the `¬φ` branch
    uses ex-falso. -/
theorem impR_nonempty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ χR : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hR : (liftFormula? env Γ χR).isSome = true)
    (ihp : PPTerm env Γ (φ :: A) (Formula.or ψ χR)) :
    (PPTerm.pByCases hφ (wtOr (wtImp hφ hψ) hR)
      (PPTerm.pOrElim hψ hR (wtOr (wtImp hφ hψ) hR) ihp
        (PPTerm.impIntro hψ
          (PPTerm.pOrInl (wtImp hφ hψ) hR
            (PPTerm.pImpK hφ hψ
              (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))))
        (PPTerm.axOrR (Δ := φ :: A) (wtImp hφ hψ) hR))
      (PPTerm.pOrInl (wtImp hφ hψ) hR
        (PPTerm.mp (wtNot hφ) (PPTerm.pEF hφ hψ)
          (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ)
            List.mem_cons_self)))).shapeCost ≤ 250 + ihp.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_pByCases_le _ _ _ _) ?_
  have hh1 := PPTerm.shapeCost_pOrElim_le hψ hR (wtOr (wtImp hφ hψ) hR) ihp
    (PPTerm.impIntro hψ
      (PPTerm.pOrInl (wtImp hφ hψ) hR
        (PPTerm.pImpK hφ hψ (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))))
    (PPTerm.axOrR (Δ := φ :: A) (wtImp hφ hψ) hR)
  have hhl := PPTerm.shapeCost_impIntro_le hψ
    (PPTerm.pOrInl (wtImp hφ hψ) hR
      (PPTerm.pImpK hφ hψ (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self)))
  have hpi := PPTerm.shapeCost_pOrInl_le (wtImp hφ hψ) hR
    (PPTerm.pImpK hφ hψ (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))
  have hpk := PPTerm.shapeCost_le_size'
    (PPTerm.pImpK (Δ := ψ :: φ :: A) hφ hψ
      (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self)) 3
    (by simp [PPTerm.pImpK, PPTerm.size])
  have hor := PPTerm.shapeCost_le_size' (PPTerm.axOrR (Δ := φ :: A) (wtImp hφ hψ) hR) 1
    (by simp [PPTerm.size])
  have hh2 := PPTerm.shapeCost_pOrInl_le (wtImp hφ hψ) hR
    (PPTerm.mp (wtNot hφ) (PPTerm.pEF (Δ := Formula.not φ :: A) hφ hψ)
      (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self))
  have hmp := PPTerm.shapeCost_le_size'
    (PPTerm.mp (wtNot hφ) (PPTerm.pEF (Δ := Formula.not φ :: A) hφ hψ)
      (PPTerm.hyp (Δ := Formula.not φ :: A) (φ := Formula.not φ) List.mem_cons_self)) 12
    (by simp [PPTerm.pEF, PPTerm.pImpK, PPTerm.size])
  simp only [pOrElimAdmin, pOrInlAdmin, List.length_cons, List.length_nil] at *
  omega

/-- **`andR` nonempty arm** — nested `pOrElim`s over `φ ∨ χR` and `ψ ∨ χR`; the innermost
    `φ,ψ` branch packs `φ ∧ ψ` (from `axAndI` on the hypotheses) into the goal disjunction. -/
theorem andR_nonempty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ χR : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hR : (liftFormula? env Γ χR).isSome = true)
    (ih1p : PPTerm env Γ A (Formula.or φ χR)) (ih2p : PPTerm env Γ A (Formula.or ψ χR)) :
    (PPTerm.pOrElim hφ hR (wtOr (wtAnd hφ hψ) hR) ih1p
      (PPTerm.impIntro hφ
        (PPTerm.pOrElim hψ hR (wtOr (wtAnd hφ hψ) hR)
          (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem φ hx) ih2p)
          (PPTerm.impIntro hψ
            (PPTerm.pOrInl (wtAnd hφ hψ) hR
              (PPTerm.mp hψ
                (PPTerm.mp hφ (PPTerm.axAndI hφ hψ)
                  (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := φ)
                    (List.mem_cons_of_mem ψ List.mem_cons_self)))
                (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))))
          (PPTerm.axOrR (Δ := φ :: A) (wtAnd hφ hψ) hR)))
      (PPTerm.axOrR (Δ := A) (wtAnd hφ hψ) hR)).shapeCost
      ≤ 30 + ih1p.shapeCost + ih2p.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_pOrElim_le _ _ _ _ _ _) ?_
  have hlouter := PPTerm.shapeCost_impIntro_le hφ
    (PPTerm.pOrElim hψ hR (wtOr (wtAnd hφ hψ) hR)
      (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem φ hx) ih2p)
      (PPTerm.impIntro hψ
        (PPTerm.pOrInl (wtAnd hφ hψ) hR
          (PPTerm.mp hψ
            (PPTerm.mp hφ (PPTerm.axAndI hφ hψ)
              (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := φ)
                (List.mem_cons_of_mem ψ List.mem_cons_self)))
            (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))))
      (PPTerm.axOrR (Δ := φ :: A) (wtAnd hφ hψ) hR))
  have hinner := PPTerm.shapeCost_pOrElim_le hψ hR (wtOr (wtAnd hφ hψ) hR)
    (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem φ hx) ih2p)
    (PPTerm.impIntro hψ
      (PPTerm.pOrInl (wtAnd hφ hψ) hR
        (PPTerm.mp hψ
          (PPTerm.mp hφ (PPTerm.axAndI hφ hψ)
            (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := φ)
              (List.mem_cons_of_mem ψ List.mem_cons_self)))
          (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))))
    (PPTerm.axOrR (Δ := φ :: A) (wtAnd hφ hψ) hR)
  have hih2w := PPTerm.shapeCost_pMono (fun _x hx => List.mem_cons_of_mem φ hx) ih2p
  have hlin := PPTerm.shapeCost_impIntro_le hψ
    (PPTerm.pOrInl (wtAnd hφ hψ) hR
      (PPTerm.mp hψ
        (PPTerm.mp hφ (PPTerm.axAndI hφ hψ)
          (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := φ)
            (List.mem_cons_of_mem ψ List.mem_cons_self)))
        (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self)))
  have hpoi := PPTerm.shapeCost_pOrInl_le (wtAnd hφ hψ) hR
    (PPTerm.mp hψ
      (PPTerm.mp hφ (PPTerm.axAndI hφ hψ)
        (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := φ)
          (List.mem_cons_of_mem ψ List.mem_cons_self)))
      (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self))
  have hhand := PPTerm.shapeCost_le_size'
    (PPTerm.mp hψ
      (PPTerm.mp hφ (PPTerm.axAndI hφ hψ)
        (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := φ)
          (List.mem_cons_of_mem ψ List.mem_cons_self)))
      (PPTerm.hyp (Δ := ψ :: φ :: A) (φ := ψ) List.mem_cons_self)) 5
    (by simp [PPTerm.size])
  have hrouter := PPTerm.shapeCost_le_size' (PPTerm.axOrR (Δ := A) (wtAnd hφ hψ) hR) 1
    (by simp [PPTerm.size])
  have hrin := PPTerm.shapeCost_le_size' (PPTerm.axOrR (Δ := φ :: A) (wtAnd hφ hψ) hR) 1
    (by simp [PPTerm.size])
  simp only [pOrElimAdmin, pOrInlAdmin, List.length_cons, List.length_nil] at *
  omega

/-- **`iffR` nonempty arm** — as `andR` nonempty, but the innermost branch packs `φ ↔ ψ`
    (from `axIffI` on the two implication hypotheses) into the goal disjunction. -/
theorem iffR_nonempty_shapeCost_le {env : Env} {Γ : Ctx} {A : List Formula} {φ ψ χR : Formula}
    (hφ : (liftFormula? env Γ φ).isSome = true) (hψ : (liftFormula? env Γ ψ).isSome = true)
    (hR : (liftFormula? env Γ χR).isSome = true)
    (ih1p : PPTerm env Γ A (Formula.or (Formula.imp φ ψ) χR))
    (ih2p : PPTerm env Γ A (Formula.or (Formula.imp ψ φ) χR)) :
    (PPTerm.pOrElim (wtImp hφ hψ) hR (wtOr (wtIff hφ hψ) hR) ih1p
      (PPTerm.impIntro (wtImp hφ hψ)
        (PPTerm.pOrElim (wtImp hψ hφ) hR (wtOr (wtIff hφ hψ) hR)
          (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih2p)
          (PPTerm.impIntro (wtImp hψ hφ)
            (PPTerm.pOrInl (wtIff hφ hψ) hR
              (PPTerm.mp (wtImp hψ hφ)
                (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ)
                  (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
                    (φ := Formula.imp φ ψ) (List.mem_cons_of_mem _ List.mem_cons_self)))
                (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
                  (φ := Formula.imp ψ φ) List.mem_cons_self))))
          (PPTerm.axOrR (Δ := Formula.imp φ ψ :: A) (wtIff hφ hψ) hR)))
      (PPTerm.axOrR (Δ := A) (wtIff hφ hψ) hR)).shapeCost
      ≤ 30 + ih1p.shapeCost + ih2p.shapeCost := by
  refine Nat.le_trans (PPTerm.shapeCost_pOrElim_le _ _ _ _ _ _) ?_
  have hlouter := PPTerm.shapeCost_impIntro_le (wtImp hφ hψ)
    (PPTerm.pOrElim (wtImp hψ hφ) hR (wtOr (wtIff hφ hψ) hR)
      (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih2p)
      (PPTerm.impIntro (wtImp hψ hφ)
        (PPTerm.pOrInl (wtIff hφ hψ) hR
          (PPTerm.mp (wtImp hψ hφ)
            (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ)
              (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
                (φ := Formula.imp φ ψ) (List.mem_cons_of_mem _ List.mem_cons_self)))
            (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
              (φ := Formula.imp ψ φ) List.mem_cons_self))))
      (PPTerm.axOrR (Δ := Formula.imp φ ψ :: A) (wtIff hφ hψ) hR))
  have hinner := PPTerm.shapeCost_pOrElim_le (wtImp hψ hφ) hR (wtOr (wtIff hφ hψ) hR)
    (PPTerm.pMono (fun _x hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih2p)
    (PPTerm.impIntro (wtImp hψ hφ)
      (PPTerm.pOrInl (wtIff hφ hψ) hR
        (PPTerm.mp (wtImp hψ hφ)
          (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ)
            (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
              (φ := Formula.imp φ ψ) (List.mem_cons_of_mem _ List.mem_cons_self)))
          (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
            (φ := Formula.imp ψ φ) List.mem_cons_self))))
    (PPTerm.axOrR (Δ := Formula.imp φ ψ :: A) (wtIff hφ hψ) hR)
  have hih2w := PPTerm.shapeCost_pMono
    (fun _x hx => List.mem_cons_of_mem (Formula.imp φ ψ) hx) ih2p
  have hlin := PPTerm.shapeCost_impIntro_le (wtImp hψ hφ)
    (PPTerm.pOrInl (wtIff hφ hψ) hR
      (PPTerm.mp (wtImp hψ hφ)
        (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ)
          (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
            (φ := Formula.imp φ ψ) (List.mem_cons_of_mem _ List.mem_cons_self)))
        (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
          (φ := Formula.imp ψ φ) List.mem_cons_self)))
  have hpoi := PPTerm.shapeCost_pOrInl_le (wtIff hφ hψ) hR
    (PPTerm.mp (wtImp hψ hφ)
      (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ)
        (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
          (φ := Formula.imp φ ψ) (List.mem_cons_of_mem _ List.mem_cons_self)))
      (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
        (φ := Formula.imp ψ φ) List.mem_cons_self))
  have hhiffp := PPTerm.shapeCost_le_size'
    (PPTerm.mp (wtImp hψ hφ)
      (PPTerm.mp (wtImp hφ hψ) (PPTerm.axIffI hφ hψ)
        (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
          (φ := Formula.imp φ ψ) (List.mem_cons_of_mem _ List.mem_cons_self)))
      (PPTerm.hyp (Δ := Formula.imp ψ φ :: Formula.imp φ ψ :: A)
        (φ := Formula.imp ψ φ) List.mem_cons_self)) 5
    (by simp [PPTerm.size])
  have hrouter := PPTerm.shapeCost_le_size' (PPTerm.axOrR (Δ := A) (wtIff hφ hψ) hR) 1
    (by simp [PPTerm.size])
  have hrin := PPTerm.shapeCost_le_size'
    (PPTerm.axOrR (Δ := Formula.imp φ ψ :: A) (wtIff hφ hψ) hR) 1 (by simp [PPTerm.size])
  simp only [pOrElimAdmin, pOrInlAdmin, List.length_cons, List.length_nil] at *
  omega

/-! ### Step 2(a): the weighted trace cost the global bound must use

    An ordinary node-counting trace size with a *fixed* constant `K` cannot bound
    `ReifiedDenote.shapeCost (compile tr)`: an `FTrace.id` is **one** trace node
    regardless of its succedent length, yet `compile` replays it through
    `pRightOr_mem`, whose certificate size grows linearly with the succedent tail
    (`PPTerm.shapeCost_pRightOr_mem_le`).  So a one-node identity trace can compile to
    an arbitrarily wide certificate.  The correct global statement therefore weighs each
    `id` leaf by its succedent width:

      `ReifiedDenote.shapeCost (compile tr) ≤ K · tr.weightedCost`.

    This does not weaken the two anti-doubling results — it still says the compiler adds
    no *second* exponential — but it is what makes the global claim true. -/

/-- Weighted trace cost: internal rule nodes cost one; an `id` leaf costs its succedent
    width (the only list-traversing replay operation in `compile` is the `pRightOr_mem`
    at `id`). -/
def FTrace.weightedCost {env : Env} {Γ : Ctx} :
    {S : FSequent} -> FTrace env Γ S -> Nat
  | _, .id (S := S) _ _ _ => S.length
  | _, .negR _ _ t => 1 + t.weightedCost
  | _, .negL _ _ t => 1 + t.weightedCost
  | _, .impR _ _ _ t => 1 + t.weightedCost
  | _, .impL _ _ _ t u => 1 + t.weightedCost + u.weightedCost
  | _, .andR _ _ _ t u => 1 + t.weightedCost + u.weightedCost
  | _, .andL _ _ t => 1 + t.weightedCost
  | _, .orR _ _ _ t => 1 + t.weightedCost
  | _, .orL _ _ _ t u => 1 + t.weightedCost + u.weightedCost
  | _, .iffR _ _ _ t u => 1 + t.weightedCost + u.weightedCost
  | _, .iffL _ _ t => 1 + t.weightedCost

/-- **The `id`-leaf bound.**  The compiled certificate of a one-node identity trace has
    distinct-shape count at most `3 ·` its weighted cost — i.e. the succedent-width
    growth of `pRightOr_mem` is exactly absorbed by charging the succedent width in the
    weight.  This is the base case a fixed-`K` node count cannot satisfy. -/
theorem id_shapeCost_le_weighted {env : Env} {Γ : Ctx}
    {A : List Formula} {head : Formula} {tail : List Formula} {φ : Formula}
    (hA : φ ∈ A) (hS : φ ∈ head :: tail) (hall : LiftsAllF env Γ (head :: tail)) :
    ReifiedDenote.shapeCost (compile (FTrace.id hA hS hall))
      ≤ 3 * (FTrace.id hA hS hall).weightedCost := by
  show (PPTerm.pRightOr_mem head tail hS (PPTerm.hyp hA) hall).shapeCost
    ≤ 3 * (head :: tail).length
  have h := PPTerm.shapeCost_pRightOr_mem_le head tail hS (PPTerm.hyp hA) hall
  simp only [PPTerm.nodeShapes, List.length_cons, List.length_nil] at h
  simp only [List.length_cons]
  omega

/-! ### Step 2(a): the global weighted-cost bound — the compiler adds no *further*
    exponential over the weighted trace

    The theorem below closes step 2(a): the distinct-shape count of the compiled
    certificate is **linear in the weighted trace cost**, `≤ 250 · weightedCost`.  Since
    `weightedCost` charges each `id` leaf its succedent width and every internal rule node
    a constant `1`, this says the compiler's replay-shape footprint is at most a constant
    multiple of the (weighted) search trace — no second exponential is introduced.  The
    proof is one structural induction dispatching each `compile` arm to its per-arm
    coefficient-one bound (above), with the refuted (empty-succedent) arms scored by the
    **joint** `Contradiction.shapeCost` so the empty-succedent chain stays linear (the
    `negR`/`orL`/`impL`/`andL`/`iffL` anti-doubling results). -/

/-- **The global weighted-cost bound.**  Every compiled certificate has distinct-shape
    count at most `250 ·` the weighted trace cost. -/
theorem shapeCost_compile_le_weighted {env : Env} {Γ : Ctx} :
    ∀ {S : FSequent} (tr : FTrace env Γ S),
      ReifiedDenote.shapeCost (compile tr) ≤ 250 * tr.weightedCost := by
  intro S tr
  induction tr with
  | @id A S φ hA hS hall =>
      cases S with
      | nil => exact absurd hS (List.not_mem_nil)
      | cons head tail =>
          exact Nat.le_trans (id_shapeCost_le_weighted hA hS hall) (by omega)
  | @negR A Θ φ hφ hΘ t ih =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (negR_empty_shapeCost_le hφ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (negR_nonempty_shapeCost_le hφ _ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
  | @negL A Θ φ hφ hΘ t ih =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (negL_empty_shapeCost_le hφ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (negL_nonempty_shapeCost_le hφ _ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
  | @impR A Θ φ ψ hφ hψ hΘ t ih =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (PPTerm.shapeCost_impIntro_le hφ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (impR_nonempty_shapeCost_le hφ hψ _ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
  | @impL A Θ φ ψ hφ hψ hΘ t u iht ihu =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (impL_empty_shapeCost_le_const hφ hψ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left ihu _) iht) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (impL_nonempty_shapeCost_le hφ hψ _ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega))
  | @andR A Θ φ ψ hφ hψ hΘ t u iht ihu =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (andR_empty_shapeCost_le hφ hψ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (andR_nonempty_shapeCost_le hφ hψ _ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega))
  | @andL A Θ φ ψ hφ hψ t ih =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (andL_empty_shapeCost_le hφ hψ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          refine Nat.le_trans (PPTerm.shapeCost_pAndLcut_le hφ hψ (compile t)) ?_
          simp only [pAndLcutAdmin, List.length_cons, List.length_nil]
          exact Nat.le_trans (Nat.add_le_add_left ih _) (by omega)
  | @orR A Θ φ ψ hφ hψ hΘ t ih =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans ih (by omega)
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (PPTerm.shapeCost_pOrAssocL_le hφ hψ _ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
  | @orL A Θ φ ψ hφ hψ hΘ t u iht ihu =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (orL_empty_shapeCost_le_const hφ hψ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          refine Nat.le_trans (PPTerm.shapeCost_pOrLcut_le hφ hψ _ (compile t) (compile u)) ?_
          simp only [orLcutAdmin, List.length_cons, List.length_nil]
          exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega)
  | @iffR A Θ φ ψ hφ hψ hΘ t u iht ihu =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (iffR_empty_shapeCost_le hφ hψ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (iffR_nonempty_shapeCost_le hφ hψ _ (compile t) (compile u))
            (Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left iht _) ihu) (by omega))
  | @iffL A Θ φ ψ hφ hψ t ih =>
      cases Θ with
      | nil =>
          simp only [compile, FTrace.weightedCost]
          exact Nat.le_trans (iffL_empty_shapeCost_le hφ hψ (compile t))
            (Nat.le_trans (Nat.add_le_add_left ih _) (by omega))
      | cons χ0 Θ' =>
          simp only [compile, FTrace.weightedCost]
          refine Nat.le_trans (PPTerm.shapeCost_pIffLcut_le hφ hψ (compile t)) ?_
          simp only [pIffLcutAdmin, List.length_cons, List.length_nil]
          exact Nat.le_trans (Nat.add_le_add_left ih _) (by omega)

end Focused
end ContextualHOL
