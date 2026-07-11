import ContextualHOL.ProvesLift

/-!
# PS2 — analytic propositional search: the two-sided focused calculus

CoreSearch0's propositional search calculus.  The search shape is deliberately
**multi-conclusion** (`Δ ⊢ Θ`, `Θ : List Formula`), because primitive classical
`not` cannot move a negated hypothesis across a single-conclusion turnstile.

We do NOT add a falsity constant to M3.  Instead the succedent is interpreted
into M3's single-conclusion `Proves` by right-nested disjunction, and the empty
succedent is given the ⊥-free meaning "the antecedent is absurd" (proves every
well-typed formula).  Whether the completeness direction is ever *forced* to
introduce an empty succedent is a pre-registered PS2 falsifier, tracked here and
never resolved by smuggling in `⊥`.

This module (increment 1) fixes the representation and proves the soundness
direction `focusedSound : FDeriv → Proves`.  Cut/MP admissibility, the K/S/CP
completeness direction, focus discipline, and subformula-boundedness follow.
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

/-! ## The two-sided sequent and its ⊥-free denotation -/

/-- A two-sided focused search sequent `ante ⊢ succ`. -/
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

end Focused
end ContextualHOL
