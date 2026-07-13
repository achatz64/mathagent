import ContextualHOL.Focused

/-!
# PS2 — finite-state search: the signed subformula closure and rule closure

This module begins the *finite-state / termination* branch of PS2.  Per the audit,
finiteness must be established for the **focused, analytic** state representation (the
two-sided `FSequent` of `Focused.lean`), not for the unfocused `FDeriv` trace language.

The backbone is the **signed subformula closure** `Formula.searchClosure`: the smallest
formula set containing `φ` and closed under taking immediate subformulas *and*, for each
`iff φ ψ`, the two implications `imp φ ψ`, `imp ψ φ` that the `iff` rules introduce.  Every
backward analytic rule replaces a principal formula by formulas drawn from its closure, so
a sequent whose formulas all lie in a closed set `C` steps only to sequents with the same
property (`FStep.inClosure`).  Since a normalized state is a pair of **sub-sets** of `C`,
this is the `≤ 4^{|C|}` finiteness argument's first half (closure); the counting half
(`finiteStateProp`) follows in a later slice.

Ordering of the branch (per audit): (1) state/key + transitions [`FStep`, here]; (2)
closure [`FStep.inClosure`, here]; (3) the `≤ 4^{|C|}` finite bound; (4) memoized BFS +
termination.
-/

namespace ContextualHOL

/-- **Signed subformula closure of a formula.**  Immediate subformulas, plus — crucially —
    for `iff φ ψ` the two implications `imp φ ψ` and `imp ψ φ` that the `iffR`/`iffL` rules
    expose (and, transitively, their subformulas).  Structurally recursive on the formula
    (the two `imp`s are added as *elements*, not recursed through, so termination is on the
    subterms `φ`, `ψ`). -/
def Formula.searchClosure : Formula -> List Formula
  | .atom n t u => [.atom n t u]
  | .papp n t => [.papp n t]
  | .and φ ψ => .and φ ψ :: (φ.searchClosure ++ ψ.searchClosure)
  | .or φ ψ => .or φ ψ :: (φ.searchClosure ++ ψ.searchClosure)
  | .imp φ ψ => .imp φ ψ :: (φ.searchClosure ++ ψ.searchClosure)
  | .not φ => .not φ :: φ.searchClosure
  | .iff φ ψ =>
      .iff φ ψ :: .imp φ ψ :: .imp ψ φ :: (φ.searchClosure ++ ψ.searchClosure)
  | .all n x φ => .all n x φ :: φ.searchClosure
  | .ex n x φ => .ex n x φ :: φ.searchClosure

/-- A formula is in its own closure (the head element). -/
theorem Formula.self_mem_searchClosure (a : Formula) : a ∈ a.searchClosure := by
  cases a <;> simp [Formula.searchClosure]

/-- **Transitivity of the closure.**  If `b` is in `a`'s closure then every member of `b`'s
    closure is in `a`'s closure — i.e. `a.searchClosure` is downward closed.  This is the
    key structural lemma: a rule that replaces `b` (a closure member) by a subformula of `b`
    keeps everything inside `a.searchClosure`.  The two `iff`-implication cases are discharged
    directly (their contents are visibly `⊆ a.searchClosure`); the constructor-child cases
    use the induction hypothesis. -/
theorem Formula.mem_searchClosure_trans :
    ∀ (a b c : Formula), b ∈ a.searchClosure -> c ∈ b.searchClosure -> c ∈ a.searchClosure := by
  intro a
  induction a with
  | atom n t u =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_singleton] at hb
      subst hb; exact hc
  | papp n t =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_singleton] at hb
      subst hb; exact hc
  | and φ ψ ihφ ihψ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons, List.mem_append] at hb ⊢
      rcases hb with rfl | hbφ | hbψ
      · simpa only [Formula.searchClosure, List.mem_cons, List.mem_append] using hc
      · exact Or.inr (Or.inl (ihφ b c hbφ hc))
      · exact Or.inr (Or.inr (ihψ b c hbψ hc))
  | or φ ψ ihφ ihψ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons, List.mem_append] at hb ⊢
      rcases hb with rfl | hbφ | hbψ
      · simpa only [Formula.searchClosure, List.mem_cons, List.mem_append] using hc
      · exact Or.inr (Or.inl (ihφ b c hbφ hc))
      · exact Or.inr (Or.inr (ihψ b c hbψ hc))
  | imp φ ψ ihφ ihψ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons, List.mem_append] at hb ⊢
      rcases hb with rfl | hbφ | hbψ
      · simpa only [Formula.searchClosure, List.mem_cons, List.mem_append] using hc
      · exact Or.inr (Or.inl (ihφ b c hbφ hc))
      · exact Or.inr (Or.inr (ihψ b c hbψ hc))
  | not φ ihφ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons] at hb ⊢
      rcases hb with rfl | hbφ
      · simpa only [Formula.searchClosure, List.mem_cons] using hc
      · exact Or.inr (ihφ b c hbφ hc)
  | iff φ ψ ihφ ihψ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons, List.mem_append] at hb ⊢
      rcases hb with rfl | rfl | rfl | hbφ | hbψ
      · -- b = iff φ ψ
        simpa only [Formula.searchClosure, List.mem_cons, List.mem_append] using hc
      · -- b = imp φ ψ
        simp only [Formula.searchClosure, List.mem_cons, List.mem_append] at hc
        rcases hc with rfl | hcφ | hcψ
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inl hcφ)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hcψ)))
      · -- b = imp ψ φ
        simp only [Formula.searchClosure, List.mem_cons, List.mem_append] at hc
        rcases hc with rfl | hcψ | hcφ
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hcψ)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hcφ)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (ihφ b c hbφ hc))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (ihψ b c hbψ hc))))
  | all n x φ ihφ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons] at hb ⊢
      rcases hb with rfl | hbφ
      · simpa only [Formula.searchClosure, List.mem_cons] using hc
      · exact Or.inr (ihφ b c hbφ hc)
  | ex n x φ ihφ =>
      intro b c hb hc
      simp only [Formula.searchClosure, List.mem_cons] at hb ⊢
      rcases hb with rfl | hbφ
      · simpa only [Formula.searchClosure, List.mem_cons] using hc
      · exact Or.inr (ihφ b c hbφ hc)

/-! ### Immediate-child membership facts (the shapes the rules introduce) -/

theorem Formula.not_child_mem (φ : Formula) : φ ∈ (Formula.not φ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons]
  exact Or.inr φ.self_mem_searchClosure

theorem Formula.and_child_left (φ ψ : Formula) : φ ∈ (Formula.and φ ψ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl φ.self_mem_searchClosure)

theorem Formula.and_child_right (φ ψ : Formula) : ψ ∈ (Formula.and φ ψ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr ψ.self_mem_searchClosure)

theorem Formula.or_child_left (φ ψ : Formula) : φ ∈ (Formula.or φ ψ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl φ.self_mem_searchClosure)

theorem Formula.or_child_right (φ ψ : Formula) : ψ ∈ (Formula.or φ ψ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr ψ.self_mem_searchClosure)

theorem Formula.imp_child_left (φ ψ : Formula) : φ ∈ (Formula.imp φ ψ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl φ.self_mem_searchClosure)

theorem Formula.imp_child_right (φ ψ : Formula) : ψ ∈ (Formula.imp φ ψ).searchClosure := by
  simp only [Formula.searchClosure, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr ψ.self_mem_searchClosure)

theorem Formula.iff_child_impL (φ ψ : Formula) :
    Formula.imp φ ψ ∈ (Formula.iff φ ψ).searchClosure := by
  simp [Formula.searchClosure]

theorem Formula.iff_child_impR (φ ψ : Formula) :
    Formula.imp ψ φ ∈ (Formula.iff φ ψ).searchClosure := by
  simp [Formula.searchClosure]

namespace Focused

/-! ## Focused search states and their backward transitions

    A search *state* is an `FSequent`.  A backward analytic rule turns a conclusion into
    one or two premises; `FStep S S'` holds when `S'` is a premise of some rule whose
    principal formula sits at the head of the appropriate side (the analytic calculus keeps
    the principal at the head — reordering to any position is handled by state
    normalization, a later slice).  This is the transition relation whose reachable set the
    finiteness bound counts. -/

/-- One backward analytic transition: `S` steps to premise `S'`. -/
inductive FStep : FSequent -> FSequent -> Prop where
  | negR {A Θ : List Formula} {φ : Formula} :
      FStep ⟨A, Formula.not φ :: Θ⟩ ⟨φ :: A, Θ⟩
  | negL {A Θ : List Formula} {φ : Formula} :
      FStep ⟨Formula.not φ :: A, Θ⟩ ⟨A, φ :: Θ⟩
  | impR {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨A, Formula.imp φ ψ :: Θ⟩ ⟨φ :: A, ψ :: Θ⟩
  | impL_left {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨Formula.imp φ ψ :: A, Θ⟩ ⟨A, φ :: Θ⟩
  | impL_right {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨Formula.imp φ ψ :: A, Θ⟩ ⟨ψ :: A, Θ⟩
  | andR_left {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨A, Formula.and φ ψ :: Θ⟩ ⟨A, φ :: Θ⟩
  | andR_right {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨A, Formula.and φ ψ :: Θ⟩ ⟨A, ψ :: Θ⟩
  | andL {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨Formula.and φ ψ :: A, Θ⟩ ⟨φ :: ψ :: A, Θ⟩
  | orR {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨A, Formula.or φ ψ :: Θ⟩ ⟨A, φ :: ψ :: Θ⟩
  | orL_left {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨Formula.or φ ψ :: A, Θ⟩ ⟨φ :: A, Θ⟩
  | orL_right {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨Formula.or φ ψ :: A, Θ⟩ ⟨ψ :: A, Θ⟩
  | iffR_left {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨A, Formula.iff φ ψ :: Θ⟩ ⟨A, Formula.imp φ ψ :: Θ⟩
  | iffR_right {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨A, Formula.iff φ ψ :: Θ⟩ ⟨A, Formula.imp ψ φ :: Θ⟩
  | iffL {A Θ : List Formula} {φ ψ : Formula} :
      FStep ⟨Formula.iff φ ψ :: A, Θ⟩ ⟨Formula.imp φ ψ :: Formula.imp ψ φ :: A, Θ⟩

/-- A formula set is **search-closed** when it contains the signed subformula closure of
    each of its members — i.e. it is closed under every shape a backward rule can expose. -/
def SearchClosed (C : List Formula) : Prop :=
  ∀ f ∈ C, ∀ g ∈ Formula.searchClosure f, g ∈ C

/-- A state lies **inside** `C` when every antecedent and succedent formula is in `C`. -/
def FSequent.InClosure (C : List Formula) (S : FSequent) : Prop :=
  (∀ f ∈ S.ante, f ∈ C) ∧ (∀ f ∈ S.succ, f ∈ C)

/-- In a search-closed `C`, if a *compound* principal `p` is in `C` then every subformula
    the rules expose from `p` is in `C`. -/
theorem SearchClosed.child {C : List Formula} (hC : SearchClosed C)
    {p g : Formula} (hp : p ∈ C) (hg : g ∈ Formula.searchClosure p) : g ∈ C :=
  hC p hp g hg

/-- **Closure preservation (step 2).**  Every backward analytic transition maps an
    in-closure state to an in-closure state: search never leaves the signed subformula
    closure `C`.  This is the analyticity property the `≤ 4^{|C|}` finite bound rests on. -/
theorem FStep.inClosure {C : List Formula} (hC : SearchClosed C)
    {S S' : FSequent} (hstep : FStep S S') (hS : S.InClosure C) : S'.InClosure C := by
  obtain ⟨hante, hsucc⟩ := hS
  cases hstep with
  | @negR A Θ φ =>
      have hnot : Formula.not φ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨?_, ?_⟩
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hnot (Formula.not_child_mem _)
        · exact hante _ hf
      · intro f hf; exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @negL A Θ φ =>
      have hnot : Formula.not φ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, ?_⟩
      · intro f hf; exact hante _ (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hnot (Formula.not_child_mem _)
        · exact hsucc _ hf
  | @impR A Θ φ ψ =>
      have himp : Formula.imp φ ψ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨?_, ?_⟩
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_left _ _)
        · exact hante _ hf
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_right _ _)
        · exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @impL_left A Θ φ ψ =>
      have himp : Formula.imp φ ψ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, ?_⟩
      · intro f hf; exact hante _ (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_left _ _)
        · exact hsucc _ hf
  | @impL_right A Θ φ ψ =>
      have himp : Formula.imp φ ψ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, ?_⟩
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_right _ _)
        · exact hante _ (List.mem_cons_of_mem _ hf)
      · intro f hf; exact hsucc _ hf
  | @andR_left A Θ φ ψ =>
      have hand : Formula.and φ ψ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨hante, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hand (Formula.and_child_left _ _)
      · exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @andR_right A Θ φ ψ =>
      have hand : Formula.and φ ψ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨hante, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hand (Formula.and_child_right _ _)
      · exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @andL A Θ φ ψ =>
      have hand : Formula.and φ ψ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, hsucc⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hand (Formula.and_child_left _ _)
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hand (Formula.and_child_right _ _)
        · exact hante _ (List.mem_cons_of_mem _ hf)
  | @orR A Θ φ ψ =>
      have hor : Formula.or φ ψ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨hante, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hor (Formula.or_child_left _ _)
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hor (Formula.or_child_right _ _)
        · exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @orL_left A Θ φ ψ =>
      have hor : Formula.or φ ψ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, hsucc⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hor (Formula.or_child_left _ _)
      · exact hante _ (List.mem_cons_of_mem _ hf)
  | @orL_right A Θ φ ψ =>
      have hor : Formula.or φ ψ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, hsucc⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hor (Formula.or_child_right _ _)
      · exact hante _ (List.mem_cons_of_mem _ hf)
  | @iffR_left A Θ φ ψ =>
      have hiff : Formula.iff φ ψ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨hante, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hiff (Formula.iff_child_impL _ _)
      · exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @iffR_right A Θ φ ψ =>
      have hiff : Formula.iff φ ψ ∈ C := hsucc _ List.mem_cons_self
      refine ⟨hante, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hiff (Formula.iff_child_impR _ _)
      · exact hsucc _ (List.mem_cons_of_mem _ hf)
  | @iffL A Θ φ ψ =>
      have hiff : Formula.iff φ ψ ∈ C := hante _ List.mem_cons_self
      refine ⟨?_, hsucc⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hiff (Formula.iff_child_impL _ _)
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hiff (Formula.iff_child_impR _ _)
        · exact hante _ (List.mem_cons_of_mem _ hf)

end Focused
end ContextualHOL
