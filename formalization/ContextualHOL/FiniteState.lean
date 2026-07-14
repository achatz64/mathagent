import ContextualHOL.Focused

/-!
# PS2 — finite-state search: the signed subformula closure and rule closure

This module builds the *finite-state / termination* branch of PS2.  Per the audit,
finiteness is established for the **analytic** state representation (the two-sided
`FSequent` of `Focused.lean`, intended to underlie the later focused calculus), not for the
unfocused `FDeriv` trace language.  `FSequent` still stores *lists*, so the finite bound is
stated over a **normalized set-key** (`normKey`), not over raw sequents.

The backbone is the **signed subformula closure** `Formula.searchClosure`: the smallest
formula set containing `φ` and closed under taking immediate subformulas *and*, for each
`iff φ ψ`, the two implications `imp φ ψ`, `imp ψ φ` that the `iff` rules introduce.  Every
backward analytic rule replaces a principal formula by formulas drawn from its closure, so
a sequent whose formulas all lie in a closed set `C` steps only to sequents with the same
property (`FStep.inClosure`).  A normalized state is a pair of **sub-sets** of `C`, of which
there are `≤ 4^{|C|}` (`finiteStateProp`); the normalized key is canonical (`normKey_congr`)
and — on in-closure states — faithful (`mem_normKey_ante_iff`), so the reachable normalized
search space is genuinely finite (`reachable_key_faithful_finite`).

Ordering of the branch (per audit): (1) state + transitions [`FStep`]; (2) closure
[`FStep.inClosure`]; (3) normalized key + the `≤ 4^{|C|}` finite bound [`normKey`,
`finiteStateProp`] — this slice; (4) memoized BFS + termination, which additionally needs a
bridge re-attaching `FTrace`'s `liftFormula?` / `LiftsAllF` guards to `FStep` (see the TODO
at the end).
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

/-! ### A self-contained powerset (for the `2^|C|` / `4^|C|` count)

    Batteries' `List.sublists` is off-limits (core Lean 4 only), so we roll our own
    order-preserving powerset `powerList` and prove the two facts step 3 needs of it:
    it has `2^|l|` elements, and every `filter` of `l` is one of them. -/

/-- All order-preserving sub-lists of `l` (a hand-rolled powerset). -/
def powerList : {α : Type} → List α → List (List α)
  | _, [] => [[]]
  | _, a :: l => powerList l ++ (powerList l).map (a :: ·)

/-- The powerset has `2^|l|` elements. -/
theorem length_powerList {α : Type} (l : List α) :
    (powerList l).length = 2 ^ l.length := by
  induction l with
  | nil => simp [powerList]
  | cons a l ih =>
      simp only [powerList, List.length_append, List.length_map, ih, List.length_cons,
        Nat.pow_succ]
      omega

/-- Every `filter` of `l` is a sub-list, hence a member of the powerset. -/
theorem filter_mem_powerList {α : Type} (p : α → Bool) (l : List α) :
    l.filter p ∈ powerList l := by
  induction l with
  | nil => simp [powerList]
  | cons a l ih =>
      simp only [powerList, List.mem_append, List.mem_map, List.filter_cons]
      by_cases h : p a
      · exact Or.inr ⟨l.filter p, ih, by simp [h]⟩
      · exact Or.inl (by simpa [h] using ih)

namespace Focused

/-! ## Analytic search states and their backward transitions

    A search *state* is an `FSequent` (the analytic substrate meant to underlie the later
    focused calculus).  A backward analytic rule turns a conclusion into one or two premises;
    `FStep S S'` holds when `S'` is a premise of some rule whose principal formula sits at the
    head of the appropriate side (the principal is kept at the head — reordering to any
    position is handled by state normalization, a later slice).  `FStep` is an *untyped
    over-approximation* of `FTrace`: it deliberately omits the `liftFormula?` / `LiftsAllF`
    side conditions, which keeps the closure/counting argument clean but must be bridged
    before `FStep` becomes the BFS relation (see the TODO at the end of the file).  This is
    the transition relation whose reachable set the finiteness bound counts. -/

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

/-! ## Step 3 — the normalized key and the `≤ 4^{|C|}` finite bound

    `FStep.inClosure` says the *lists* stay inside `C`, but a raw `FSequent` still carries
    ordering and duplicate formulas, so the states themselves are not yet a finite set.  The
    counting argument is about **sets**: a normalized state is a pair of subsets of `C`, of
    which there are `2^{|C|} · 2^{|C|} = 4^{|C|}`.

    We make that precise with a canonical **normalized key** `normKey C S`: filter `C` by
    membership in each side of `S`.  This collapses ordering and duplicates (two states with
    the same ante/succ *sets* get identical keys — `normKey_congr`), always lands in the
    powerset of `C` (`normKey_mem_allKeys`), and — for in-closure states — loses no
    information (`mem_normKey_ante_iff`).  The reachable, in-closure normalized states
    therefore inject into a master list of `≤ 4^{|C|}` keys (`finiteStateProp`). -/

/-- Boolean membership test built from `DecidableEq Formula` alone (core's `Decidable (· ∈ ·)`
    for lists needs `LawfulBEq`, which `Formula` does not derive). -/
def memb (f : Formula) (l : List Formula) : Bool :=
  l.any (fun g => decide (f = g))

/-- `memb` decides list membership. -/
theorem memb_iff (f : Formula) (l : List Formula) : memb f l = true ↔ f ∈ l := by
  simp only [memb, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨g, hg, h⟩ => h ▸ hg, fun h => ⟨f, h, rfl⟩⟩

/-- Two `Bool`s are equal when they agree as propositions. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The canonical **normalized key** of a state relative to a closure `C`: each side is
    `C` filtered by membership, which discards ordering and duplicates.  States that agree
    on their ante/succ *sets* (as subsets of `C`) get the same key. -/
def normKey (C : List Formula) (S : FSequent) : List Formula × List Formula :=
  (C.filter (memb · S.ante), C.filter (memb · S.succ))

/-- The key is canonical: it depends only on the ante/succ **sets**, not on order or
    multiplicity.  (This is what makes it a genuine set-quotient rather than a relabelled
    `FSequent`.) -/
theorem normKey_congr (C : List Formula) {S S' : FSequent}
    (ha : ∀ f, f ∈ S.ante ↔ f ∈ S'.ante) (hs : ∀ f, f ∈ S.succ ↔ f ∈ S'.succ) :
    normKey C S = normKey C S' := by
  simp only [normKey]
  congr 1
  · exact List.filter_congr fun f _ =>
      bool_eq_of_iff (by rw [memb_iff, memb_iff]; exact ha f)
  · exact List.filter_congr fun f _ =>
      bool_eq_of_iff (by rw [memb_iff, memb_iff]; exact hs f)

/-! ### The master list of keys and the `4^{|C|}` count -/

/-- All possible normalized keys over `C`: a pair of powerset elements. -/
def allKeys (C : List Formula) : List (List Formula × List Formula) :=
  (powerList C).flatMap (fun a => (powerList C).map (fun s => (a, s)))

/-- A `flatMap` whose inner lists all have length `|t|` has length `|l| · |t|`. -/
theorem length_flatMap_const {α β γ : Type} (l : List α) (t : List γ) (g : α → γ → β) :
    (l.flatMap (fun a => t.map (g a))).length = l.length * t.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

/-- The master list has exactly `2^{|C|} · 2^{|C|}` keys. -/
theorem length_allKeys (C : List Formula) :
    (allKeys C).length = 2 ^ C.length * 2 ^ C.length := by
  rw [allKeys, length_flatMap_const, length_powerList]

/-- `2^n · 2^n = 4^n` (self-contained; no Mathlib `ring`/`Nat.mul_pow`). -/
theorem two_pow_mul_two_pow (n : Nat) : 2 ^ n * 2 ^ n = 4 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      calc 2 ^ n * 2 * (2 ^ n * 2)
          = 2 ^ n * 2 ^ n * (2 * 2) := by ac_rfl
        _ = 4 ^ n * 4 := by rw [ih]

/-- Any pair of powerset elements is a key. -/
theorem mem_allKeys {C : List Formula} {a s : List Formula}
    (ha : a ∈ powerList C) (hs : s ∈ powerList C) : (a, s) ∈ allKeys C := by
  simp only [allKeys, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, s, hs, rfl⟩

/-- Every normalized key lands in the master list — unconditionally, since each side is a
    `filter` of `C`. -/
theorem normKey_mem_allKeys (C : List Formula) (S : FSequent) :
    normKey C S ∈ allKeys C :=
  mem_allKeys (filter_mem_powerList _ C) (filter_mem_powerList _ C)

/-- **Fidelity (antecedent).**  For an in-closure state the normalized key loses nothing:
    its antecedent side has exactly the antecedent formulas.  Hence distinct in-closure
    set-states get distinct keys — the key is a faithful injection on the search domain. -/
theorem mem_normKey_ante_iff {C : List Formula} {S : FSequent}
    (hS : S.InClosure C) (f : Formula) : f ∈ (normKey C S).1 ↔ f ∈ S.ante := by
  simp only [normKey, List.mem_filter, memb_iff]
  exact ⟨fun h => h.2, fun h => ⟨hS.1 f h, h⟩⟩

/-- **Fidelity (succedent).** -/
theorem mem_normKey_succ_iff {C : List Formula} {S : FSequent}
    (hS : S.InClosure C) (f : Formula) : f ∈ (normKey C S).2 ↔ f ∈ S.succ := by
  simp only [normKey, List.mem_filter, memb_iff]
  exact ⟨fun h => h.2, fun h => ⟨hS.2 f h, h⟩⟩

/-- **`finiteStateProp` — the finite bound.**  There is a master list of `≤ 4^{|C|}`
    normalized keys that contains the key of *every* state over `C`.  Together with
    `FStep.inClosure` (search stays in `C`) and the fidelity lemmas (the key faithfully
    represents an in-closure state), this is the finiteness of the normalized search space:
    at most `4^{|C|}` distinct reachable states. -/
theorem finiteStateProp (C : List Formula) :
    ∃ master : List (List Formula × List Formula),
      master.length ≤ 4 ^ C.length ∧
      ∀ S : FSequent, normKey C S ∈ master := by
  refine ⟨allKeys C, Nat.le_of_eq ?_, fun S => normKey_mem_allKeys C S⟩
  rw [length_allKeys, two_pow_mul_two_pow]

/-! ### Reachability: the reachable search space stays finite -/

/-- Reflexive–transitive closure of `FStep` (self-contained; no Mathlib `ReflTransGen`). -/
inductive FStepStar : FSequent -> FSequent -> Prop where
  | refl (S : FSequent) : FStepStar S S
  | step {S T U : FSequent} : FStep S T -> FStepStar T U -> FStepStar S U

/-- Reachability preserves in-closure: from an in-closure start, every reachable state is
    still in `C`.  (Iterates `FStep.inClosure`.) -/
theorem FStepStar.inClosure {C : List Formula} (hC : SearchClosed C) {S S' : FSequent}
    (h : FStepStar S S') : S.InClosure C -> S'.InClosure C := by
  induction h with
  | refl S => exact id
  | step hst _ ih => exact fun hS => ih (FStep.inClosure hC hst hS)

/-- **Capstone.**  From an in-closure start `S₀`, every `FStep*`-reachable state `S` has a
    key inside the `≤ 4^{|C|}` master list, and that key faithfully represents `S` (loses no
    ante/succ formula).  So the reachable normalized search space is finite. -/
theorem reachable_key_faithful_finite {C : List Formula} (hC : SearchClosed C)
    {S₀ S : FSequent} (h0 : S₀.InClosure C) (h : FStepStar S₀ S) :
    normKey C S ∈ allKeys C ∧
    (∀ f, f ∈ (normKey C S).1 ↔ f ∈ S.ante) ∧
    (∀ f, f ∈ (normKey C S).2 ↔ f ∈ S.succ) :=
  have hS : S.InClosure C := FStepStar.inClosure hC h h0
  ⟨normKey_mem_allKeys C S, fun f => mem_normKey_ante_iff hS f,
    fun f => mem_normKey_succ_iff hS f⟩

/-! ### The closure of a search goal

    Assembling `C` for an actual goal `G`: the union of the signed subformula closures of
    `G`'s formulas.  It is search-closed and contains `G`, so `finiteStateProp` applies to
    the search started from `⟨[], G⟩`. -/

/-- The signed subformula closure of a whole goal (list of formulas). -/
def goalClosure (G : List Formula) : List Formula :=
  G.flatMap Formula.searchClosure

/-- The goal closure is search-closed (uses closure transitivity). -/
theorem searchClosed_goalClosure (G : List Formula) : SearchClosed (goalClosure G) := by
  intro f hf g hg
  simp only [goalClosure, List.mem_flatMap] at hf ⊢
  obtain ⟨h, hhG, hfh⟩ := hf
  exact ⟨h, hhG, Formula.mem_searchClosure_trans h f g hfh hg⟩

/-- The initial sequent `⟨[], G⟩` lies inside the goal closure. -/
theorem initial_inClosure (G : List Formula) :
    (⟨[], G⟩ : FSequent).InClosure (goalClosure G) := by
  refine ⟨fun f hf => absurd hf List.not_mem_nil, fun f hf => ?_⟩
  simp only [goalClosure, List.mem_flatMap]
  exact ⟨f, hf, f.self_mem_searchClosure⟩

/-- **Goal-level finiteness.**  Every state reachable from `⟨[], G⟩` has a faithful key in a
    master list of `≤ 4^{|goalClosure G|}` keys: the search space for goal `G` is finite. -/
theorem finiteStateProp_goal (G : List Formula) {S : FSequent}
    (h : FStepStar ⟨[], G⟩ S) :
    normKey (goalClosure G) S ∈ allKeys (goalClosure G) ∧
    (∀ f, f ∈ (normKey (goalClosure G) S).1 ↔ f ∈ S.ante) ∧
    (∀ f, f ∈ (normKey (goalClosure G) S).2 ↔ f ∈ S.succ) :=
  reachable_key_faithful_finite (searchClosed_goalClosure G) (initial_inClosure G) h

/-! ## Step 4, gate 1 — order-insensitive (key-level) transitions

    `normKey` erases list order, but `FStep` only decomposes the *head* of a side, so two
    list-states with the same key can expose different `FStep` moves.  To search over keys
    we need an order-insensitive transition.  `FStepArb` reorders a side (a permutation)
    before stepping at the head, so *any* member can be principal; it contains `FStep`
    (`FStep.toArb`), is invariant under permuting the source (`FStepArb.of_seqPerm`), and
    preserves the closure (`FStepArb.inClosure`).  Combined with `normKey` being exactly the
    quotient by same-sets (`normKey_eq_of_setEq` / `setEq_of_normKey_eq`), this is the
    coherence layer the key-level search rests on.

    Still open (later gate-1/2 slices): the full quotient by `SetEq` (permutation handles
    reordering but not duplicate multiplicity), and retaining two-premise rules
    (`andR`,`orL`,`impL`,`iffR`) as **AND/OR hyperedges** rather than single `S → S'` edges,
    so the key-level object is a proof-search hypergraph — a plain graph BFS is insufficient. -/

/-- Two states have the same ante/succ **sets** — the equivalence `normKey` quotients by. -/
def SetEq (S S' : FSequent) : Prop :=
  (∀ f, f ∈ S.ante ↔ f ∈ S'.ante) ∧ (∀ f, f ∈ S.succ ↔ f ∈ S'.succ)

theorem SetEq.refl (S : FSequent) : SetEq S S := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem SetEq.symm {S S' : FSequent} (h : SetEq S S') : SetEq S' S :=
  ⟨fun f => (h.1 f).symm, fun f => (h.2 f).symm⟩

theorem SetEq.trans {S S' S'' : FSequent} (h : SetEq S S') (h' : SetEq S' S'') :
    SetEq S S'' :=
  ⟨fun f => (h.1 f).trans (h'.1 f), fun f => (h.2 f).trans (h'.2 f)⟩

/-- `normKey` respects `SetEq`: same sets give the same key (unconditional). -/
theorem normKey_eq_of_setEq {C : List Formula} {S S' : FSequent} (h : SetEq S S') :
    normKey C S = normKey C S' :=
  normKey_congr C h.1 h.2

/-- `normKey` is complete for `SetEq` on in-closure states: equal keys ⟹ same sets. -/
theorem setEq_of_normKey_eq {C : List Formula} {S S' : FSequent}
    (hS : S.InClosure C) (hS' : S'.InClosure C) (h : normKey C S = normKey C S') :
    SetEq S S' := by
  refine ⟨fun f => ?_, fun f => ?_⟩
  · rw [← mem_normKey_ante_iff hS f, ← mem_normKey_ante_iff hS' f, h]
  · rw [← mem_normKey_succ_iff hS f, ← mem_normKey_succ_iff hS' f, h]

/-- Two states equal up to reordering each side (a permutation of ante and of succ). -/
def SeqPerm (S S' : FSequent) : Prop :=
  List.Perm S.ante S'.ante ∧ List.Perm S.succ S'.succ

theorem SeqPerm.refl (S : FSequent) : SeqPerm S S :=
  ⟨List.Perm.refl _, List.Perm.refl _⟩

/-- A permutation of the sides is in particular a `SetEq`. -/
theorem SeqPerm.toSetEq {S S' : FSequent} (h : SeqPerm S S') : SetEq S S' :=
  ⟨fun f => h.1.mem_iff (a := f), fun f => h.2.mem_iff (a := f)⟩

theorem SeqPerm.inClosure {C : List Formula} {S T : FSequent}
    (hp : SeqPerm S T) (hS : S.InClosure C) : T.InClosure C :=
  ⟨fun f hf => hS.1 f (hp.1.mem_iff.mpr hf), fun f hf => hS.2 f (hp.2.mem_iff.mpr hf)⟩

/-- **Order-insensitive transition.**  Reorder a side so the intended principal is at the
    head, then take an `FStep`.  Any member of a side can thus be principal — matching the
    key, which has no order. -/
def FStepArb (S S' : FSequent) : Prop :=
  ∃ T, SeqPerm S T ∧ FStep T S'

/-- `FStep` is the special case with no reordering. -/
theorem FStep.toArb {S S' : FSequent} (h : FStep S S') : FStepArb S S' :=
  ⟨S, SeqPerm.refl S, h⟩

/-- **Key-level coherence (up to reordering).**  `FStepArb` is invariant under permuting the
    source, so permutation-equivalent representatives of a key expose the same `FStepArb`
    successors — the property `FStep` alone lacked. -/
theorem FStepArb.of_seqPerm {S S₂ S' : FSequent} (hp : SeqPerm S S₂) (h : FStepArb S₂ S') :
    FStepArb S S' := by
  obtain ⟨T, hpT, hst⟩ := h
  exact ⟨T, ⟨hp.1.trans hpT.1, hp.2.trans hpT.2⟩, hst⟩

/-- `FStepArb` preserves the closure (reorder, then `FStep.inClosure`). -/
theorem FStepArb.inClosure {C : List Formula} (hC : SearchClosed C) {S S' : FSequent}
    (h : FStepArb S S') (hS : S.InClosure C) : S'.InClosure C := by
  obtain ⟨T, hp, hst⟩ := h
  exact FStep.inClosure hC hst (hp.inClosure hS)

/-! ## Step 4 — the normalized AND/OR hypergraph on set-keys

    A two-way *one-step* simulation of `FStepArb` by a deduplicated key relation is
    **impossible**, because deduplication changes the operational rule — contraction is baked
    into the set level, it is not a missing coherence lemma.  (Counterexample: let the
    antecedent hold two copies of `and p q`.  Raw `FStepArb` applies `andL` to one copy and
    leaves the other, giving the set `{and p q, p, q}`; the deduplicated representative has a
    single copy and yields `{p, q}` — different keys.  The same happens on the succedent.)

    So the search rule is defined **directly on set-keys**: pick a principal *anywhere* in a
    side (membership, not head — `FStepArb`'s reordering is subsumed), delete it at set level
    (`sremove`), add its rule components, and — crucially — keep *all* premises of a
    two-premise rule (`andR`,`orL`,`impL`,`iffR`) together as **one hyperedge** (a premise
    *list*).  `KProvable` is then the AND/OR reachability over this hypergraph: a key is
    provable iff it is an identity axiom, or *some* rule reduces it to premises that are *all*
    provable.

    This makes the rule a genuine relation on sets: it respects `SetEq` (`KStep.respects_setEq`
    — permutation *and* duplicate multiplicity, the full quotient `FStepArb` could not reach),
    it keeps the search inside the closure (`KStep.inClosure`), and — via `normKey` — the
    reachable keys are the same `≤ 4^{|C|}` finite set.  What remains is the typed bridge and
    the correspondence with `FTrace`/`ProvesProp` derivations via contraction/exchange
    admissibility (recorded as a TODO): a *normalized-hyperderivation* ↔ real-derivation
    theorem, not a raw one-step equality. -/

/-- Set-level removal of a formula: drop *every* occurrence of `p` (uses `DecidableEq Formula`
    directly, so no `LawfulBEq` is needed). -/
def sremove (p : Formula) (l : List Formula) : List Formula :=
  l.filter (fun g => decide (g ≠ p))

/-- Membership in `sremove`: everything of `l` except `p`. -/
theorem mem_sremove {p f : Formula} {l : List Formula} :
    f ∈ sremove p l ↔ f ∈ l ∧ f ≠ p := by
  simp only [sremove, List.mem_filter, decide_eq_true_eq]

/-- **The set-key hyperrule.**  `KStep S ps` holds when some backward analytic rule fires on a
    principal formula occurring *anywhere* in a side of `S`, producing the premise list `ps`
    (its **hyperedge**): the principal is deleted at set level and its components added.
    Two-premise rules (`andR`,`orL`,`impL`,`iffR`) produce a two-element `ps` — an AND-node —
    so the hypergraph structure is retained rather than flattened to `S → S'` edges. -/
inductive KStep : FSequent -> List FSequent -> Prop where
  | andL {A Θ : List Formula} {φ ψ : Formula} (h : Formula.and φ ψ ∈ A) :
      KStep ⟨A, Θ⟩ [⟨φ :: ψ :: sremove (Formula.and φ ψ) A, Θ⟩]
  | andR {A Θ : List Formula} {φ ψ : Formula} (h : Formula.and φ ψ ∈ Θ) :
      KStep ⟨A, Θ⟩ [⟨A, φ :: sremove (Formula.and φ ψ) Θ⟩, ⟨A, ψ :: sremove (Formula.and φ ψ) Θ⟩]
  | orR {A Θ : List Formula} {φ ψ : Formula} (h : Formula.or φ ψ ∈ Θ) :
      KStep ⟨A, Θ⟩ [⟨A, φ :: ψ :: sremove (Formula.or φ ψ) Θ⟩]
  | orL {A Θ : List Formula} {φ ψ : Formula} (h : Formula.or φ ψ ∈ A) :
      KStep ⟨A, Θ⟩ [⟨φ :: sremove (Formula.or φ ψ) A, Θ⟩, ⟨ψ :: sremove (Formula.or φ ψ) A, Θ⟩]
  | impR {A Θ : List Formula} {φ ψ : Formula} (h : Formula.imp φ ψ ∈ Θ) :
      KStep ⟨A, Θ⟩ [⟨φ :: A, ψ :: sremove (Formula.imp φ ψ) Θ⟩]
  | impL {A Θ : List Formula} {φ ψ : Formula} (h : Formula.imp φ ψ ∈ A) :
      KStep ⟨A, Θ⟩ [⟨sremove (Formula.imp φ ψ) A, φ :: Θ⟩, ⟨ψ :: sremove (Formula.imp φ ψ) A, Θ⟩]
  | negR {A Θ : List Formula} {φ : Formula} (h : Formula.not φ ∈ Θ) :
      KStep ⟨A, Θ⟩ [⟨φ :: A, sremove (Formula.not φ) Θ⟩]
  | negL {A Θ : List Formula} {φ : Formula} (h : Formula.not φ ∈ A) :
      KStep ⟨A, Θ⟩ [⟨sremove (Formula.not φ) A, φ :: Θ⟩]
  | iffR {A Θ : List Formula} {φ ψ : Formula} (h : Formula.iff φ ψ ∈ Θ) :
      KStep ⟨A, Θ⟩ [⟨A, Formula.imp φ ψ :: sremove (Formula.iff φ ψ) Θ⟩,
                    ⟨A, Formula.imp ψ φ :: sremove (Formula.iff φ ψ) Θ⟩]
  | iffL {A Θ : List Formula} {φ ψ : Formula} (h : Formula.iff φ ψ ∈ A) :
      KStep ⟨A, Θ⟩ [⟨Formula.imp φ ψ :: Formula.imp ψ φ :: sremove (Formula.iff φ ψ) A, Θ⟩]

/-- **AND/OR provability over the hypergraph.**  A key is provable if it is an identity axiom
    (some formula on both sides), or some rule reduces it to a hyperedge whose premises are
    *all* provable.  (`∀ P ∈ ps, KProvable P` is the AND over a hyperedge; the choice of rule
    is the OR.) -/
inductive KProvable : FSequent -> Prop where
  | ax {A Θ : List Formula} {f : Formula} (hA : f ∈ A) (hΘ : f ∈ Θ) : KProvable ⟨A, Θ⟩
  | rule {S : FSequent} {ps : List FSequent}
      (hstep : KStep S ps) (hpr : ∀ P ∈ ps, KProvable P) : KProvable S

/-- **Analyticity of the hypergraph (gate 2's closure lemma).**  Every premise of every
    hyperedge fired from an in-closure key is itself in-closure: the set-key search never
    leaves the signed subformula closure `C`.  (The mirror of `FStep.inClosure` for the
    hyperrule.) -/
theorem KStep.inClosure {C : List Formula} (hC : SearchClosed C) {S : FSequent}
    {ps : List FSequent} (hstep : KStep S ps) (hS : S.InClosure C) :
    ∀ P ∈ ps, P.InClosure C := by
  obtain ⟨hante, hsucc⟩ := hS
  cases hstep with
  | @andL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hand : Formula.and φ ψ ∈ C := hante _ hmem
      refine ⟨fun f hf => ?_, hsucc⟩
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hand (Formula.and_child_left _ _)
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hand (Formula.and_child_right _ _)
      · exact hante _ (mem_sremove.mp hf).1
  | @andR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      have hand : Formula.and φ ψ ∈ C := hsucc _ hmem
      rcases hP with rfl | rfl
      · refine ⟨hante, fun f hf => ?_⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hand (Formula.and_child_left _ _)
        · exact hsucc _ (mem_sremove.mp hf).1
      · refine ⟨hante, fun f hf => ?_⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hand (Formula.and_child_right _ _)
        · exact hsucc _ (mem_sremove.mp hf).1
  | @orR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hor : Formula.or φ ψ ∈ C := hsucc _ hmem
      refine ⟨hante, fun f hf => ?_⟩
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hor (Formula.or_child_left _ _)
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hor (Formula.or_child_right _ _)
      · exact hsucc _ (mem_sremove.mp hf).1
  | @orL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      have hor : Formula.or φ ψ ∈ C := hante _ hmem
      rcases hP with rfl | rfl
      · refine ⟨fun f hf => ?_, hsucc⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hor (Formula.or_child_left _ _)
        · exact hante _ (mem_sremove.mp hf).1
      · refine ⟨fun f hf => ?_, hsucc⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hor (Formula.or_child_right _ _)
        · exact hante _ (mem_sremove.mp hf).1
  | @impR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have himp : Formula.imp φ ψ ∈ C := hsucc _ hmem
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_left _ _)
        · exact hante _ hf
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_right _ _)
        · exact hsucc _ (mem_sremove.mp hf).1
  | @impL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      have himp : Formula.imp φ ψ ∈ C := hante _ hmem
      rcases hP with rfl | rfl
      · refine ⟨fun f hf => ?_, fun f hf => ?_⟩
        · exact hante _ (mem_sremove.mp hf).1
        · rcases List.mem_cons.1 hf with rfl | hf
          · exact hC.child himp (Formula.imp_child_left _ _)
          · exact hsucc _ hf
      · refine ⟨fun f hf => ?_, hsucc⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child himp (Formula.imp_child_right _ _)
        · exact hante _ (mem_sremove.mp hf).1
  | @negR A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hnot : Formula.not φ ∈ C := hsucc _ hmem
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hnot (Formula.not_child_mem _)
        · exact hante _ hf
      · exact hsucc _ (mem_sremove.mp hf).1
  | @negL A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hnot : Formula.not φ ∈ C := hante _ hmem
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · exact hante _ (mem_sremove.mp hf).1
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hnot (Formula.not_child_mem _)
        · exact hsucc _ hf
  | @iffR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      have hiff : Formula.iff φ ψ ∈ C := hsucc _ hmem
      rcases hP with rfl | rfl
      · refine ⟨hante, fun f hf => ?_⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hiff (Formula.iff_child_impL _ _)
        · exact hsucc _ (mem_sremove.mp hf).1
      · refine ⟨hante, fun f hf => ?_⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hC.child hiff (Formula.iff_child_impR _ _)
        · exact hsucc _ (mem_sremove.mp hf).1
  | @iffL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hiff : Formula.iff φ ψ ∈ C := hante _ hmem
      refine ⟨fun f hf => ?_, hsucc⟩
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hiff (Formula.iff_child_impL _ _)
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hC.child hiff (Formula.iff_child_impR _ _)
      · exact hante _ (mem_sremove.mp hf).1

/-! ### The hyperrule is well-defined on set-keys (the real gate-1 fix)

    `FStepArb` gave coherence only up to *reordering*; the set-level rule gives coherence up to
    the *full* `SetEq` (reordering **and** duplicate multiplicity), because it selects the
    principal by membership and deletes it at set level.  `KStep.respects_setEq` proves it:
    `SetEq`-equal keys expose `SetEq`-equal hyperedges. -/

/-- Congruence of `∈` through a `cons`. -/
theorem mem_cons_congr {a f : Formula} {l l' : List Formula}
    (h : f ∈ l ↔ f ∈ l') : (f ∈ a :: l) ↔ (f ∈ a :: l') := by
  simp only [List.mem_cons, h]

/-- Congruence of `∈` through `sremove` (same sets ⟹ same `sremove` sets). -/
theorem mem_sremove_congr {p : Formula} {A A' : List Formula}
    (hA : ∀ g, g ∈ A ↔ g ∈ A') (f : Formula) :
    f ∈ sremove p A ↔ f ∈ sremove p A' := by
  simp only [mem_sremove, hA f]

/-- Pointwise `SetEq` of two premise lists (self-contained; avoids a `List.Forall₂`
    dependency). -/
def SetEqAll : List FSequent -> List FSequent -> Prop
  | [], [] => True
  | P :: ps, P' :: ps' => SetEq P P' ∧ SetEqAll ps ps'
  | _, _ => False

/-- **The hyperrule respects `SetEq` (full quotient coherence).**  If `S` and `S'` have the
    same ante/succ *sets* and `S` fires a hyperedge `ps`, then `S'` fires a corresponding
    hyperedge `ps'` with each premise `SetEq` to `ps`'s.  So `KStep` descends to a relation on
    set-keys — the well-definedness that a one-step `FStepArb` quotient could not have. -/
theorem KStep.respects_setEq {S S' : FSequent} (h : SetEq S S')
    {ps : List FSequent} (hstep : KStep S ps) :
    ∃ ps', KStep S' ps' ∧ SetEqAll ps ps' := by
  cases hstep with
  | @andL A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨φ :: ψ :: sremove (Formula.and φ ψ) A', Θ'⟩], KStep.andL ((hA _).mp hmem),
        ⟨fun f => mem_cons_congr (mem_cons_congr (mem_sremove_congr hA f)), fun f => hΘ f⟩,
        trivial⟩
  | @andR A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨A', φ :: sremove (Formula.and φ ψ) Θ'⟩, ⟨A', ψ :: sremove (Formula.and φ ψ) Θ'⟩],
        KStep.andR ((hΘ _).mp hmem),
        ⟨fun f => hA f, fun f => mem_cons_congr (mem_sremove_congr hΘ f)⟩,
        ⟨fun f => hA f, fun f => mem_cons_congr (mem_sremove_congr hΘ f)⟩, trivial⟩
  | @orR A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨A', φ :: ψ :: sremove (Formula.or φ ψ) Θ'⟩], KStep.orR ((hΘ _).mp hmem),
        ⟨fun f => hA f, fun f => mem_cons_congr (mem_cons_congr (mem_sremove_congr hΘ f))⟩,
        trivial⟩
  | @orL A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨φ :: sremove (Formula.or φ ψ) A', Θ'⟩, ⟨ψ :: sremove (Formula.or φ ψ) A', Θ'⟩],
        KStep.orL ((hA _).mp hmem),
        ⟨fun f => mem_cons_congr (mem_sremove_congr hA f), fun f => hΘ f⟩,
        ⟨fun f => mem_cons_congr (mem_sremove_congr hA f), fun f => hΘ f⟩, trivial⟩
  | @impR A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨φ :: A', ψ :: sremove (Formula.imp φ ψ) Θ'⟩], KStep.impR ((hΘ _).mp hmem),
        ⟨fun f => mem_cons_congr (hA f), fun f => mem_cons_congr (mem_sremove_congr hΘ f)⟩,
        trivial⟩
  | @impL A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨sremove (Formula.imp φ ψ) A', φ :: Θ'⟩, ⟨ψ :: sremove (Formula.imp φ ψ) A', Θ'⟩],
        KStep.impL ((hA _).mp hmem),
        ⟨fun f => mem_sremove_congr hA f, fun f => mem_cons_congr (hΘ f)⟩,
        ⟨fun f => mem_cons_congr (mem_sremove_congr hA f), fun f => hΘ f⟩, trivial⟩
  | @negR A Θ φ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨φ :: A', sremove (Formula.not φ) Θ'⟩], KStep.negR ((hΘ _).mp hmem),
        ⟨fun f => mem_cons_congr (hA f), fun f => mem_sremove_congr hΘ f⟩, trivial⟩
  | @negL A Θ φ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨sremove (Formula.not φ) A', φ :: Θ'⟩], KStep.negL ((hA _).mp hmem),
        ⟨fun f => mem_sremove_congr hA f, fun f => mem_cons_congr (hΘ f)⟩, trivial⟩
  | @iffR A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨A', Formula.imp φ ψ :: sremove (Formula.iff φ ψ) Θ'⟩,
              ⟨A', Formula.imp ψ φ :: sremove (Formula.iff φ ψ) Θ'⟩],
        KStep.iffR ((hΘ _).mp hmem),
        ⟨fun f => hA f, fun f => mem_cons_congr (mem_sremove_congr hΘ f)⟩,
        ⟨fun f => hA f, fun f => mem_cons_congr (mem_sremove_congr hΘ f)⟩, trivial⟩
  | @iffL A Θ φ ψ hmem =>
      obtain ⟨A', Θ'⟩ := S'; obtain ⟨hA, hΘ⟩ := h
      exact ⟨[⟨Formula.imp φ ψ :: Formula.imp ψ φ :: sremove (Formula.iff φ ψ) A', Θ'⟩],
        KStep.iffL ((hA _).mp hmem),
        ⟨fun f => mem_cons_congr (mem_cons_congr (mem_sremove_congr hA f)), fun f => hΘ f⟩,
        trivial⟩

/-! ### Monotonicity of `KProvable` (weakening + `SetEq`-invariance)

    Two structural admissibilities the completeness simulation needs *regardless* of how the
    contraction gate is discharged.  Both hold because the set-key rule picks its principal by
    **membership**, deletes it by **set-level** `sremove`, and never touches the passive
    context except to grow it: enlarging either side keeps every axiom firing and keeps every
    rule's principal available, and `sremove` is monotone, so each hyperedge premise stays
    reachable under enlargement.  (These go from *fewer* to *more* resources — the easy
    direction; the hard, contraction direction is the separate gate below.) -/

/-- Enlarging a list monotonically at a fixed head. -/
private theorem cons_mono {a : Formula} {l l' : List Formula}
    (h : ∀ x, x ∈ l → x ∈ l') : ∀ x, x ∈ a :: l → x ∈ a :: l' :=
  fun x hx => List.mem_cons.2 ((List.mem_cons.1 hx).imp id (h x))

/-- Set-level removal is monotone: enlarging the list enlarges its `sremove`. -/
private theorem sremove_mono {p : Formula} {l l' : List Formula}
    (h : ∀ x, x ∈ l → x ∈ l') : ∀ x, x ∈ sremove p l → x ∈ sremove p l' :=
  fun x hx => mem_sremove.2 ⟨h x (mem_sremove.1 hx).1, (mem_sremove.1 hx).2⟩

/-- **Weakening of `KProvable`.**  A provable key stays provable when *either* side is enlarged
    (setwise).  Proof: induction on the derivation; the identity axiom survives (its witness is
    still on both sides), and every rule re-fires on the enlarged key with the same principal —
    each hyperedge premise's enlargement is discharged by the induction hypothesis, using that
    the added components are shared and `sremove` is monotone. -/
theorem KProvable.weaken {S : FSequent} (h : KProvable S) :
    ∀ {A' Θ' : List Formula},
      (∀ x, x ∈ S.ante → x ∈ A') → (∀ x, x ∈ S.succ → x ∈ Θ') → KProvable ⟨A', Θ'⟩ := by
  induction h with
  | @ax A Θ f hA hΘ =>
      intro A' Θ' hAsub hΘsub
      exact KProvable.ax (hAsub f hA) (hΘsub f hΘ)
  | @rule S ps hstep hpr ih =>
      intro A' Θ' hAsub hΘsub
      cases hstep with
      | @andL A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.andL (hAsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_singleton] at hP'; subst hP'
          exact ih ⟨φ :: ψ :: sremove (Formula.and φ ψ) A, Θ⟩ (by simp)
            (cons_mono (cons_mono (sremove_mono hAsub))) hΘsub
      | @andR A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.andR (hΘsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
          rcases hP' with rfl | rfl
          · exact ih ⟨A, φ :: sremove (Formula.and φ ψ) Θ⟩ (by simp) hAsub
              (cons_mono (sremove_mono hΘsub))
          · exact ih ⟨A, ψ :: sremove (Formula.and φ ψ) Θ⟩ (by simp) hAsub
              (cons_mono (sremove_mono hΘsub))
      | @orR A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.orR (hΘsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_singleton] at hP'; subst hP'
          exact ih ⟨A, φ :: ψ :: sremove (Formula.or φ ψ) Θ⟩ (by simp) hAsub
            (cons_mono (cons_mono (sremove_mono hΘsub)))
      | @orL A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.orL (hAsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
          rcases hP' with rfl | rfl
          · exact ih ⟨φ :: sremove (Formula.or φ ψ) A, Θ⟩ (by simp)
              (cons_mono (sremove_mono hAsub)) hΘsub
          · exact ih ⟨ψ :: sremove (Formula.or φ ψ) A, Θ⟩ (by simp)
              (cons_mono (sremove_mono hAsub)) hΘsub
      | @impR A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.impR (hΘsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_singleton] at hP'; subst hP'
          exact ih ⟨φ :: A, ψ :: sremove (Formula.imp φ ψ) Θ⟩ (by simp)
            (cons_mono hAsub) (cons_mono (sremove_mono hΘsub))
      | @impL A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.impL (hAsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
          rcases hP' with rfl | rfl
          · exact ih ⟨sremove (Formula.imp φ ψ) A, φ :: Θ⟩ (by simp)
              (sremove_mono hAsub) (cons_mono hΘsub)
          · exact ih ⟨ψ :: sremove (Formula.imp φ ψ) A, Θ⟩ (by simp)
              (cons_mono (sremove_mono hAsub)) hΘsub
      | @negR A Θ φ hmem =>
          refine KProvable.rule (KStep.negR (hΘsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_singleton] at hP'; subst hP'
          exact ih ⟨φ :: A, sremove (Formula.not φ) Θ⟩ (by simp)
            (cons_mono hAsub) (sremove_mono hΘsub)
      | @negL A Θ φ hmem =>
          refine KProvable.rule (KStep.negL (hAsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_singleton] at hP'; subst hP'
          exact ih ⟨sremove (Formula.not φ) A, φ :: Θ⟩ (by simp)
            (sremove_mono hAsub) (cons_mono hΘsub)
      | @iffR A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.iffR (hΘsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
          rcases hP' with rfl | rfl
          · exact ih ⟨A, Formula.imp φ ψ :: sremove (Formula.iff φ ψ) Θ⟩ (by simp) hAsub
              (cons_mono (sremove_mono hΘsub))
          · exact ih ⟨A, Formula.imp ψ φ :: sremove (Formula.iff φ ψ) Θ⟩ (by simp) hAsub
              (cons_mono (sremove_mono hΘsub))
      | @iffL A Θ φ ψ hmem =>
          refine KProvable.rule (KStep.iffL (hAsub _ hmem)) ?_
          intro P' hP'; simp only [List.mem_singleton] at hP'; subst hP'
          exact ih ⟨Formula.imp φ ψ :: Formula.imp ψ φ :: sremove (Formula.iff φ ψ) A, Θ⟩
            (by simp) (cons_mono (cons_mono (sremove_mono hAsub))) hΘsub

/-- **`KProvable` is a property of the set-key.**  It respects `SetEq` (same ante/succ sets),
    so it genuinely descends to the canonical key — two applications of weakening, one per
    inclusion.  (This is contraction *for genuine set-duplicates*; the harder contraction that
    drops an analytically-redundant hypothesis is the gate below.) -/
theorem KProvable.respects_setEq {S S' : FSequent} (h : SetEq S S')
    (hp : KProvable S) : KProvable S' := by
  obtain ⟨A', Θ'⟩ := S'
  exact hp.weaken (fun x hx => (h.1 x).mp hx) (fun x hx => (h.2 x).mp hx)

/-! ### The completeness bridge, reduced to cut-admissibility (the first gate)

    `FDeriv env Γ S → KProvable S`: the real list-based analytic calculus (principal at the
    *head*) is simulated by the set-key hypergraph (principal chosen by *membership*, deleted by
    set-level `sremove`).  Firing the matching `KStep` on an `FDeriv` conclusion reproduces the
    rule exactly, but its premise applies `sremove principal` to the principal's side — literally
    the `FDeriv` premise when the principal is not duplicated, but requiring the principal to be
    *dropped* when a surplus copy survives in the passive context.  Dropping such a copy, whose
    analytic components are already present, is one **cut**.

    The whole residual is discharged by the single lemma `KCut` below, via the two structural
    reducts `dropAnte`/`dropSucc` — *including* `negL`/`impL`, whose components land on the
    opposite side, since the cut moves the principal across sides for free.  This turns the
    diagnosis "completeness reduces to cut-admissibility" into a *proved reduction* (green,
    `sorry`-free): the only obligation left for `FDeriv → KProvable` is `KCut` itself, the
    standard cut-admissibility gate.  (No `FSequent.Lifts` hypothesis is needed for this
    direction: the set-key rule fires on membership alone.) -/

/-- **Cut-admissibility for the set-key calculus** — the outstanding gate.  A formula `g`
    provable on the right of a key and usable on its left may be removed.  Stated with the cut
    formula at the head of the relevant side; `weaken` moves it there from anywhere. -/
def KCut : Prop :=
  ∀ (A Θ : List Formula) (g : Formula),
    KProvable ⟨A, g :: Θ⟩ → KProvable ⟨g :: A, Θ⟩ → KProvable ⟨A, Θ⟩

/-- A component is never equal to a compound it sits strictly inside (size decreases). -/
private theorem child_ne {a b : Formula} (h : sizeOf a < sizeOf b) : a ≠ b :=
  fun e => absurd (e ▸ h) (Nat.lt_irrefl _)

private theorem ne_not (φ : Formula) : φ ≠ Formula.not φ :=
  child_ne (by simp only [Formula.not.sizeOf_spec]; omega)
private theorem ne_and_l (φ ψ : Formula) : φ ≠ Formula.and φ ψ :=
  child_ne (by simp only [Formula.and.sizeOf_spec]; omega)
private theorem ne_and_r (φ ψ : Formula) : ψ ≠ Formula.and φ ψ :=
  child_ne (by simp only [Formula.and.sizeOf_spec]; omega)
private theorem ne_or_l (φ ψ : Formula) : φ ≠ Formula.or φ ψ :=
  child_ne (by simp only [Formula.or.sizeOf_spec]; omega)
private theorem ne_or_r (φ ψ : Formula) : ψ ≠ Formula.or φ ψ :=
  child_ne (by simp only [Formula.or.sizeOf_spec]; omega)
private theorem ne_imp_l (φ ψ : Formula) : φ ≠ Formula.imp φ ψ :=
  child_ne (by simp only [Formula.imp.sizeOf_spec]; omega)
private theorem ne_imp_r (φ ψ : Formula) : ψ ≠ Formula.imp φ ψ :=
  child_ne (by simp only [Formula.imp.sizeOf_spec]; omega)
private theorem ne_impL_iff (φ ψ : Formula) : Formula.imp φ ψ ≠ Formula.iff φ ψ :=
  fun h => Formula.noConfusion h
private theorem ne_impR_iff (φ ψ : Formula) : Formula.imp ψ φ ≠ Formula.iff φ ψ :=
  fun h => Formula.noConfusion h

/-- Set-level removal drops a head that *is* the removed formula. -/
private theorem sremove_cons_self (p : Formula) (l : List Formula) :
    sremove p (p :: l) = sremove p l := by
  simp [sremove]

/-- Set-level removal keeps a head that differs from the removed formula. -/
private theorem sremove_cons_of_ne {a p : Formula} (h : a ≠ p) (l : List Formula) :
    sremove p (a :: l) = a :: sremove p l := by
  simp only [sremove, List.filter_cons]
  rw [if_pos]
  simpa using h

/-- **Left drop by cut.**  Remove an antecedent formula `g` from a provable key, given `g` is
    re-derivable on the right of the residual (`hg`).  The reinstated-left premise is `hB`
    weakened (every element of `B` is `g` or already in `sremove g B`). -/
theorem KProvable.dropAnte (hcut : KCut) {B Θ : List Formula} {g : Formula}
    (hB : KProvable ⟨B, Θ⟩) (hg : KProvable ⟨sremove g B, g :: Θ⟩) :
    KProvable ⟨sremove g B, Θ⟩ :=
  hcut (sremove g B) Θ g hg
    (hB.weaken
      (fun x hx => by
        by_cases hxg : x = g
        · rw [hxg]; exact List.Mem.head _
        · exact List.Mem.tail _ (mem_sremove.2 ⟨hx, hxg⟩))
      (fun _ hx => hx))

/-- **Right drop by cut.**  Dual of `dropAnte`: remove a succedent formula `g`, given `g` is
    refutable on the left of the residual (`hg`). -/
theorem KProvable.dropSucc (hcut : KCut) {A Θ : List Formula} {g : Formula}
    (hΘ : KProvable ⟨A, Θ⟩) (hg : KProvable ⟨g :: A, sremove g Θ⟩) :
    KProvable ⟨A, sremove g Θ⟩ :=
  hcut A (sremove g Θ) g
    (hΘ.weaken (fun _ hx => hx)
      (fun x hx => by
        by_cases hxg : x = g
        · rw [hxg]; exact List.Mem.head _
        · exact List.Mem.tail _ (mem_sremove.2 ⟨hx, hxg⟩)))
    hg

/-- **The completeness bridge, modulo cut.**  Every `FDeriv` derivation maps to a `KProvable`
    certificate of the same key, given cut-admissibility `KCut`.  Each rule fires its `KStep`
    twin on the conclusion; the resulting premise is the `FDeriv` premise with `sremove
    principal` applied to the principal's side, which `dropAnte`/`dropSucc` (one cut each,
    re-deriving the dropped principal from its now-present components via the *dual* one-step
    rule + identity) reconcile with the induction hypothesis.  This is a *proved* reduction of
    `FDeriv → KProvable` to `KCut` — the sole remaining completeness obligation. -/
theorem FDeriv.toKProvable (hcut : KCut) {env : Env} {Γ : Ctx} :
    ∀ {S : FSequent}, FDeriv env Γ S → KProvable S := by
  intro S d
  induction d with
  | @id A S φ hA hS _ => exact KProvable.ax hA hS
  | @negR A Θ φ _ _ _ ih =>
      refine KProvable.rule (KStep.negR (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      rw [sremove_cons_self]
      refine KProvable.dropSucc hcut ih ?_
      refine KProvable.rule (KStep.negL (List.Mem.head _)) ?_
      intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
      exact KProvable.ax
        (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_not φ⟩) (List.Mem.head _)
  | @negL A Θ φ _ _ _ ih =>
      refine KProvable.rule (KStep.negL (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      rw [sremove_cons_self]
      refine KProvable.dropAnte hcut ih ?_
      refine KProvable.rule (KStep.negR (List.Mem.head _)) ?_
      intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
      exact KProvable.ax
        (List.Mem.head _) (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_not φ⟩)
  | @impR A Θ φ ψ _ _ _ _ ih =>
      refine KProvable.rule (KStep.impR (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      rw [sremove_cons_self, ← sremove_cons_of_ne (ne_imp_r φ ψ) Θ]
      refine KProvable.dropSucc hcut ih ?_
      refine KProvable.rule (KStep.impL (List.Mem.head _)) ?_
      intro Q hQ; simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_imp_l φ ψ⟩) (List.Mem.head _)
      · exact KProvable.ax
          (List.Mem.head _) (mem_sremove.2 ⟨List.Mem.head _, ne_imp_r φ ψ⟩)
  | @impL A Θ φ ψ _ _ _ _ _ ih1 ih2 =>
      refine KProvable.rule (KStep.impL (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [sremove_cons_self]
        refine KProvable.dropAnte hcut ih1 ?_
        refine KProvable.rule (KStep.impR (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax (List.Mem.head _)
          (List.Mem.tail _ (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_imp_l φ ψ⟩))
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_imp_r φ ψ) A]
        refine KProvable.dropAnte hcut ih2 ?_
        refine KProvable.rule (KStep.impR (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax
          (List.Mem.tail _ (mem_sremove.2 ⟨List.Mem.head _, ne_imp_r φ ψ⟩)) (List.Mem.head _)
  | @andR A Θ φ ψ _ _ _ _ _ ih1 ih2 =>
      refine KProvable.rule (KStep.andR (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_and_l φ ψ) Θ]
        refine KProvable.dropSucc hcut ih1 ?_
        refine KProvable.rule (KStep.andL (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax (List.Mem.head _)
          (mem_sremove.2 ⟨List.Mem.head _, ne_and_l φ ψ⟩)
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_and_r φ ψ) Θ]
        refine KProvable.dropSucc hcut ih2 ?_
        refine KProvable.rule (KStep.andL (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax (List.Mem.tail _ (List.Mem.head _))
          (mem_sremove.2 ⟨List.Mem.head _, ne_and_r φ ψ⟩)
  | @andL A Θ φ ψ _ _ _ ih =>
      refine KProvable.rule (KStep.andL (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      rw [sremove_cons_self, ← sremove_cons_of_ne (ne_and_r φ ψ) A,
        ← sremove_cons_of_ne (ne_and_l φ ψ) (ψ :: A)]
      refine KProvable.dropAnte hcut ih ?_
      refine KProvable.rule (KStep.andR (List.Mem.head _)) ?_
      intro Q hQ; simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.head _, ne_and_l φ ψ⟩) (List.Mem.head _)
      · exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_and_r φ ψ⟩) (List.Mem.head _)
  | @orR A Θ φ ψ _ _ _ _ ih =>
      refine KProvable.rule (KStep.orR (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      rw [sremove_cons_self, ← sremove_cons_of_ne (ne_or_r φ ψ) Θ,
        ← sremove_cons_of_ne (ne_or_l φ ψ) (ψ :: Θ)]
      refine KProvable.dropSucc hcut ih ?_
      refine KProvable.rule (KStep.orL (List.Mem.head _)) ?_
      intro Q hQ; simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact KProvable.ax (List.Mem.head _)
          (mem_sremove.2 ⟨List.Mem.head _, ne_or_l φ ψ⟩)
      · exact KProvable.ax (List.Mem.head _)
          (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_or_r φ ψ⟩)
  | @orL A Θ φ ψ _ _ _ _ _ ih1 ih2 =>
      refine KProvable.rule (KStep.orL (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_or_l φ ψ) A]
        refine KProvable.dropAnte hcut ih1 ?_
        refine KProvable.rule (KStep.orR (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.head _, ne_or_l φ ψ⟩) (List.Mem.head _)
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_or_r φ ψ) A]
        refine KProvable.dropAnte hcut ih2 ?_
        refine KProvable.rule (KStep.orR (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.head _, ne_or_r φ ψ⟩)
          (List.Mem.tail _ (List.Mem.head _))
  | @iffR A Θ φ ψ _ _ _ _ _ ih1 ih2 =>
      refine KProvable.rule (KStep.iffR (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_impL_iff φ ψ) Θ]
        refine KProvable.dropSucc hcut ih1 ?_
        refine KProvable.rule (KStep.iffL (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax (List.Mem.head _)
          (mem_sremove.2 ⟨List.Mem.head _, ne_impL_iff φ ψ⟩)
      · rw [sremove_cons_self, ← sremove_cons_of_ne (ne_impR_iff φ ψ) Θ]
        refine KProvable.dropSucc hcut ih2 ?_
        refine KProvable.rule (KStep.iffL (List.Mem.head _)) ?_
        intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
        exact KProvable.ax (List.Mem.tail _ (List.Mem.head _))
          (mem_sremove.2 ⟨List.Mem.head _, ne_impR_iff φ ψ⟩)
  | @iffL A Θ φ ψ _ _ _ ih =>
      refine KProvable.rule (KStep.iffL (List.Mem.head _)) ?_
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      rw [sremove_cons_self, ← sremove_cons_of_ne (ne_impR_iff φ ψ) A,
        ← sremove_cons_of_ne (ne_impL_iff φ ψ) (Formula.imp ψ φ :: A)]
      refine KProvable.dropAnte hcut ih ?_
      refine KProvable.rule (KStep.iffR (List.Mem.head _)) ?_
      intro Q hQ; simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.head _, ne_impL_iff φ ψ⟩) (List.Mem.head _)
      · exact KProvable.ax
          (mem_sremove.2 ⟨List.Mem.tail _ (List.Mem.head _), ne_impR_iff φ ψ⟩) (List.Mem.head _)

/-! ### The typed invariant, re-attached to the set-key rule (gate 3, before soundness)

    `KStep`/`KProvable` are untyped: they never mention `liftFormula?` or `LiftsAllF`, so on
    their own a `KProvable` certificate has no guarantee that its formulas are meaningful in the
    fixed contextual environment `(env, Γ)`.  Per the audit's sequencing refinement, that guard
    must be re-attached *before* the `KProvable → ProvesProp` soundness proof — otherwise the
    untyped induction would carry no typedness hypothesis to feed `ProvesProp`'s side
    conditions.

    The invariant is exactly the one `FTrace` threads through its `liftFormula?` / `LiftsAllF`
    premises: **every formula on both sides lifts** (`FSequent.Lifts`).  The key metatheorem is
    that the set-key rule *preserves* it (`KStep.preserves_lifts`): the mirror of
    `KStep.inClosure`, but for typedness rather than analyticity.  Since the analytic rules only
    ever replace a principal by pieces of it, the components lift whenever the principal does. -/

/-- The typed invariant on a set-key: every formula on **both** sides lifts into the fixed
    contextual environment.  This is the side condition `FTrace` carries as `liftFormula?`
    (principals) and `LiftsAllF` (the passive succedent), collected into one predicate on the
    whole sequent so it can be threaded along a `KProvable` derivation. -/
def FSequent.Lifts (env : Env) (Γ : Ctx) (S : FSequent) : Prop :=
  LiftsAllF env Γ S.ante ∧ LiftsAllF env Γ S.succ

/-- `LiftsAllF` is monotone under `sremove` (deleting a formula keeps a lifting list
    lifting). -/
theorem LiftsAllF.sremove {env : Env} {Γ : Ctx} {p : Formula} {l : List Formula}
    (h : LiftsAllF env Γ l) : LiftsAllF env Γ (sremove p l) :=
  fun f hf => h f (mem_sremove.mp hf).1

/-- Split a lifting `and` into its two lifting components. -/
theorem lift_and_split {env : Env} {Γ : Ctx} {a b : Formula}
    (h : (liftFormula? env Γ (Formula.and a b)).isSome = true) :
    (liftFormula? env Γ a).isSome = true ∧ (liftFormula? env Γ b).isSome = true := by
  rw [liftFormula?_and_isSome] at h; simpa only [Bool.and_eq_true] using h

/-- Split a lifting `or` into its two lifting components. -/
theorem lift_or_split {env : Env} {Γ : Ctx} {a b : Formula}
    (h : (liftFormula? env Γ (Formula.or a b)).isSome = true) :
    (liftFormula? env Γ a).isSome = true ∧ (liftFormula? env Γ b).isSome = true := by
  rw [liftFormula?_or_isSome] at h; simpa only [Bool.and_eq_true] using h

/-- Split a lifting `imp` into its two lifting components. -/
theorem lift_imp_split {env : Env} {Γ : Ctx} {a b : Formula}
    (h : (liftFormula? env Γ (Formula.imp a b)).isSome = true) :
    (liftFormula? env Γ a).isSome = true ∧ (liftFormula? env Γ b).isSome = true := by
  rw [liftFormula?_imp_isSome] at h; simpa only [Bool.and_eq_true] using h

/-- Split a lifting `iff` into its two lifting components. -/
theorem lift_iff_split {env : Env} {Γ : Ctx} {a b : Formula}
    (h : (liftFormula? env Γ (Formula.iff a b)).isSome = true) :
    (liftFormula? env Γ a).isSome = true ∧ (liftFormula? env Γ b).isSome = true := by
  rw [liftFormula?_iff_isSome] at h; simpa only [Bool.and_eq_true] using h

/-- Recover the lifting of `a` from a lifting `not a`. -/
theorem lift_not_split {env : Env} {Γ : Ctx} {a : Formula}
    (h : (liftFormula? env Γ (Formula.not a)).isSome = true) :
    (liftFormula? env Γ a).isSome = true := by
  rw [liftFormula?_not_isSome] at h; exact h

/-- **The set-key rule preserves the typed invariant (gate-3 typedness lemma).**  If `S` lifts
    and `KStep S ps` fires a hyperedge, then every premise in `ps` lifts.  The typed mirror of
    `KStep.inClosure`: the two-premise `iffR`/`iffL` cases rebuild `imp` components with `wtImp`
    from the split `iff`; every retained side stays lifting by `LiftsAllF.sremove`. -/
theorem KStep.preserves_lifts {env : Env} {Γ : Ctx} {S : FSequent} {ps : List FSequent}
    (hstep : KStep S ps) (hS : S.Lifts env Γ) : ∀ P ∈ ps, P.Lifts env Γ := by
  obtain ⟨hA, hΘ⟩ := hS
  cases hstep with
  | @andL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      obtain ⟨hφ, hψ⟩ := lift_and_split (hA _ hmem)
      exact ⟨LiftsAllF.cons hφ (LiftsAllF.cons hψ hA.sremove), hΘ⟩
  | @andR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      obtain ⟨hφ, hψ⟩ := lift_and_split (hΘ _ hmem)
      rcases hP with rfl | rfl
      · exact ⟨hA, LiftsAllF.cons hφ hΘ.sremove⟩
      · exact ⟨hA, LiftsAllF.cons hψ hΘ.sremove⟩
  | @orR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      obtain ⟨hφ, hψ⟩ := lift_or_split (hΘ _ hmem)
      exact ⟨hA, LiftsAllF.cons hφ (LiftsAllF.cons hψ hΘ.sremove)⟩
  | @orL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      obtain ⟨hφ, hψ⟩ := lift_or_split (hA _ hmem)
      rcases hP with rfl | rfl
      · exact ⟨LiftsAllF.cons hφ hA.sremove, hΘ⟩
      · exact ⟨LiftsAllF.cons hψ hA.sremove, hΘ⟩
  | @impR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      obtain ⟨hφ, hψ⟩ := lift_imp_split (hΘ _ hmem)
      exact ⟨LiftsAllF.cons hφ hA, LiftsAllF.cons hψ hΘ.sremove⟩
  | @impL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      obtain ⟨hφ, hψ⟩ := lift_imp_split (hA _ hmem)
      rcases hP with rfl | rfl
      · exact ⟨hA.sremove, LiftsAllF.cons hφ hΘ⟩
      · exact ⟨LiftsAllF.cons hψ hA.sremove, hΘ⟩
  | @negR A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hφ := lift_not_split (hΘ _ hmem)
      exact ⟨LiftsAllF.cons hφ hA, hΘ.sremove⟩
  | @negL A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have hφ := lift_not_split (hA _ hmem)
      exact ⟨hA.sremove, LiftsAllF.cons hφ hΘ⟩
  | @iffR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      obtain ⟨hφ, hψ⟩ := lift_iff_split (hΘ _ hmem)
      rcases hP with rfl | rfl
      · exact ⟨hA, LiftsAllF.cons (wtImp hφ hψ) hΘ.sremove⟩
      · exact ⟨hA, LiftsAllF.cons (wtImp hψ hφ) hΘ.sremove⟩
  | @iffL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      obtain ⟨hφ, hψ⟩ := lift_iff_split (hA _ hmem)
      exact ⟨LiftsAllF.cons (wtImp hφ hψ) (LiftsAllF.cons (wtImp hψ hφ) hA.sremove), hΘ⟩

/-! ### Set-key soundness into `denote` (for lifting roots)

    The soundness target is `KProvable S → S.Lifts env Γ → denote env Γ S` — **not**
    `KProvable → ProvesProp`: an empty succedent denotes "the assumptions are absurd, so prove
    any well-typed formula" (`denote ⟨A, []⟩ = ∀ φ, liftFormula? φ → ProvesProp A φ`), which has
    no single `ProvesProp` conclusion.  The `S.Lifts` hypothesis is kept in the statement: this
    is correspondence *for lifting roots*, a deliberate strengthening of raw `FTrace` (which does
    not globally require every antecedent formula to lift).

    The proof reuses `Focused.lean`'s head-form rule-soundness lemmas (`soundAndL`, `soundNegR`,
    …) after transporting the set-key conclusion `⟨A, Θ⟩` (principal *anywhere*) to head form
    `⟨p :: sremove p A, Θ⟩`.  That transport is where structural admissibility lives: the
    **antecedent** side is free (`denote` uses the antecedent only through `ProvesProp`, which is
    membership-based, so `pMono` gives weakening + exchange + contraction on the left); the
    **succedent** side needs a genuine `rightOr` structural lemma — introduction is
    `pRightOr_mem`, and the matching **elimination** (`rightOr_elim`) is proved here by induction
    on the succedent, using `pOrElim` and left-weakening. -/

/-- Pulling a member to the front and deduplicating it leaves the underlying set unchanged. -/
theorem mem_cons_sremove_iff {p : Formula} {l : List Formula} (hp : p ∈ l) (x : Formula) :
    (x ∈ p :: sremove p l) ↔ x ∈ l := by
  simp only [List.mem_cons, mem_sremove]
  constructor
  · rintro (rfl | ⟨hx, _⟩)
    · exact hp
    · exact hx
  · intro hx
    by_cases hxp : x = p
    · exact Or.inl hxp
    · exact Or.inr ⟨hx, hxp⟩

/-- **Elimination of a right-nested disjunction** (the dual of `pRightOr_mem`).  If the whole
    `rightOr φ Θ` is provable and every disjunct `ψ ∈ φ :: Θ` proves the goal `T` when added to
    the context, then `T` is provable.  Proved by induction on `Θ` via binary `pOrElim`, pushing
    each case through left-weakening (`pMono`).  This is the succedent-side structural
    admissibility the set-key rule needs. -/
theorem rightOr_elim {env : Env} {Γ : Ctx} {A : List Formula} {T : Formula}
    (hT : (liftFormula? env Γ T).isSome = true) :
    ∀ (φ : Formula) (Θ : List Formula), LiftsAllF env Γ (φ :: Θ) ->
      ProvesProp env Γ A (rightOr φ Θ) ->
      (∀ ψ, ψ ∈ φ :: Θ -> ProvesProp env Γ (ψ :: A) T) ->
      ProvesProp env Γ A T
  | φ, [], hall, hor, hcase => by
      have hφ := hall.head
      exact ProvesProp.mp hφ (ProvesProp.impIntro hφ (hcase φ (by simp))) hor
  | φ, χ :: Θ', hall, hor, hcase => by
      have hφ := hall.head
      have hrest : (liftFormula? env Γ (rightOr χ Θ')).isSome = true :=
        liftFormula?_rightOr_isSome χ Θ' hall.tail.head hall.tail.tail
      refine pOrElim hφ hrest hT hor (ProvesProp.impIntro hφ (hcase φ (by simp))) ?_
      refine ProvesProp.impIntro hrest ?_
      refine rightOr_elim hT χ Θ' hall.tail (ProvesProp.hyp (by simp)) ?_
      intro ψ hψ
      refine pMono ?_ (hcase ψ (List.mem_cons_of_mem _ hψ))
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ (by simp)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Transport `denote` across a set-equal **antecedent** — free, since `denote` touches the
    antecedent only through `ProvesProp`, which is monotone under `pMono`. -/
theorem denote_ante_transport {env : Env} {Γ : Ctx} {A A' Θ : List Formula}
    (hA : ∀ x, x ∈ A ↔ x ∈ A') (h : denote env Γ ⟨A, Θ⟩) : denote env Γ ⟨A', Θ⟩ := by
  cases Θ with
  | nil => intro φ hφ; exact pMono (fun x hx => (hA x).mp hx) (h φ hφ)
  | cons χ Θ' => exact pMono (fun x hx => (hA x).mp hx) h

/-- Transport `denote` across a set-equal **succedent** — the real structural step, discharged
    with `rightOr_elim` (eliminate the source disjunction) + `pRightOr_mem` (reintroduce each
    disjunct into the target).  Needs both succedents lifting. -/
theorem denote_succ_transport {env : Env} {Γ : Ctx} {A Θ Θ' : List Formula}
    (hΘ : ∀ x, x ∈ Θ ↔ x ∈ Θ') (hl : LiftsAllF env Γ Θ) (hl' : LiftsAllF env Γ Θ')
    (h : denote env Γ ⟨A, Θ⟩) : denote env Γ ⟨A, Θ'⟩ := by
  cases Θ with
  | nil =>
      cases Θ' with
      | nil => exact h
      | cons χ' Θ'0 => exact absurd ((hΘ χ').2 (by simp)) (by simp)
  | cons χ Θ0 =>
      cases Θ' with
      | nil => exact absurd ((hΘ χ).1 (by simp)) (by simp)
      | cons χ' Θ'0 =>
          have hT : (liftFormula? env Γ (rightOr χ' Θ'0)).isSome = true :=
            liftFormula?_rightOr_isSome χ' Θ'0 hl'.head hl'.tail
          refine rightOr_elim hT χ Θ0 hl h ?_
          intro ψ hψ
          exact pRightOr_mem χ' Θ'0 ((hΘ ψ).1 hψ) (ProvesProp.hyp (by simp)) hl'

/-- **Set-key soundness (for lifting roots).**  A `KProvable` certificate whose root lifts in
    `(env, Γ)` denotes: identity keys go through `soundId`; each hyperrule reduces to the
    head-form rule-soundness lemma of `Focused.lean` after transporting the (anywhere-)principal
    to the head with `denote_ante_transport` / `denote_succ_transport`, its premises supplied by
    the induction hypothesis under `KStep.preserves_lifts`. -/
theorem KProvable.sound {env : Env} {Γ : Ctx} :
    ∀ {S : FSequent}, KProvable S -> S.Lifts env Γ -> denote env Γ S := by
  intro S h
  induction h with
  | @ax A Θ f hA hΘ => intro hS; exact soundId hA hΘ hS.2
  | @rule S ps hstep hpr ih =>
      intro hS
      have hden : ∀ P, P ∈ ps -> denote env Γ P :=
        fun P hP => ih P hP (KStep.preserves_lifts hstep hS P hP)
      cases hstep with
      | @andL A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_and_split (hS.1 _ hmem)
          exact denote_ante_transport (fun x => mem_cons_sremove_iff hmem x)
            (soundAndL hφ hψ (hden _ (by simp)))
      | @andR A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_and_split (hS.2 _ hmem)
          exact denote_succ_transport (fun x => mem_cons_sremove_iff hmem x)
            (LiftsAllF.cons (hS.2 _ hmem) hS.2.sremove) hS.2
            (soundAndR hφ hψ hS.2.sremove (hden _ (by simp)) (hden _ (by simp)))
      | @orR A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_or_split (hS.2 _ hmem)
          exact denote_succ_transport (fun x => mem_cons_sremove_iff hmem x)
            (LiftsAllF.cons (hS.2 _ hmem) hS.2.sremove) hS.2
            (soundOrR hφ hψ hS.2.sremove (hden _ (by simp)))
      | @orL A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_or_split (hS.1 _ hmem)
          exact denote_ante_transport (fun x => mem_cons_sremove_iff hmem x)
            (soundOrL hφ hψ hS.2 (hden _ (by simp)) (hden _ (by simp)))
      | @impR A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_imp_split (hS.2 _ hmem)
          exact denote_succ_transport (fun x => mem_cons_sremove_iff hmem x)
            (LiftsAllF.cons (hS.2 _ hmem) hS.2.sremove) hS.2
            (soundImpR hφ hψ hS.2.sremove (hden _ (by simp)))
      | @impL A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_imp_split (hS.1 _ hmem)
          exact denote_ante_transport (fun x => mem_cons_sremove_iff hmem x)
            (soundImpL hφ hψ hS.2 (hden _ (by simp)) (hden _ (by simp)))
      | @negR A Θ φ hmem =>
          have hφ := lift_not_split (hS.2 _ hmem)
          exact denote_succ_transport (fun x => mem_cons_sremove_iff hmem x)
            (LiftsAllF.cons (hS.2 _ hmem) hS.2.sremove) hS.2
            (soundNegR hφ hS.2.sremove (hden _ (by simp)))
      | @negL A Θ φ hmem =>
          have hφ := lift_not_split (hS.1 _ hmem)
          exact denote_ante_transport (fun x => mem_cons_sremove_iff hmem x)
            (soundNegL hφ hS.2 (hden _ (by simp)))
      | @iffR A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_iff_split (hS.2 _ hmem)
          exact denote_succ_transport (fun x => mem_cons_sremove_iff hmem x)
            (LiftsAllF.cons (hS.2 _ hmem) hS.2.sremove) hS.2
            (soundIffR hφ hψ hS.2.sremove (hden _ (by simp)) (hden _ (by simp)))
      | @iffL A Θ φ ψ hmem =>
          obtain ⟨hφ, hψ⟩ := lift_iff_split (hS.1 _ hmem)
          exact denote_ante_transport (fun x => mem_cons_sremove_iff hmem x)
            (soundIffL hφ hψ (hden _ (by simp)))

/-! ### `KCut` is a *theorem*: cut-admissibility via propositional completeness

    The set-key calculus decomposes only the five propositional connectives; atoms, `papp`,
    `all`, `ex` are opaque.  So its adequate semantics is two-valued propositional: a valuation
    `v : Formula → Bool` on the opaque formulas, extended homomorphically by `eval`.  `KProvable`
    is *sound* (`psound`) and *complete* (`pcomplete`) for this semantics, and cut is a triviality
    on the semantic side — giving `KCut` outright, with no height-indexed cut-permutation
    argument.  Completeness is by well-founded recursion on a connective-complexity measure `cx`
    that strictly decreases under every (invertible) rule; the base case (no compound present)
    forces an identity axiom via the countermodel `v f := decide (f ∈ A)`. -/

/-- Homomorphic Boolean evaluation of a formula under a valuation on the *opaque* atoms
    (`atom`/`papp`/`all`/`ex`).  `iff` is decomposed exactly as the two implications, matching the
    `iffL`/`iffR` rules. -/
def eval (v : Formula → Bool) : Formula → Bool
  | Formula.and φ ψ => eval v φ && eval v ψ
  | Formula.or φ ψ => eval v φ || eval v ψ
  | Formula.imp φ ψ => (!eval v φ) || eval v ψ
  | Formula.iff φ ψ => ((!eval v φ) || eval v ψ) && ((!eval v ψ) || eval v φ)
  | Formula.not φ => !eval v φ
  | f => v f

@[simp] theorem eval_and (v) (φ ψ : Formula) :
    eval v (Formula.and φ ψ) = (eval v φ && eval v ψ) := rfl
@[simp] theorem eval_or (v) (φ ψ : Formula) :
    eval v (Formula.or φ ψ) = (eval v φ || eval v ψ) := rfl
@[simp] theorem eval_imp (v) (φ ψ : Formula) :
    eval v (Formula.imp φ ψ) = ((!eval v φ) || eval v ψ) := rfl
@[simp] theorem eval_not (v) (φ : Formula) :
    eval v (Formula.not φ) = !eval v φ := rfl

/-- `iff` evaluates as the conjunction of its two implications. -/
theorem eval_iff (v) (φ ψ : Formula) :
    eval v (Formula.iff φ ψ) = (eval v (Formula.imp φ ψ) && eval v (Formula.imp ψ φ)) := rfl

/-- Semantic validity of a key: under every valuation making all antecedents true, some
    succedent is true. -/
def Valid (S : FSequent) : Prop :=
  ∀ v : Formula → Bool,
    (∀ f ∈ S.ante, eval v f = true) → ∃ f ∈ S.succ, eval v f = true

/-- Connective complexity: strictly greater than the total complexity of a rule's added
    components.  `iff` counts as its two implications plus one, so `iffL`/`iffR` strictly
    decrease. -/
def cx : Formula → Nat
  | Formula.and φ ψ => cx φ + cx ψ + 1
  | Formula.or φ ψ => cx φ + cx ψ + 1
  | Formula.imp φ ψ => cx φ + cx ψ + 1
  | Formula.iff φ ψ => cx φ + cx ψ + cx φ + cx ψ + 3
  | Formula.not φ => cx φ + 1
  | _ => 0

@[simp] theorem cx_and (φ ψ : Formula) : cx (Formula.and φ ψ) = cx φ + cx ψ + 1 := rfl
@[simp] theorem cx_or (φ ψ : Formula) : cx (Formula.or φ ψ) = cx φ + cx ψ + 1 := rfl
@[simp] theorem cx_imp (φ ψ : Formula) : cx (Formula.imp φ ψ) = cx φ + cx ψ + 1 := rfl
@[simp] theorem cx_iff (φ ψ : Formula) :
    cx (Formula.iff φ ψ) = cx φ + cx ψ + cx φ + cx ψ + 3 := rfl
@[simp] theorem cx_not (φ : Formula) : cx (Formula.not φ) = cx φ + 1 := rfl

/-- Total complexity of a list (with multiplicity). -/
def listCx : List Formula → Nat
  | [] => 0
  | a :: l => cx a + listCx l

@[simp] theorem listCx_nil : listCx [] = 0 := rfl
@[simp] theorem listCx_cons (a : Formula) (l : List Formula) :
    listCx (a :: l) = cx a + listCx l := rfl

/-- Total complexity of a key. -/
def seqCx (S : FSequent) : Nat := listCx S.ante + listCx S.succ

/-- Everything surviving `sremove` was already there, hence true whenever all of `l` is. -/
private theorem eval_sremove_of_all {v : Formula → Bool} {p : Formula} {l : List Formula}
    (h : ∀ f ∈ l, eval v f = true) : ∀ f ∈ sremove p l, eval v f = true :=
  fun f hf => h f (mem_sremove.1 hf).1

/-- **Propositional soundness.**  Every `KProvable` key is `Valid`: each analytic rule is sound
    under the homomorphic `eval`. -/
theorem KProvable.psound {S : FSequent} (h : KProvable S) : Valid S := by
  induction h with
  | @ax A Θ f hA hΘ => intro v hante; exact ⟨f, hΘ, hante _ hA⟩
  | @rule S ps hstep hpr ih =>
      cases hstep with
      | @andL A Θ φ ψ hmem =>
          intro v hante
          have hp : eval v (Formula.and φ ψ) = true := hante _ hmem
          rw [eval_and, Bool.and_eq_true] at hp
          exact ih ⟨φ :: ψ :: sremove (Formula.and φ ψ) A, Θ⟩ (by simp) v
            (fun f hf => by
              rcases List.mem_cons.1 hf with rfl | hf
              · exact hp.1
              rcases List.mem_cons.1 hf with rfl | hf
              · exact hp.2
              · exact hante _ (mem_sremove.1 hf).1)
      | @andR A Θ φ ψ hmem =>
          intro v hante
          obtain ⟨f, hf, hev⟩ :=
            ih ⟨A, φ :: sremove (Formula.and φ ψ) Θ⟩ (by simp) v hante
          rcases List.mem_cons.1 hf with hfe | hf
          · rw [hfe] at hev
            obtain ⟨g, hg, hgev⟩ :=
              ih ⟨A, ψ :: sremove (Formula.and φ ψ) Θ⟩ (by simp) v hante
            rcases List.mem_cons.1 hg with hge | hg
            · rw [hge] at hgev
              exact ⟨Formula.and φ ψ, hmem, by rw [eval_and, hev, hgev, Bool.and_self]⟩
            · exact ⟨g, (mem_sremove.1 hg).1, hgev⟩
          · exact ⟨f, (mem_sremove.1 hf).1, hev⟩
      | @orR A Θ φ ψ hmem =>
          intro v hante
          obtain ⟨f, hf, hev⟩ :=
            ih ⟨A, φ :: ψ :: sremove (Formula.or φ ψ) Θ⟩ (by simp) v hante
          rcases List.mem_cons.1 hf with hfe | hf
          · rw [hfe] at hev
            exact ⟨Formula.or φ ψ, hmem, by rw [eval_or, hev, Bool.true_or]⟩
          rcases List.mem_cons.1 hf with hfe | hf
          · rw [hfe] at hev
            exact ⟨Formula.or φ ψ, hmem, by rw [eval_or, hev, Bool.or_true]⟩
          · exact ⟨f, (mem_sremove.1 hf).1, hev⟩
      | @orL A Θ φ ψ hmem =>
          intro v hante
          have hor : eval v (Formula.or φ ψ) = true := hante _ hmem
          rw [eval_or] at hor
          have hsrem := eval_sremove_of_all (v := v) (p := Formula.or φ ψ) hante
          cases hφ : eval v φ with
          | true =>
              exact ih ⟨φ :: sremove (Formula.or φ ψ) A, Θ⟩ (by simp) v
                (fun g hg => by
                  rcases List.mem_cons.1 hg with rfl | hg
                  · exact hφ
                  · exact hsrem _ hg)
          | false =>
              rw [hφ, Bool.false_or] at hor
              exact ih ⟨ψ :: sremove (Formula.or φ ψ) A, Θ⟩ (by simp) v
                (fun g hg => by
                  rcases List.mem_cons.1 hg with rfl | hg
                  · exact hor
                  · exact hsrem _ hg)
      | @impR A Θ φ ψ hmem =>
          intro v hante
          cases hφ : eval v φ with
          | false => exact ⟨Formula.imp φ ψ, hmem, by rw [eval_imp, hφ, Bool.not_false, Bool.true_or]⟩
          | true =>
              obtain ⟨f, hf, hev⟩ :=
                ih ⟨φ :: A, ψ :: sremove (Formula.imp φ ψ) Θ⟩ (by simp) v
                  (fun g hg => by
                    rcases List.mem_cons.1 hg with rfl | hg
                    · exact hφ
                    · exact hante _ hg)
              rcases List.mem_cons.1 hf with hfe | hf
              · rw [hfe] at hev
                exact ⟨Formula.imp φ ψ, hmem, by rw [eval_imp, hev]; exact Bool.or_true _⟩
              · exact ⟨f, (mem_sremove.1 hf).1, hev⟩
      | @impL A Θ φ ψ hmem =>
          intro v hante
          have hsrem := eval_sremove_of_all (v := v) (p := Formula.imp φ ψ) hante
          obtain ⟨f, hf, hev⟩ :=
            ih ⟨sremove (Formula.imp φ ψ) A, φ :: Θ⟩ (by simp) v hsrem
          rcases List.mem_cons.1 hf with hfe | hf
          · rw [hfe] at hev
            have himp : eval v (Formula.imp φ ψ) = true := hante _ hmem
            rw [eval_imp, hev] at himp
            simp only [Bool.not_true, Bool.false_or] at himp
            exact ih ⟨ψ :: sremove (Formula.imp φ ψ) A, Θ⟩ (by simp) v
              (fun x hx => by
                rcases List.mem_cons.1 hx with rfl | hx
                · exact himp
                · exact hsrem _ hx)
          · exact ⟨f, hf, hev⟩
      | @negR A Θ φ hmem =>
          intro v hante
          cases hφ : eval v φ with
          | false => exact ⟨Formula.not φ, hmem, by rw [eval_not, hφ, Bool.not_false]⟩
          | true =>
              obtain ⟨f, hf, hev⟩ :=
                ih ⟨φ :: A, sremove (Formula.not φ) Θ⟩ (by simp) v
                  (fun g hg => by
                    rcases List.mem_cons.1 hg with rfl | hg
                    · exact hφ
                    · exact hante _ hg)
              exact ⟨f, (mem_sremove.1 hf).1, hev⟩
      | @negL A Θ φ hmem =>
          intro v hante
          have hnot : eval v (Formula.not φ) = true := hante _ hmem
          rw [eval_not] at hnot
          have hsrem := eval_sremove_of_all (v := v) (p := Formula.not φ) hante
          obtain ⟨f, hf, hev⟩ :=
            ih ⟨sremove (Formula.not φ) A, φ :: Θ⟩ (by simp) v hsrem
          rcases List.mem_cons.1 hf with hfe | hf
          · rw [hfe] at hev; rw [hev] at hnot; exact absurd hnot (by decide)
          · exact ⟨f, hf, hev⟩
      | @iffR A Θ φ ψ hmem =>
          intro v hante
          obtain ⟨f, hf, hev⟩ :=
            ih ⟨A, Formula.imp φ ψ :: sremove (Formula.iff φ ψ) Θ⟩ (by simp) v hante
          rcases List.mem_cons.1 hf with rfl | hf
          · obtain ⟨g, hg, hgev⟩ :=
              ih ⟨A, Formula.imp ψ φ :: sremove (Formula.iff φ ψ) Θ⟩ (by simp) v hante
            rcases List.mem_cons.1 hg with rfl | hg
            · exact ⟨Formula.iff φ ψ, hmem, by rw [eval_iff, hev, hgev, Bool.and_self]⟩
            · exact ⟨g, (mem_sremove.1 hg).1, hgev⟩
          · exact ⟨f, (mem_sremove.1 hf).1, hev⟩
      | @iffL A Θ φ ψ hmem =>
          intro v hante
          have hiff : eval v (Formula.iff φ ψ) = true := hante _ hmem
          rw [eval_iff, Bool.and_eq_true] at hiff
          exact ih ⟨Formula.imp φ ψ :: Formula.imp ψ φ :: sremove (Formula.iff φ ψ) A, Θ⟩
            (by simp) v
            (fun g hg => by
              rcases List.mem_cons.1 hg with rfl | hg
              · exact hiff.1
              rcases List.mem_cons.1 hg with rfl | hg
              · exact hiff.2
              · exact hante _ (mem_sremove.1 hg).1)

/-- `sremove` never increases total complexity. -/
private theorem listCx_sremove_le (p : Formula) :
    ∀ (l : List Formula), listCx (sremove p l) ≤ listCx l := by
  intro l
  induction l with
  | nil => simp [sremove]
  | cons a l ih =>
      by_cases hap : a = p
      · subst hap; rw [sremove_cons_self, listCx_cons]; omega
      · rw [sremove_cons_of_ne hap, listCx_cons, listCx_cons]; omega

/-- Removing a present formula drops at least its own complexity. -/
private theorem listCx_sremove_add {p : Formula} :
    ∀ {l : List Formula}, p ∈ l → listCx (sremove p l) + cx p ≤ listCx l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons a l ih =>
      intro h
      by_cases hap : a = p
      · subst hap
        rw [sremove_cons_self, listCx_cons]
        have := listCx_sremove_le a l; omega
      · rw [sremove_cons_of_ne hap, listCx_cons, listCx_cons]
        rcases List.mem_cons.1 h with he | hpl
        · exact absurd he.symm hap
        · have := ih hpl; omega

/-- **Every rule strictly decreases total complexity.**  The termination measure for the
    completeness search: the added components always weigh strictly less than the (fully removed)
    principal. -/
private theorem KStep.seqCx_lt {S : FSequent} {ps : List FSequent}
    (hstep : KStep S ps) : ∀ P ∈ ps, seqCx P < seqCx S := by
  cases hstep with
  | @andL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have h := listCx_sremove_add (p := Formula.and φ ψ) hmem
      simp only [seqCx, listCx_cons, cx_and] at h ⊢; omega
  | @andR A Θ φ ψ hmem =>
      have h := listCx_sremove_add (p := Formula.and φ ψ) hmem
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl <;>
        (simp only [seqCx, listCx_cons, cx_and] at h ⊢; omega)
  | @orR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have h := listCx_sremove_add (p := Formula.or φ ψ) hmem
      simp only [seqCx, listCx_cons, cx_or] at h ⊢; omega
  | @orL A Θ φ ψ hmem =>
      have h := listCx_sremove_add (p := Formula.or φ ψ) hmem
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl <;>
        (simp only [seqCx, listCx_cons, cx_or] at h ⊢; omega)
  | @impR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have h := listCx_sremove_add (p := Formula.imp φ ψ) hmem
      simp only [seqCx, listCx_cons, cx_imp] at h ⊢; omega
  | @impL A Θ φ ψ hmem =>
      have h := listCx_sremove_add (p := Formula.imp φ ψ) hmem
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl <;>
        (simp only [seqCx, listCx_cons, cx_imp] at h ⊢; omega)
  | @negR A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have h := listCx_sremove_add (p := Formula.not φ) hmem
      simp only [seqCx, listCx_cons, cx_not] at h ⊢; omega
  | @negL A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have h := listCx_sremove_add (p := Formula.not φ) hmem
      simp only [seqCx, listCx_cons, cx_not] at h ⊢; omega
  | @iffR A Θ φ ψ hmem =>
      have h := listCx_sremove_add (p := Formula.iff φ ψ) hmem
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl <;>
        (simp only [seqCx, listCx_cons, cx_iff, cx_imp] at h ⊢; omega)
  | @iffL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      have h := listCx_sremove_add (p := Formula.iff φ ψ) hmem
      simp only [seqCx, listCx_cons, cx_iff, cx_imp] at h ⊢; omega

/-- **Propositional invertibility.**  Each analytic rule is invertible under `eval`: validity of
    the conclusion transfers to every premise.  This is what lets completeness push `Valid` down
    to the (smaller) premises of a fired rule. -/
theorem KStep.valid_premises {S : FSequent} {ps : List FSequent}
    (hstep : KStep S ps) (hS : Valid S) : ∀ P ∈ ps, Valid P := by
  cases hstep with
  | @andL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      intro v hpre
      have hφ : eval v φ = true := hpre _ (List.Mem.head _)
      have hψ : eval v ψ = true := hpre _ (List.Mem.tail _ (List.Mem.head _))
      apply hS v; intro f hf
      by_cases hfe : f = Formula.and φ ψ
      · rw [hfe, eval_and, hφ, hψ, Bool.and_self]
      · exact hpre _ (List.Mem.tail _ (List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩)))
  | @andR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · intro v hA
        obtain ⟨f, hf, hev⟩ := hS v hA
        by_cases hfe : f = Formula.and φ ψ
        · subst hfe; rw [eval_and, Bool.and_eq_true] at hev
          exact ⟨φ, List.Mem.head _, hev.1⟩
        · exact ⟨f, List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩), hev⟩
      · intro v hA
        obtain ⟨f, hf, hev⟩ := hS v hA
        by_cases hfe : f = Formula.and φ ψ
        · subst hfe; rw [eval_and, Bool.and_eq_true] at hev
          exact ⟨ψ, List.Mem.head _, hev.2⟩
        · exact ⟨f, List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩), hev⟩
  | @orR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      intro v hA
      obtain ⟨f, hf, hev⟩ := hS v hA
      by_cases hfe : f = Formula.or φ ψ
      · subst hfe; rw [eval_or, Bool.or_eq_true] at hev
        rcases hev with h1 | h2
        · exact ⟨φ, List.Mem.head _, h1⟩
        · exact ⟨ψ, List.Mem.tail _ (List.Mem.head _), h2⟩
      · exact ⟨f, List.Mem.tail _ (List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩)), hev⟩
  | @orL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · intro v hpre
        have hφ : eval v φ = true := hpre _ (List.Mem.head _)
        apply hS v; intro f hf
        by_cases hfe : f = Formula.or φ ψ
        · rw [hfe, eval_or, hφ, Bool.true_or]
        · exact hpre _ (List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩))
      · intro v hpre
        have hψ : eval v ψ = true := hpre _ (List.Mem.head _)
        apply hS v; intro f hf
        by_cases hfe : f = Formula.or φ ψ
        · rw [hfe, eval_or, hψ, Bool.or_true]
        · exact hpre _ (List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩))
  | @impR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      intro v hpre
      have hφ : eval v φ = true := hpre _ (List.Mem.head _)
      have hA : ∀ f ∈ A, eval v f = true := fun f hf => hpre _ (List.Mem.tail _ hf)
      obtain ⟨f, hf, hev⟩ := hS v hA
      by_cases hfe : f = Formula.imp φ ψ
      · subst hfe; rw [eval_imp, hφ] at hev
        simp only [Bool.not_true, Bool.false_or] at hev
        exact ⟨ψ, List.Mem.head _, hev⟩
      · exact ⟨f, List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩), hev⟩
  | @impL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · intro v hpre
        cases himp : eval v (Formula.imp φ ψ) with
        | false =>
            rw [eval_imp] at himp
            have hφ : eval v φ = true := by
              cases h : eval v φ with
              | true => rfl
              | false => rw [h, Bool.not_false, Bool.true_or] at himp; exact absurd himp (by decide)
            exact ⟨φ, List.Mem.head _, hφ⟩
        | true =>
            have hA : ∀ f ∈ A, eval v f = true := by
              intro f hf
              by_cases hfe : f = Formula.imp φ ψ
              · rw [hfe]; exact himp
              · exact hpre _ (mem_sremove.2 ⟨hf, hfe⟩)
            obtain ⟨f, hf, hev⟩ := hS v hA
            exact ⟨f, List.Mem.tail _ hf, hev⟩
      · intro v hpre
        have hψ : eval v ψ = true := hpre _ (List.Mem.head _)
        have hsrem : ∀ f ∈ sremove (Formula.imp φ ψ) A, eval v f = true :=
          fun f hf => hpre _ (List.Mem.tail _ hf)
        have hA : ∀ f ∈ A, eval v f = true := by
          intro f hf
          by_cases hfe : f = Formula.imp φ ψ
          · rw [hfe, eval_imp, hψ]; exact Bool.or_true _
          · exact hsrem _ (mem_sremove.2 ⟨hf, hfe⟩)
        exact hS v hA
  | @negR A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      intro v hpre
      have hφ : eval v φ = true := hpre _ (List.Mem.head _)
      have hA : ∀ f ∈ A, eval v f = true := fun f hf => hpre _ (List.Mem.tail _ hf)
      obtain ⟨f, hf, hev⟩ := hS v hA
      refine ⟨f, mem_sremove.2 ⟨hf, ?_⟩, hev⟩
      intro hfe; rw [hfe, eval_not, hφ] at hev; exact absurd hev (by decide)
  | @negL A Θ φ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      intro v hpre
      cases hφ : eval v φ with
      | true => exact ⟨φ, List.Mem.head _, hφ⟩
      | false =>
          have hnot : eval v (Formula.not φ) = true := by rw [eval_not, hφ, Bool.not_false]
          have hA : ∀ f ∈ A, eval v f = true := by
            intro f hf
            by_cases hfe : f = Formula.not φ
            · rw [hfe]; exact hnot
            · exact hpre _ (mem_sremove.2 ⟨hf, hfe⟩)
          obtain ⟨f, hf, hev⟩ := hS v hA
          exact ⟨f, List.Mem.tail _ hf, hev⟩
  | @iffR A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · intro v hA
        obtain ⟨f, hf, hev⟩ := hS v hA
        by_cases hfe : f = Formula.iff φ ψ
        · subst hfe; rw [eval_iff, Bool.and_eq_true] at hev
          exact ⟨Formula.imp φ ψ, List.Mem.head _, hev.1⟩
        · exact ⟨f, List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩), hev⟩
      · intro v hA
        obtain ⟨f, hf, hev⟩ := hS v hA
        by_cases hfe : f = Formula.iff φ ψ
        · subst hfe; rw [eval_iff, Bool.and_eq_true] at hev
          exact ⟨Formula.imp ψ φ, List.Mem.head _, hev.2⟩
        · exact ⟨f, List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩), hev⟩
  | @iffL A Θ φ ψ hmem =>
      intro P hP; simp only [List.mem_singleton] at hP; subst hP
      intro v hpre
      have h1 : eval v (Formula.imp φ ψ) = true := hpre _ (List.Mem.head _)
      have h2 : eval v (Formula.imp ψ φ) = true := hpre _ (List.Mem.tail _ (List.Mem.head _))
      apply hS v; intro f hf
      by_cases hfe : f = Formula.iff φ ψ
      · rw [hfe, eval_iff, h1, h2, Bool.and_self]
      · exact hpre _ (List.Mem.tail _ (List.Mem.tail _ (mem_sremove.2 ⟨hf, hfe⟩)))

/-- Boolean test for the five decomposable connectives (everything else is opaque). -/
def isCompound : Formula → Bool
  | Formula.and _ _ => true
  | Formula.or _ _ => true
  | Formula.imp _ _ => true
  | Formula.iff _ _ => true
  | Formula.not _ => true
  | _ => false

/-- On an opaque formula, `eval` is just the valuation. -/
private theorem eval_base {v : Formula → Bool} {f : Formula} (h : isCompound f = false) :
    eval v f = v f := by
  cases f <;> first | rfl | simp [isCompound] at h

/-- A list either contains a decomposable formula or is entirely opaque. -/
private theorem exists_compound_or_all_base (l : List Formula) :
    (∃ f ∈ l, isCompound f = true) ∨ (∀ f ∈ l, isCompound f = false) := by
  induction l with
  | nil => right; intro f hf; exact absurd hf (by simp)
  | cons a l ih =>
      cases ha : isCompound a with
      | true => left; exact ⟨a, List.Mem.head _, ha⟩
      | false =>
          rcases ih with ⟨f, hf, hcf⟩ | hall
          · left; exact ⟨f, List.Mem.tail _ hf, hcf⟩
          · right; intro f hf
            rcases List.mem_cons.1 hf with rfl | hf
            · exact ha
            · exact hall f hf

/-- Some left rule fires on a decomposable antecedent formula.  Type-valued (returns the premise
    list in a `Subtype`) so it can drive the `Decidable` evaluator; `obtain` still destructures it
    in `Prop` goals (`pcomplete`). -/
private def compound_ante_step {A Θ : List Formula} {f : Formula}
    (hc : isCompound f = true) (hf : f ∈ A) : {ps : List FSequent // KStep ⟨A, Θ⟩ ps} := by
  cases f with
  | and φ ψ => exact ⟨_, KStep.andL hf⟩
  | or φ ψ => exact ⟨_, KStep.orL hf⟩
  | imp φ ψ => exact ⟨_, KStep.impL hf⟩
  | iff φ ψ => exact ⟨_, KStep.iffL hf⟩
  | not φ => exact ⟨_, KStep.negL hf⟩
  | atom _ _ _ => simp [isCompound] at hc
  | papp _ _ => simp [isCompound] at hc
  | all _ _ _ => simp [isCompound] at hc
  | ex _ _ _ => simp [isCompound] at hc

/-- Some right rule fires on a decomposable succedent formula (Type-valued, as
    `compound_ante_step`). -/
private def compound_succ_step {A Θ : List Formula} {f : Formula}
    (hc : isCompound f = true) (hf : f ∈ Θ) : {ps : List FSequent // KStep ⟨A, Θ⟩ ps} := by
  cases f with
  | and φ ψ => exact ⟨_, KStep.andR hf⟩
  | or φ ψ => exact ⟨_, KStep.orR hf⟩
  | imp φ ψ => exact ⟨_, KStep.impR hf⟩
  | iff φ ψ => exact ⟨_, KStep.iffR hf⟩
  | not φ => exact ⟨_, KStep.negR hf⟩
  | atom _ _ _ => simp [isCompound] at hc
  | papp _ _ => simp [isCompound] at hc
  | all _ _ _ => simp [isCompound] at hc
  | ex _ _ _ => simp [isCompound] at hc

/-- **Propositional completeness.**  Every `Valid` key is `KProvable`, by well-founded recursion
    on total complexity `seqCx`: if a connective is present, fire its (complexity-decreasing,
    invertible) rule and recurse on the premises; otherwise the countermodel `v x := decide (x ∈
    A)` forces an identity axiom. -/
theorem KProvable.pcomplete (S : FSequent) (hV : Valid S) : KProvable S := by
  rcases exists_compound_or_all_base S.ante with ⟨f, hf, hcf⟩ | hAbase
  · obtain ⟨ps, hstep⟩ := compound_ante_step (A := S.ante) (Θ := S.succ) hcf hf
    exact KProvable.rule hstep
      (fun P hP => KProvable.pcomplete P (hstep.valid_premises hV P hP))
  · rcases exists_compound_or_all_base S.succ with ⟨f, hf, hcf⟩ | hΘbase
    · obtain ⟨ps, hstep⟩ := compound_succ_step (A := S.ante) (Θ := S.succ) hcf hf
      exact KProvable.rule hstep
        (fun P hP => KProvable.pcomplete P (hstep.valid_premises hV P hP))
    · obtain ⟨g, hgΘ, hgev⟩ :=
        hV (fun x => memb x S.ante)
          (fun f hf => by rw [eval_base (hAbase f hf)]; exact (memb_iff f S.ante).mpr hf)
      have hgA : g ∈ S.ante := by
        rw [eval_base (hΘbase g hgΘ)] at hgev; exact (memb_iff g S.ante).mp hgev
      exact KProvable.ax hgA hgΘ
  termination_by seqCx S
  decreasing_by
    all_goals exact hstep.seqCx_lt _ hP

/-- **`KCut` is a theorem.**  Cut is trivial on the semantic side (`Valid`), so it holds for
    `KProvable` by soundness (`psound`) + completeness (`pcomplete`). -/
theorem kCut : KCut := by
  intro A Θ g h1 h2
  apply KProvable.pcomplete
  intro v hA
  by_cases hg : eval v g = true
  · exact h2.psound v
      (fun f hf => by
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hg
        · exact hA f hf)
  · obtain ⟨f, hf, hev⟩ := h1.psound v hA
    rcases List.mem_cons.1 hf with rfl | hf
    · exact absurd hev hg
    · exact ⟨f, hf, hev⟩

/-- **The completeness bridge, unconditionally.**  `KCut` being a theorem, every `FDeriv`
    derivation maps to a `KProvable` certificate of the same key with no side hypothesis. -/
theorem FDeriv.toKProvable' {env : Env} {Γ : Ctx} {S : FSequent}
    (d : FDeriv env Γ S) : KProvable S :=
  FDeriv.toKProvable kCut d

/-! ### Proof-producing canonical-key evaluator (`Decidable (KProvable S)`)

    Per the audit's refinement: the finite-search evaluator must **emit a certificate**, not a
    Boolean — `KProvable`/`pcomplete`/`kCut` live in `Prop`, so a `Bool` decision would discard
    the derivation.  We give the evaluator as a `Decidable (KProvable S)`: on success it returns
    `isTrue d` with `d : KProvable S` an actual set-key derivation (built from `KProvable.rule`/
    `KProvable.ax`); on failure `isFalse` with a genuine refutation.  It has the same shape as
    `pcomplete` — fire a complexity-decreasing, invertible rule on any present connective and
    recurse on its premises; at a fully-atomic key, succeed iff an identity axiom is available
    (`find?`) and otherwise refute via the countermodel `v x := memb x A`.  Termination is on
    `seqCx` (`KStep.seqCx_lt`); the `isFalse` branches reuse `psound`/`valid_premises`/`pcomplete`.
    `KProvable.normKey_congr` then certifies the decision depends only on the canonical key
    `normKey C S`, so this is genuinely a *canonical-key* evaluator whose state space is the
    `≤ 4^{|C|}` members of `allKeys C`.

    Boundary retained (per the audit): turning a positive result `KProvable S` into an
    object-logic proof still goes through `KProvable.sound`, which needs the lifting-root
    condition `S.Lifts env Γ`; the evaluator itself lives purely at the set-key layer. -/

/-- Decide a bounded universal over a concrete premise list from a member-indexed decider.
    (Core's `List.decidableBAll` wants a global `DecidablePred`; here each decider is a
    complexity-decreasing recursive call.) -/
private def decForallMem : (ps : List FSequent) →
    (∀ P ∈ ps, Decidable (KProvable P)) → Decidable (∀ P ∈ ps, KProvable P)
  | [], _ => isTrue (fun _ hP => absurd hP List.not_mem_nil)
  | P :: ps, rec =>
    match rec P List.mem_cons_self with
    | isFalse h => isFalse (fun hall => h (hall P List.mem_cons_self))
    | isTrue hP =>
        match decForallMem ps (fun Q hQ => rec Q (List.mem_cons_of_mem P hQ)) with
        | isFalse h => isFalse (fun hall => h (fun Q hQ => hall Q (List.mem_cons_of_mem P hQ)))
        | isTrue hps => isTrue (fun Q hQ => by
            rcases List.mem_cons.1 hQ with rfl | hQ
            · exact hP
            · exact hps Q hQ)

/-- Constructively locate the first compound in a list, or witness that all its members are
    atomic — a `Type`-valued (large-eliminable) classifier, so it can drive a `Decidable`
    construction (the `Prop`-valued `exists_compound_or_all_base` cannot). -/
private def firstCompound : (l : List Formula) →
    PSum {f : Formula // f ∈ l ∧ isCompound f = true} (∀ f ∈ l, isCompound f = false)
  | [] => PSum.inr (fun _ hf => absurd hf List.not_mem_nil)
  | a :: l =>
    if h : isCompound a = true then
      PSum.inl ⟨a, List.mem_cons_self, h⟩
    else
      match firstCompound l with
      | PSum.inl ⟨f, hf, hc⟩ => PSum.inl ⟨f, List.mem_cons_of_mem a hf, hc⟩
      | PSum.inr hall => PSum.inr (fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact eq_false_of_ne_true h
          · exact hall f hf)

/-- **Proof-producing canonical-key evaluator.**  Decides `KProvable S`, returning an actual
    set-key derivation on success (`isTrue`) and a genuine refutation on failure (`isFalse`) —
    not a Boolean.  Same recursion as `pcomplete`, terminating on `seqCx`. -/
def KProvable.decide (S : FSequent) : Decidable (KProvable S) := by
  cases firstCompound S.ante with
  | inl fw =>
      obtain ⟨f, hf, hcf⟩ := fw
      obtain ⟨ps, hstep⟩ := compound_ante_step (A := S.ante) (Θ := S.succ) hcf hf
      exact match decForallMem ps (fun P hP => KProvable.decide P) with
        | isTrue h => isTrue (KProvable.rule hstep h)
        | isFalse h => isFalse (fun hp =>
            h (fun P hP => KProvable.pcomplete P (hstep.valid_premises hp.psound P hP)))
  | inr hAbase =>
      cases firstCompound S.succ with
      | inl fw =>
          obtain ⟨f, hf, hcf⟩ := fw
          obtain ⟨ps, hstep⟩ := compound_succ_step (A := S.ante) (Θ := S.succ) hcf hf
          exact match decForallMem ps (fun P hP => KProvable.decide P) with
            | isTrue h => isTrue (KProvable.rule hstep h)
            | isFalse h => isFalse (fun hp =>
                h (fun P hP => KProvable.pcomplete P (hstep.valid_premises hp.psound P hP)))
      | inr hΘbase =>
          exact match hfd : S.succ.find? (fun g => memb g S.ante) with
            | some g => by
                have hmem := List.find?_some hfd
                exact isTrue (KProvable.ax ((memb_iff g S.ante).1 hmem)
                  (List.mem_of_find?_eq_some hfd))
            | none => isFalse (fun hp => by
                obtain ⟨g, hgΘ, hgev⟩ := hp.psound (fun x => memb x S.ante)
                  (fun f hf => by rw [eval_base (hAbase f hf)]; exact (memb_iff f S.ante).mpr hf)
                have hgmem : memb g S.ante = true := by
                  rw [eval_base (hΘbase g hgΘ)] at hgev; exact hgev
                exact (List.find?_eq_none.1 hfd g hgΘ) hgmem)
  termination_by seqCx S
  decreasing_by all_goals exact hstep.seqCx_lt _ hP

/-- The evaluator as a typeclass instance: `KProvable S` is decidable. -/
instance (S : FSequent) : Decidable (KProvable S) := KProvable.decide S

/-- **The evaluator is a function of the canonical key.**  On in-closure states, `KProvable`
    depends only on `normKey C S`: equal keys are inter-provable.  So `KProvable.decide` genuinely
    evaluates the canonical key, and its state space is the `≤ 4^{|C|}` members of `allKeys C`. -/
theorem KProvable.normKey_congr {C : List Formula} {S S' : FSequent}
    (hS : S.InClosure C) (hS' : S'.InClosure C) (hk : normKey C S = normKey C S') :
    KProvable S ↔ KProvable S' :=
  ⟨fun hp => hp.respects_setEq (setEq_of_normKey_eq hS hS' hk),
   fun hp => hp.respects_setEq (setEq_of_normKey_eq hS' hS hk.symm)⟩

/-! ### TODO — what remains for the memoized search algorithm

    With `FSequent.Lifts` + `KStep.preserves_lifts` (typed guard re-attached) and
    `KProvable.sound` (set-key soundness into `denote`, for lifting roots) in hand, the *sound*
    direction of correspondence is done.  The completeness bridge is now **unconditional**:
    `FDeriv.toKProvable'` derives `FDeriv → KProvable` with no side hypothesis (no `FSequent.Lifts`
    needed — the set-key rule fires on membership), because `KCut` is a *theorem* (`kCut`).  The
    certified proof-search over the finite normalized state space is now realized as a
    proof-producing decision procedure (`KProvable.decide`, below):

    **`KCut` is proved (`kCut`), via propositional adequacy — no cut-permutation argument.**
    The set-key calculus decomposes only the five propositional connectives (`atom`/`papp`/`all`/
    `ex` are opaque), so its adequate semantics is two-valued propositional: a valuation
    `v : Formula → Bool`, extended homomorphically by `eval`.  `KProvable` is **sound** (`psound`)
    and **complete** (`pcomplete`) for this `Valid` semantics; cut is then a triviality on the
    semantic side.  Completeness is by well-founded recursion on the connective-complexity measure
    `cx`/`seqCx`, which strictly decreases under every rule (`KStep.seqCx_lt`); each rule is
    invertible (`KStep.valid_premises`) so `Valid` transfers to the smaller premises, and the
    base case (no compound present) forces an identity axiom via the countermodel `v x := memb x
    A`.  `kCut` (and hence `FDeriv.toKProvable'`) depends only on `propext`/`Quot.sound` — no
    `Classical.choice`, no `sorryAx`.  The bridge itself still fires each `KStep` twin on the
    conclusion and discharges the `sremove`-residual drop with one cut via `dropAnte`/`dropSucc`
    (including `negL`/`impL`, whose components land on the *opposite* side — the cut moves the
    principal across sides for free).  This is the **normalized-hyperderivation ↔ real-derivation**
    correspondence, *not* a raw one-step equivalence (provably false — see the counterexample).

    **Proof-producing canonical-key evaluator — DONE (`KProvable.decide`).**  The evaluator is
    `Decidable (KProvable S)`: on success `isTrue d` returns an actual set-key derivation `d`
    (from `KProvable.rule`/`KProvable.ax`), on failure `isFalse` a genuine refutation — a
    *certificate*, not a Boolean (per the audit: `KProvable`/`pcomplete`/`kCut` are `Prop`, so a
    `Bool` would discard the derivation).  Same recursion as `pcomplete`, terminating on `seqCx`;
    `isTrue`/`isFalse` reuse `psound`/`valid_premises`/`pcomplete`.  It computes (verified:
    `p→p`, `p⊢p`, `p∨¬p`, MP all `true`; bare `p`, `p→q` `false`) and depends only on
    `propext`/`Quot.sound`.  `KProvable.normKey_congr` certifies the decision depends only on the
    canonical key `normKey C S` (equal in-closure keys are inter-provable), so this *is* the
    canonical-key evaluator, with state space the `≤ 4^{|C|}` members of `allKeys C`.  Boundary
    (per the audit): a positive `KProvable S` becomes an object-logic proof only through
    `KProvable.sound`, which still needs the lifting-root condition `S.Lifts env Γ`.

    (Separately, and downstream of this whole `FDeriv ↔ KProvable` layer, PS2 still needs the
    genuine focused-completeness result `ProvesProp → FDeriv` — that the analytic calculus is
    complete for the Hilbert kernel — which is not part of this file's set-key correspondence.
    A genuinely *memoized* executable BFS with a runtime table keyed by `normKey` — as opposed to
    this seqCx-recursive certificate producer — is an optional efficiency refinement, not a
    soundness/completeness gate.) -/

end Focused
end ContextualHOL
