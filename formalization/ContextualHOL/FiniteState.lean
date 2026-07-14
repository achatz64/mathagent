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

/-! ### TODO — what remains for the memoized search algorithm

    With `FSequent.Lifts` + `KStep.preserves_lifts` (typed guard re-attached) and
    `KProvable.sound` (set-key soundness into `denote`, for lifting roots) in hand, the *sound*
    direction of correspondence is done.  Two things remain before the hypergraph is a
    *certified* memoized proof-search:

    **Completeness (the harder direction).**  `denote`/`FTrace`-derivable `→ KProvable` (under
    `FSequent.Lifts`): the analytic rules must be shown invertible up to the set-key, so that any
    real derivation is matched by a hyperderivation.  Because the set-level rule bakes in
    contraction (and exchange), this stays a **normalized-hyperderivation ↔ real-derivation**
    correspondence, *not* a raw one-step equivalence (which is provably false, see the
    counterexample above).

    **Canonical-key evaluator.**  `KStep` is a relation on list-valued `FSequent`s that is
    well-defined *modulo* `SetEq` (`KStep.respects_setEq`) — not yet literally a graph whose
    vertices are canonical `normKey`s.  The executable finite hypergraph still needs a
    relation/evaluator stated at the canonical-key level, over which the memoized AND/OR
    evaluation runs.

    Once both land, the memoized AND/OR evaluation over the `≤ 4^{|C|}` keys (terminating by
    the finite bound) is the decision procedure. -/

end Focused
end ContextualHOL
