namespace Construct
  -- Unique existence (own def; core Lean 4 has no `∃!` notation without Mathlib).
  def ExistsUnique {X : Type} (p : X -> Prop) : Prop := ∃ x, (p x) ∧ ((y : X) -> (p y) -> y = x)

  -- Unique choice / definite description: strictly weaker than `Classical.choose`
  -- (it does not yield excluded middle via Diaconescu), so it keeps the
  -- development off `Classical.choice`.
  axiom get      {X : Type} {h : X -> Prop} : (ExistsUnique h) -> X
  axiom get_spec {X : Type} {h : X -> Prop} (c : ExistsUnique h) : (h (get c))
end Construct

-- How hard / what kind of gap we are leaving open.
inductive Difficulty
  | trivial     -- one-liner, just not worth spelling out here
  | routine     -- standard, mechanical (a tedious induction, bookkeeping)
  | hard        -- genuinely difficult but believed provable
  | later       -- deferred; intend to come back and prove it
  | unclear     -- statement/notation itself needs pinning down first
  | impossible  -- believed false or unprovable as stated (a red flag)
deriving Repr

-- A deliberately unproved step ("gap"): a documented `sorry`. `reason` records
-- what is being assumed and `difficulty` classifies it (see `Difficulty`).
-- Unlike `sorry`, the explanation and rating live in the term, and every use is
-- auditable via `#print axioms`.
-- Use it in term position (`gap "why" .routine`) or tactically
-- (`exact gap "why" .routine`). A `def` that stubs *data* (not a `Prop`) with
-- `gap` must be `noncomputable`.
axiom gap {α : Sort u} (reason : String) (difficulty : Difficulty) : α

-- Peano as a class over a generic carrier `N`: data first, then the laws.
-- Each `instance` discharges the laws from its own construction, so the former
-- axioms (`zero`, `next`, `cond`) become obligations a carrier must meet, not
-- fresh global postulates.
class Peano (N : Type) where
  zero : N                                                     -- data
  next : N -> N                                                -- data
  next_all       : (n : N) -> n = zero ∨ ∃ m : N, next m = n   -- law
  next_injective : (n : N) -> (m : N) -> (next m = next n -> n = m)
  next_non_zero  : (n : N) -> ¬ (next n = zero)
  induction : (β : N -> Prop) ->
    ((β zero) ∧ ((n : N) -> (β n -> β (next n)))) -> ((n : N) -> β n)

namespace Peano
  variable {N : Type} [Peano N]

  def InductionHyp (β : N -> Prop) : Prop := (β zero) ∧ ((n : N) -> (β n -> β (next n)))
  def InductionConclusion (β : N -> Prop) : Prop := (n : N) -> β n

  -- two functions that agree pointwise by induction are equal
  def fun_unique {X : Type} {f g : N -> X}
      (h : InductionHyp (fun n => f n = g n)) : f = g :=
    funext (induction (fun n => f n = g n) h)

  -- the three defining equations of addition, as named fields
  structure IsAddition (f : N -> N -> N) : Prop where
    zero_zero  : f zero zero = zero
    succ_left  : (n : N) -> (m : N) -> f (next n) m = next (f n m)
    succ_right : (n : N) -> (m : N) -> f n (next m) = next (f n m)

  def identity : N -> N := fun n => n

  -- proof of existence (and uniqueness) of addition, for any Peano carrier
  theorem addition_existence : Construct.ExistsUnique (IsAddition (N := N)) :=
    let IsSlice (n : N) (f : N -> N) :=
      ((f zero) = n ∧ ((m : N) -> (f (next m)) = (next (f m))))

    -- the zero/successor recurrence pins `f` down uniquely, so `SliceExists`
    -- is a genuine `∃!` and needs no separate uniqueness bundling.
    let SliceExists (n : N) : Prop := Construct.ExistsUnique (IsSlice n)

    let identity_next_cond : ((m : N) -> (identity (next m)) = (next (identity m))) := by intro w; rfl

      -- the recurrence has at most one solution
    let slice_addition_unique {n : N} {f g : N -> N}
        (hf : IsSlice n f) (hg : IsSlice n g) : f = g := by
      apply fun_unique
      constructor
      · show f zero = g zero
        rw [hf.left, hg.left]
      · intro k ih
        show f (next k) = g (next k)
        rw [hf.right k, hg.right k, show f k = g k from ih]

    -- base case: `identity` solves the recurrence for `zero`
    let slice_addition_zero : SliceExists zero :=
      have hcond : IsSlice zero identity :=
        have identity_cond (n : N) : (identity n) = n := by rfl
        ⟨identity_cond zero, identity_next_cond⟩
      ⟨identity, hcond, fun _ hg => slice_addition_unique hg hcond⟩

    -- step case: if `f` solves for `n`, then `fun k => next (f k)` solves for `next n`
    let slice_addition_induction_step (n : N) (h : SliceExists n) :
      SliceExists (next n) :=
      have ⟨f, hf, _⟩ := h
      let g : N -> N := fun k => next (f k)
      have g_zero : g zero = next n := congrArg next hf.left
      have g_succ : (m : N) -> g (next m) = next (g m) := fun m => congrArg next (hf.right m)
      have hcond : IsSlice (next n) g := ⟨g_zero, g_succ⟩
      ⟨g, hcond, fun _ hgg => slice_addition_unique hgg hcond⟩

    let addition_from_induction :=
      (induction SliceExists (And.intro slice_addition_zero slice_addition_induction_step))

    let addition := fun (n : N) => fun (m : N) =>
      Construct.get (addition_from_induction n) m

    -- `get_spec` returns the defining recurrence of the chosen slice:
    --   spec n : addition n zero = n  ∧  ∀ m, addition n (next m) = next (addition n m)
    have spec : (n : N) -> IsSlice n (addition n) :=
      fun n => Construct.get_spec (addition_from_induction n)
    have addition_0 : addition zero zero = zero :=
      (spec zero).left
    have addition_right : (n : N) -> (m : N) -> addition n (next m) = next (addition n m) :=
      fun n m => (spec n).right m
    have addition_left : (n : N) -> (m : N) -> addition (next n) m = next (addition n m) :=
    fun n m =>
      -- `fun k => next (addition n k)` also solves the recurrence for `next n`,
      -- so uniqueness forces it to equal `addition (next n)`
      have hcond : IsSlice (next n) (fun k => next (addition n k)) :=
        ⟨congrArg next (spec n).left, fun k => congrArg next ((spec n).right k)⟩
      have key : addition (next n) = fun k => next (addition n k) :=
        slice_addition_unique (spec (next n)) hcond
      congrFun key m

    -- uniqueness: any `g` satisfying the same recurrence equals `addition`
    ⟨addition, ⟨addition_0, addition_left, addition_right⟩,
      fun g hg =>
        -- the left-recursion reaches `n`, i.e. `g n zero = n` — itself an induction
        have gn_zero : (n : N) -> g n zero = n :=
          induction (fun n => g n zero = n)
            ⟨hg.zero_zero, fun n ih => (hg.succ_left n zero).trans (congrArg next ih)⟩
        -- each slice `g n` solves `IsSlice n`, so it equals `addition n`
        funext fun n =>
          slice_addition_unique ⟨gn_zero n, fun m => hg.succ_right n m⟩ (spec n)⟩

  noncomputable abbrev addition := Construct.get (addition_existence (N := N))
  def addition_spec := Construct.get_spec (addition_existence (N := N))

end Peano
