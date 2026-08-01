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
  next_injective : (n : N) -> (m : N) -> (next m = next n -> n = m)   -- law
  next_non_zero  : (n : N) -> ¬ (next n = zero)
  induction : (β : N -> Prop) ->
    ((β zero) ∧ ((n : N) -> (β n -> β (next n)))) -> ((n : N) -> β n)

namespace Peano
  variable {N : Type} [Peano N]

  -- Derivable from `induction`, so it is a theorem rather than a field: no
  -- `instance` should have to discharge it.  Take `β` to be the statement
  -- itself; the step case does not even use its hypothesis.
  theorem next_all (n : N) : n = zero ∨ ∃ m : N, next m = n :=
    induction (fun n => n = zero ∨ ∃ m : N, next m = n)
      ⟨Or.inl rfl, fun k _ => Or.inr ⟨k, rfl⟩⟩ n

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

  /- ## Recursion

  `induction` has motive `β : N -> Prop`: it can *prove* things about every `n`,
  but it cannot hand back an element of `X`, so it cannot define a function by
  recursion.  `Construct.get` is the missing step, and doing it once — here —
  turns every later definition by recursion into three lines.

  The recursion is run on the graph rather than on values, because that is the
  part that has to be stated without recursion: `RecRel` is the least relation
  containing `(zero, x0)` and closed under `next` on the left and `s` on the
  right, written `inductive`-free as the intersection of all such relations. -/

  section Recursion
  variable {X : Type}

  -- `f` solves the recurrence given by a start value and a step
  structure IsRec (x0 : X) (s : X -> X) (f : N -> X) : Prop where
    zero : f zero = x0
    next : (n : N) -> f (next n) = s (f n)

  def RecRel (x0 : X) (s : X -> X) (n : N) (x : X) : Prop :=
    (S : N -> X -> Prop) -> S zero x0 ->
      ((a : N) -> (b : X) -> S a b -> S (next a) (s b)) -> S n x

  variable (x0 : X) (s : X -> X)

  -- the two closure properties, immediately from the definition
  theorem rec_rel_zero : RecRel (N := N) x0 s zero x0 :=
    fun _ h0 _ => h0

  theorem rec_rel_next {n : N} {x : X} (h : RecRel x0 s n x) :
      RecRel x0 s (next n) (s x) :=
    fun S h0 hs => hs n x (h S h0 hs)

  -- inversion: a successor is only ever related to a step.  The invariant must
  -- carry `RecRel a b` itself, otherwise the closure case cannot rebuild it.
  theorem rec_rel_inv {n : N} {x : X} (h : RecRel x0 s (next n) x) :
      ∃ b : X, x = s b ∧ RecRel x0 s n b :=
    let S : N -> X -> Prop := fun a b =>
      RecRel x0 s a b ∧ ((a = zero ∧ b = x0) ∨
        ∃ a' : N, ∃ b' : X, a = next a' ∧ b = s b' ∧ RecRel x0 s a' b')
    have h0 : S zero x0 := ⟨rec_rel_zero x0 s, Or.inl ⟨rfl, rfl⟩⟩
    have hs : (a : N) -> (b : X) -> S a b -> S (next a) (s b) :=
      fun a b hab => ⟨rec_rel_next x0 s hab.left, Or.inr ⟨a, b, rfl, rfl, hab.left⟩⟩
    match (h S h0 hs).right with
    | Or.inl hz => absurd hz.left (next_non_zero n)
    | Or.inr ⟨a', b', ha, hb, hab⟩ => ⟨b', hb, next_injective a' n ha ▸ hab⟩

  -- one induction delivers existence *and* uniqueness of the value at each `n`
  theorem rec_rel_existence (n : N) :
      Construct.ExistsUnique (RecRel (N := N) x0 s n) :=
    have base : Construct.ExistsUnique (RecRel (N := N) x0 s zero) :=
      ⟨x0, rec_rel_zero x0 s, fun _y hy =>
        let S : N -> X -> Prop := fun a b => a = zero -> b = x0
        have h0 : S zero x0 := fun _ => rfl
        have hs : (a : N) -> (b : X) -> S a b -> S (next a) (s b) :=
          fun a _ _ hcontra => absurd hcontra (next_non_zero a)
        hy S h0 hs rfl⟩
    have step : (k : N) -> Construct.ExistsUnique (RecRel (N := N) x0 s k) ->
        Construct.ExistsUnique (RecRel (N := N) x0 s (next k)) :=
      fun _k ⟨b, hb, hunique⟩ =>
        ⟨s b, rec_rel_next x0 s hb, fun _y hy =>
          have ⟨c, hyc, hkc⟩ := rec_rel_inv x0 s hy
          hyc.trans (congrArg s (hunique c hkc))⟩
    induction (fun k => Construct.ExistsUnique (RecRel (N := N) x0 s k))
      ⟨base, step⟩ n

  theorem rec_rel_unique {n : N} {x y : X}
      (hx : RecRel x0 s n x) (hy : RecRel x0 s n y) : x = y :=
    have ⟨_, _, hunique⟩ := rec_rel_existence (N := N) x0 s n
    (hunique x hx).trans (hunique y hy).symm

  -- the solution of the recurrence
  noncomputable def recurse : N -> X := fun n => Construct.get (rec_rel_existence x0 s n)

  theorem rec_rel_recurse (n : N) : RecRel x0 s n (recurse (N := N) x0 s n) :=
    Construct.get_spec (rec_rel_existence x0 s n)

  theorem recurse_is_rec : IsRec x0 s (recurse (N := N) x0 s) :=
    ⟨rec_rel_unique x0 s (rec_rel_recurse x0 s zero) (rec_rel_zero x0 s),
     fun n => rec_rel_unique x0 s (rec_rel_recurse x0 s (next n))
       (rec_rel_next x0 s (rec_rel_recurse x0 s n))⟩

  -- uniqueness needs no choice principle: it is one induction
  theorem rec_unique {f g : N -> X} (hf : IsRec x0 s f) (hg : IsRec x0 s g) : f = g :=
    fun_unique ⟨hf.zero.trans hg.zero.symm,
      fun n ih => (hf.next n).trans ((congrArg s ih).trans (hg.next n).symm)⟩

  -- the recursion theorem: every recurrence has exactly one solution
  theorem recursion : Construct.ExistsUnique (IsRec (N := N) x0 s) :=
    ⟨recurse x0 s, recurse_is_rec x0 s,
      fun _g hg => rec_unique x0 s hg (recurse_is_rec x0 s)⟩

  end Recursion

  /- ## Categoricity (Dedekind)

  Any two Peano carriers are uniquely isomorphic.  With `recursion` in hand this
  is not a construction at all: it is the recurrence `zero, next` read in `M`. -/

  section Cast
  variable {M : Type} [Peano M]

  noncomputable def cast : N -> M := recurse zero next

  theorem cast_existence : Construct.ExistsUnique (IsRec (N := N) (zero : M) next) :=
    recursion zero next

  theorem cast_zero : cast (N := N) (M := M) zero = zero := (recurse_is_rec zero next).zero
  theorem cast_next (n : N) : cast (M := M) (next n) = next (cast (M := M) n) :=
    (recurse_is_rec zero next).next n

  end Cast

end Peano
