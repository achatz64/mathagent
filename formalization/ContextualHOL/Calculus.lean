import ContextualHOL.Substitution

/-!
# The contextual calculus  Γ | Δ ⊢ φ

Deep embedding of the contextual HOL judgment from `ma1/contextual_hol.md`:
an ordered object context Γ, a list of assumptions Δ (each a formula over Γ),
and a conclusion φ over Γ.

Design decisions (see `ma1/m3.md` for the running status):

* Assumption convention: Δ is HEAD-NEWEST, and the intended Core reading of the
  sequent is the single-closure form
    `Vy C[Γ] (chain Δ [[φ]])`   with   `chain (ψ :: Δ) φ = chain Δ (ψ → φ)`.
  With this convention `impIntro` (discharge of the newest assumption) is a
  NO-OP at the closed level — the premise and conclusion close to the same
  Core proposition.

* Propositional layer is Hilbert-style (axiom schemas + `mp` + `hyp`), not
  natural deduction.  Each schema lifts to a single Y-generic ∀-lifted fibre
  tautology; `mp` lifts through the assumption chain by iterating the
  Y-generic K/S facts.  No per-depth families.

* Quantifier layer is the adjunction presentation, NOT "pick arbitrary x":
  `allIntro` / `exElim` move a variable between the object context and the
  formula; freshness is a structural side condition on names.  `allCounit`
  is the counit of weakening ⊣ ∀ (instantiate the weakened universal at the
  context head); its β-content is `translate_substFormula` at `t := var x`.

* Structurality is primitive through the two GENERATORS, not general σ:
  `ctxSubst` (reindex along ⟨t, id⟩, β-content = `SubstEquiv`) and
  `ctxWeaken` (reindex along `snd`).  `allElim` is DERIVED from
  `ctxWeaken` + `allCounit` + `mp` + `ctxSubst` — see `Proves.allElim` below.

* `ctxSubst` substitutes ONLY the conclusion; assumptions must not mention x
  free and pass through unchanged.  (Substituting Δ pointwise would demand
  `avoids x ψ` for every ψ ∈ Δ, which is unsatisfiable in the standard case
  where Δ contains the very universal `∀x.φ` being eliminated — it binds x.)
  On the Core side the assumptions' obligation is the weakening collapse
  `snd ∘ ⟨t, id⟩ = id`, not substitution.  The fully general "substitute Δ
  too" rule stays admissible: move the x-dependent assumption into the
  conclusion with `impIntro`, substitute, and re-discharge with `mp`/`hyp`.

* Named-syntax asymmetry: `exIntro` must stay PRIMITIVE (with `substFormula`
  in the premise).  The dual "unit" route would substitute through the
  formula `φ → ∃x.φ`, which mentions x both free and bound — excluded by the
  `avoids` discipline of `substFormula`.

* Constructors carry `checkFormula?` side conditions exactly where the
  lifting induction will need a translation to exist and cannot recover it
  from the conclusion (cut formulas, schema components, quantifier bodies).
-/

namespace ContextualHOL

-- ===== free occurrence (complement of `avoids`: `avoids` = never BOUND,
-- `occursFree` = appears FREE; x is absent from φ iff both are negative) =====

def occursFreeTerm (x : Name) : Term -> Bool
  | Term.var y => y = x
  | Term.const _ => false
  | Term.raw _ _ => false

def occursFree (x : Name) : Formula -> Bool
  | Formula.atom _ l r => occursFreeTerm x l || occursFreeTerm x r
  | Formula.papp _ a => occursFreeTerm x a
  | Formula.and p q => occursFree x p || occursFree x q
  | Formula.or p q => occursFree x p || occursFree x q
  | Formula.imp p q => occursFree x p || occursFree x q
  | Formula.iff p q => occursFree x p || occursFree x q
  | Formula.not p => occursFree x p
  | Formula.all y _ b => (!(y = x : Bool)) && occursFree x b
  | Formula.ex y _ b => (!(y = x : Bool)) && occursFree x b

-- ===== substitution at an absent name is the identity =====

theorem substTerm_fresh (x : Name) (t : Term) :
    forall (u : Term), occursFreeTerm x u = false -> substTerm x t u = u := by
  intro u h
  cases u with
  | var y =>
      simp [occursFreeTerm] at h
      simp [substTerm, h]
  | const c => rfl
  | raw n ty => rfl

theorem substFormula_fresh (x : Name) (t : Term) :
    forall (phi : Formula), avoids x phi = true -> occursFree x phi = false ->
      substFormula x t phi = phi := by
  intro phi
  induction phi with
  | atom r l right =>
      intro _ hfree
      simp only [occursFree, Bool.or_eq_false_iff] at hfree
      simp [substFormula, substTerm_fresh x t l hfree.1,
        substTerm_fresh x t right hfree.2]
  | papp p a =>
      intro _ hfree
      simp only [occursFree] at hfree
      simp [substFormula, substTerm_fresh x t a hfree]
  | and p q ihP ihQ =>
      intro havoid hfree
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [occursFree, Bool.or_eq_false_iff] at hfree
      simp [substFormula, ihP havoid.1 hfree.1, ihQ havoid.2 hfree.2]
  | or p q ihP ihQ =>
      intro havoid hfree
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [occursFree, Bool.or_eq_false_iff] at hfree
      simp [substFormula, ihP havoid.1 hfree.1, ihQ havoid.2 hfree.2]
  | imp p q ihP ihQ =>
      intro havoid hfree
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [occursFree, Bool.or_eq_false_iff] at hfree
      simp [substFormula, ihP havoid.1 hfree.1, ihQ havoid.2 hfree.2]
  | iff p q ihP ihQ =>
      intro havoid hfree
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [occursFree, Bool.or_eq_false_iff] at hfree
      simp [substFormula, ihP havoid.1 hfree.1, ihQ havoid.2 hfree.2]
  | not p ihP =>
      intro havoid hfree
      simp only [avoids] at havoid
      simp only [occursFree] at hfree
      simp [substFormula, ihP havoid hfree]
  | all n ty b ihB =>
      intro havoid hfree
      simp only [avoids, Bool.and_eq_true] at havoid
      have hnx : ¬ (n = x) := by simpa using havoid.1
      simp only [occursFree] at hfree
      have hb : occursFree x b = false := by
        cases h : occursFree x b
        · rfl
        · rw [h] at hfree; simp [hnx] at hfree
      simp [substFormula, ihB havoid.2 hb]
  | ex n ty b ihB =>
      intro havoid hfree
      simp only [avoids, Bool.and_eq_true] at havoid
      have hnx : ¬ (n = x) := by simpa using havoid.1
      simp only [occursFree] at hfree
      have hb : occursFree x b = false := by
        cases h : occursFree x b
        · rfl
        · rw [h] at hfree; simp [hnx] at hfree
      simp [substFormula, ihB havoid.2 hb]

-- ===== duplicating a context binding preserves typing =====
--
-- Inserting a SECOND copy of the head binding never changes name resolution
-- types (the first copy already shadows everything behind it), so
-- `checkFormula?` is stable.  Needed to weaken a formula from `x :: Γ` to
-- `x :: x :: Γ` in the derived `allElim` (the cut formula `∀x.φ` re-crosses
-- its own binder name).

set_option linter.unusedSimpArgs false in
theorem lookupVar_dup (y : Name) (b : Binding) :
    forall (Ψ Γ : Ctx),
      (lookupVar? y (Ψ ++ b :: b :: Γ)).map Prod.snd
        = (lookupVar? y (Ψ ++ b :: Γ)).map Prod.snd := by
  intro Ψ
  induction Ψ with
  | nil =>
      intro Γ
      simp only [List.nil_append, lookupVar?]
      by_cases hb : b.name = y
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb]
        cases h : lookupVar? y Γ with
        | none => simp [lookupVar?, hb, h]
        | some p => simp [lookupVar?, hb, h]
  | cons c rest ih =>
      intro Γ
      simp only [List.cons_append, lookupVar?]
      by_cases hc : c.name = y
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        have := ih Γ
        cases h1 : lookupVar? y (rest ++ b :: b :: Γ) <;>
          cases h2 : lookupVar? y (rest ++ b :: Γ) <;>
            simp [h1, h2] at this ⊢
        exact this

theorem inferTerm_dup (env : Env) (b : Binding) (Ψ Γ : Ctx) :
    forall (u : Term),
      inferTerm? env (Ψ ++ b :: b :: Γ) u = inferTerm? env (Ψ ++ b :: Γ) u := by
  intro u
  cases u with
  | var y =>
      simp only [inferTerm?]
      have := lookupVar_dup y b Ψ Γ
      cases h1 : lookupVar? y (Ψ ++ b :: b :: Γ) <;>
        cases h2 : lookupVar? y (Ψ ++ b :: Γ) <;>
          simp [h1, h2] at this ⊢
      exact this
  | const c => rfl
  | raw n ty => rfl

theorem checkFormula_dup (env : Env) (b : Binding) :
    forall (phi : Formula) (Ψ Γ : Ctx),
      checkFormula? env (Ψ ++ b :: b :: Γ) phi
        = checkFormula? env (Ψ ++ b :: Γ) phi := by
  intro phi
  induction phi with
  | atom rel l r =>
      intro Ψ Γ
      simp only [checkFormula?, inferTerm_dup]
  | papp p a =>
      intro Ψ Γ
      simp only [checkFormula?, inferTerm_dup]
  | and p q ihP ihQ =>
      intro Ψ Γ
      simp only [checkFormula?, ihP Ψ Γ, ihQ Ψ Γ]
  | or p q ihP ihQ =>
      intro Ψ Γ
      simp only [checkFormula?, ihP Ψ Γ, ihQ Ψ Γ]
  | imp p q ihP ihQ =>
      intro Ψ Γ
      simp only [checkFormula?, ihP Ψ Γ, ihQ Ψ Γ]
  | iff p q ihP ihQ =>
      intro Ψ Γ
      simp only [checkFormula?, ihP Ψ Γ, ihQ Ψ Γ]
  | not p ihP =>
      intro Ψ Γ
      simp only [checkFormula?, ihP Ψ Γ]
  | all n ty body ihB =>
      intro Ψ Γ
      simp only [checkFormula?]
      exact ihB ({ name := n, ty := ty } :: Ψ) Γ
  | ex n ty body ihB =>
      intro Ψ Γ
      simp only [checkFormula?]
      exact ihB ({ name := n, ty := ty } :: Ψ) Γ

theorem checkFormula_dup_head (env : Env) (b : Binding) (Γ : Ctx) (phi : Formula) :
    checkFormula? env (b :: Γ) phi = some () ->
      checkFormula? env (b :: b :: Γ) phi = some () := by
  intro h
  have := checkFormula_dup env b phi [] Γ
  simp only [List.nil_append] at this
  rw [this]
  exact h

-- ===== the calculus =====

inductive Proves (env : Env) : Ctx -> List Formula -> Formula -> Prop where
  -- assumption
  | hyp {Γ : Ctx} {Δ : List Formula} {phi : Formula} :
      phi ∈ Δ -> Proves env Γ Δ phi
  -- discharge the NEWEST assumption (no-op under the head-newest chain closure)
  | impIntro {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      Proves env Γ (phi :: Δ) psi ->
      Proves env Γ Δ (Formula.imp phi psi)
  -- modus ponens (carries wf of the cut formula)
  | mp {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      Proves env Γ Δ (Formula.imp phi psi) ->
      Proves env Γ Δ phi ->
      Proves env Γ Δ psi
  -- Hilbert schemas: K, S, and Łukasiewicz contraposition (classical), then
  -- the ∧/∨/↔ axioms.  Each lifts to one Y-generic ∀-lifted fibre tautology.
  | axK {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp phi (Formula.imp psi phi))
  | axS {Γ : Ctx} {Δ : List Formula} {phi psi chi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      checkFormula? env Γ chi = some () ->
      Proves env Γ Δ (Formula.imp
        (Formula.imp phi (Formula.imp psi chi))
        (Formula.imp (Formula.imp phi psi) (Formula.imp phi chi)))
  | axCP {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp
        (Formula.imp (Formula.not psi) (Formula.not phi))
        (Formula.imp phi psi))
  | axAndL {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp (Formula.and phi psi) phi)
  | axAndR {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp (Formula.and phi psi) psi)
  | axAndI {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp phi (Formula.imp psi (Formula.and phi psi)))
  | axOrL {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp phi (Formula.or phi psi))
  | axOrR {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp psi (Formula.or phi psi))
  | axOrE {Γ : Ctx} {Δ : List Formula} {phi psi chi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      checkFormula? env Γ chi = some () ->
      Proves env Γ Δ (Formula.imp (Formula.imp phi chi)
        (Formula.imp (Formula.imp psi chi)
          (Formula.imp (Formula.or phi psi) chi)))
  | axIffI {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp (Formula.imp phi psi)
        (Formula.imp (Formula.imp psi phi) (Formula.iff phi psi)))
  | axIffL {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp (Formula.iff phi psi) (Formula.imp phi psi))
  | axIffR {Γ : Ctx} {Δ : List Formula} {phi psi : Formula} :
      checkFormula? env Γ phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.imp (Formula.iff phi psi) (Formula.imp psi phi))
  -- ∀-introduction: the adjunction/context move.  The premise lives over the
  -- extended context; freshness of x for Δ is structural (a name condition),
  -- not a proviso about an eigenvariable.
  | allIntro {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty} {phi : Formula} :
      (forall psi, psi ∈ Δ -> occursFree x psi = false) ->
      Proves env ({ name := x, ty := X } :: Γ) Δ phi ->
      Proves env Γ Δ (Formula.all x X phi)
  -- counit of weakening ⊣ ∀: over a context whose head is x, the (shadow-)
  -- weakened universal implies its body.  β-content: `translate_substFormula`
  -- at t := Term.var x (hence the `avoids` condition).
  | allCounit {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty} {phi : Formula} :
      avoids x phi = true ->
      checkFormula? env ({ name := x, ty := X } :: Γ) phi = some () ->
      Proves env ({ name := x, ty := X } :: Γ) Δ
        (Formula.imp (Formula.all x X phi) phi)
  -- ∃-elimination: the dual adjunction move (Exist_gen shape).
  | exElim {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty} {phi psi : Formula} :
      (forall chi, chi ∈ Δ -> occursFree x chi = false) ->
      occursFree x psi = false ->
      checkFormula? env ({ name := x, ty := X } :: Γ) phi = some () ->
      checkFormula? env Γ psi = some () ->
      Proves env Γ Δ (Formula.ex x X phi) ->
      Proves env ({ name := x, ty := X } :: Γ) (phi :: Δ) psi ->
      Proves env Γ Δ psi
  -- ∃-introduction: PRIMITIVE, with substFormula in the premise (see the
  -- header note on the named-syntax asymmetry).
  | exIntro {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty} {phi : Formula}
      {t : Term} :
      inferTerm? env Γ t = some X ->
      avoids x phi = true ->
      (forall w, t = Term.var w -> avoids w phi = true) ->
      checkFormula? env ({ name := x, ty := X } :: Γ) phi = some () ->
      Proves env Γ Δ (substFormula x t phi) ->
      Proves env Γ Δ (Formula.ex x X phi)
  -- structural generator 1: weakening (reindex along `snd`).
  | ctxWeaken {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty} {phi : Formula} :
      occursFree x phi = false ->
      (forall psi, psi ∈ Δ -> occursFree x psi = false) ->
      Proves env Γ Δ phi ->
      Proves env ({ name := x, ty := X } :: Γ) Δ phi
  -- structural generator 2: substitution (reindex along ⟨t, id⟩; β-content =
  -- `SubstEquiv` via `translate_substFormula`).  Only the conclusion is
  -- substituted; assumptions must not mention x free (see the header note).
  | ctxSubst {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty} {phi : Formula}
      {t : Term} :
      inferTerm? env Γ t = some X ->
      avoids x phi = true ->
      (forall w, t = Term.var w -> avoids w phi = true) ->
      (forall psi, psi ∈ Δ -> occursFree x psi = false) ->
      checkFormula? env ({ name := x, ty := X } :: Γ) phi = some () ->
      Proves env ({ name := x, ty := X } :: Γ) Δ phi ->
      Proves env Γ Δ (substFormula x t phi)

namespace Proves

-- ===== derived rules =====

-- φ → φ, the SKK sanity derivation.
theorem impRefl (env : Env) {Γ : Ctx} {Δ : List Formula} (phi : Formula)
    (hphi : checkFormula? env Γ phi = some ()) :
    Proves env Γ Δ (Formula.imp phi phi) := by
  have hii : checkFormula? env Γ (Formula.imp phi phi) = some () := by
    simp [checkFormula?, hphi]
  exact mp (by simp [checkFormula?, hphi])
    (mp (by simp [checkFormula?, hphi])
      (axS (chi := phi) hphi hii hphi)
      (axK hphi hii))
    (axK hphi hphi)

-- ∀-elimination, DERIVED from the generators:
--   Γ|Δ ⊢ ∀x.φ  --ctxWeaken-->  x::Γ|Δ ⊢ ∀x.φ  --allCounit+mp-->
--   x::Γ|Δ ⊢ φ  --ctxSubst t-->  Γ|Δ ⊢ φ[x := t]
theorem allElim (env : Env) {Γ : Ctx} {Δ : List Formula} {x : Name} {X : Ty}
    {phi : Formula} {t : Term}
    (ht : inferTerm? env Γ t = some X)
    (havoid : avoids x phi = true)
    (htavoid : forall w, t = Term.var w -> avoids w phi = true)
    (hfresh : forall psi, psi ∈ Δ -> occursFree x psi = false)
    (hwf : checkFormula? env ({ name := x, ty := X } :: Γ) phi = some ())
    (h : Proves env Γ Δ (Formula.all x X phi)) :
    Proves env Γ Δ (substFormula x t phi) := by
  -- weaken the universal across its own binder name (x is shadowed, not free)
  have h1 : Proves env ({ name := x, ty := X } :: Γ) Δ (Formula.all x X phi) :=
    ctxWeaken (by simp [occursFree]) hfresh h
  -- instantiate at the context head via the counit
  have hwfAll : checkFormula? env ({ name := x, ty := X } :: Γ)
      (Formula.all x X phi) = some () := by
    simp only [checkFormula?]
    exact checkFormula_dup_head env { name := x, ty := X } Γ phi hwf
  have h2 : Proves env ({ name := x, ty := X } :: Γ) Δ phi :=
    mp hwfAll (allCounit havoid hwf) h1
  -- substitute the context head by t
  exact ctxSubst ht havoid htavoid hfresh hwf h2

end Proves

-- ===== sanity examples =====

namespace CalculusExamples

def demoEnv : Env :=
  { consts := [("c", Ty.base "X")],
    rels := [("R", { left := Ty.base "X", right := Ty.base "X" })],
    preds := [("phi", Ty.base "X")] }

-- ⊢ ∀u. (phi(u) → phi(u)) : allIntro over impRefl, empty Δ.
example : Proves demoEnv [] []
    (Formula.all "u" (Ty.base "X")
      (Formula.imp (Formula.papp "phi" (Term.var "u"))
        (Formula.papp "phi" (Term.var "u")))) :=
  Proves.allIntro (fun _ h => nomatch h)
    (Proves.impRefl demoEnv (Formula.papp "phi" (Term.var "u")) rfl)

-- ⊢ (∀u. R(u,c)) → R(c,c) : the derived allElim at t := const c, under
-- impIntro — the eliminated universal sits in Δ (via hyp) and binds u, which
-- is exactly the case the conclusion-only ctxSubst is designed for.
example : Proves demoEnv [] []
    (Formula.imp
      (Formula.all "u" (Ty.base "X")
        (Formula.atom "R" (Term.var "u") (Term.const "c")))
      (Formula.atom "R" (Term.const "c") (Term.const "c"))) :=
  Proves.impIntro rfl
    (Proves.allElim demoEnv
      (t := Term.const "c")
      rfl rfl (fun _ hw => nomatch hw)
      (fun psi h => by
        cases h with
        | head => rfl
        | tail _ h => exact nomatch h)
      rfl
      (Proves.hyp (List.Mem.head _)))

end CalculusExamples

end ContextualHOL
