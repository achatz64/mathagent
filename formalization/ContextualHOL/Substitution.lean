import ContextualHOL.Core

/-!
# The substitution lemma relative to a finite β-basis

This is the syntactic heart of the finiteness question (core.md, "Expressibility of
core"): is the list of β-rule infra axioms finite?

`SubstEquiv tc k newCtx P Q` is the judgment "`P`, a predicate over the extended
context `Ψ ++ x :: Γ` (`k = Ψ.length`), reindexed along the `k`-fold binder lift of
the substitution map `⟨tc, id⟩ : C[Γ] → X × C[Γ]`, is observationally equal to `Q`".
Its constructors are the deep-embedded β-basis: one constructor per formula former,
each corresponding to a (schema) family of Core axioms of the shape "categorical
equation observed at PC" — see the per-constructor comments mapping them onto
`ma1/beta_basis.cor` / `classical_first_order_logic_new.cor`.

`translate_substFormula` then proves: for every HOL formula φ, object variable x and
term t, the canonical translation of `φ[x := t]` is `SubstEquiv`-related to the
canonical translation of φ over the extended context — at EVERY binder depth `Ψ`
(this genericity is exactly the "schema-per-depth" risk: the theorem shows one
constructor family per former suffices for all depths).

Because `SubstEquiv` has finitely many constructors and the induction closes, the
β-facts needed to consume substitution are finitely generated.  Each constructor now
has a live Core counterpart in `beta_basis.cor` / `classical_first_order_logic_new.cor`;
the next tightening step is to emit/check Core proof terms from these constructors.
-/

namespace ContextualHOL

-- ===== HOL-side substitution =====

-- terms are atomic (var/const/raw), so substitution is name replacement.
def substTerm (x : Name) (t : Term) : Term -> Term
  | Term.var y => if y = x then t else Term.var y
  | Term.const c => Term.const c
  | Term.raw n ty => Term.raw n ty

-- naive substitution: recurses under binders without capture checks.  It is used
-- only under the `avoids` freshness discipline below, which rules capture out.
def substFormula (x : Name) (t : Term) : Formula -> Formula
  | Formula.atom r l right => Formula.atom r (substTerm x t l) (substTerm x t right)
  | Formula.papp p a => Formula.papp p (substTerm x t a)
  | Formula.and p q => Formula.and (substFormula x t p) (substFormula x t q)
  | Formula.or p q => Formula.or (substFormula x t p) (substFormula x t q)
  | Formula.imp p q => Formula.imp (substFormula x t p) (substFormula x t q)
  | Formula.iff p q => Formula.iff (substFormula x t p) (substFormula x t q)
  | Formula.not p => Formula.not (substFormula x t p)
  | Formula.all n ty b => Formula.all n ty (substFormula x t b)
  | Formula.ex n ty b => Formula.ex n ty (substFormula x t b)

-- "`n` is never bound in φ" — the freshness side condition making naive
-- substitution capture-free.
def avoids (n : Name) : Formula -> Bool
  | Formula.atom _ _ _ => true
  | Formula.papp _ _ => true
  | Formula.and p q => avoids n p && avoids n q
  | Formula.or p q => avoids n p && avoids n q
  | Formula.imp p q => avoids n p && avoids n q
  | Formula.iff p q => avoids n p && avoids n q
  | Formula.not p => avoids n p
  | Formula.all m _ b => !(m = n : Bool) && avoids n b
  | Formula.ex m _ b => !(m = n : Bool) && avoids n b

-- ===== Core-side term substitution =====

-- shift a Core term from context C[Γ] to C[Ψ ++ Γ] (k = Ψ.length): projections move
-- k deeper, constants re-target their stored context type.
def shiftCoreTerm (k : Nat) (newCtx : Ty) : Core.Term -> Core.Term
  | Core.Term.proj n => Core.Term.proj (n + k)
  | Core.Term.weakening ty _ name => Core.Term.weakening ty newCtx name
  | Core.Term.raw name ty => Core.Term.raw name ty

-- substitute the variable at de-Bruijn index k by (the shift of) tc, mapping a term
-- over C[Ψ ++ x :: Γ] to one over C[Ψ ++ Γ].
def substCoreTerm (k : Nat) (newCtx : Ty) (tc : Core.Term) : Core.Term -> Core.Term
  | Core.Term.proj n =>
      if n < k then Core.Term.proj n
      else if n = k then shiftCoreTerm k newCtx tc
      else Core.Term.proj (n - 1)
  | Core.Term.weakening ty _ name => Core.Term.weakening ty newCtx name
  | Core.Term.raw name ty => Core.Term.raw name ty

-- ===== the finite β-basis, deep-embedded =====

-- SubstEquiv tc k newCtx P Q :
--   P lives over C[Ψ ++ x :: Γ] with k = Ψ.length and newCtx = C[Ψ ++ Γ];
--   Q is P reindexed along the k-fold binder lift of ⟨tc, id⟩.
-- Each constructor is one β-basis family (all soundness obligations are Core axiom
-- schemas already stated — or flagged — in the live infra):
inductive SubstEquiv (tc : Core.Term) : Nat -> Ty -> Core.Pred -> Core.Pred -> Prop
  -- atom: sub2 reindexes into its argument maps, then each argument slot is a
  -- projection/constant β.  Live counterparts: Forall_sub2_reindex_beta +
  -- Forall_fst_pair_beta_left / Forall_snd_pair_then_beta_right /
  -- Forall_const_comp_beta_right / Forall_pointAt_fst_beta_right (beta_basis.cor);
  -- at a point, beta_sub2_point + beta_v0/weakening_arg*.
  | atom (k : Nat) (newCtx oldCtx left right : Ty) (rel : Name)
      (l r : Core.Term) :
      SubstEquiv tc k newCtx
        (Core.Pred.atom oldCtx left right rel l r)
        (Core.Pred.atom newCtx left right rel
          (substCoreTerm k newCtx tc l) (substCoreTerm k newCtx tc r))
  -- φ-slot: (phi ∘ u) reindexes into u.  Live counterparts:
  -- Forall_unary_reindex_beta plus the unary product/terminal observations
  -- (beta_basis.cor).
  | papp (k : Nat) (newCtx oldCtx argTy : Ty) (pred : Name) (arg : Core.Term) :
      SubstEquiv tc k newCtx
        (Core.Pred.papp oldCtx argTy pred arg)
        (Core.Pred.papp newCtx argTy pred (substCoreTerm k newCtx tc arg))
  -- connective homomorphisms: reindexing distributes over each pointwise
  -- connective, composed via the ∀-lifted congruences.  Live counterparts:
  -- Forall_and/or/imp/iff/not_reindex_beta plus Forall_*Cong (beta_basis.cor).
  | and (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      SubstEquiv tc k newCtx p p' -> SubstEquiv tc k newCtx q q' ->
      SubstEquiv tc k newCtx (Core.Pred.and oldCtx p q) (Core.Pred.and newCtx p' q')
  | or (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      SubstEquiv tc k newCtx p p' -> SubstEquiv tc k newCtx q q' ->
      SubstEquiv tc k newCtx (Core.Pred.or oldCtx p q) (Core.Pred.or newCtx p' q')
  | imp (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      SubstEquiv tc k newCtx p p' -> SubstEquiv tc k newCtx q q' ->
      SubstEquiv tc k newCtx (Core.Pred.imp oldCtx p q) (Core.Pred.imp newCtx p' q')
  | iff (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      SubstEquiv tc k newCtx p p' -> SubstEquiv tc k newCtx q q' ->
      SubstEquiv tc k newCtx (Core.Pred.iff oldCtx p q) (Core.Pred.iff newCtx p' q')
  | not (k : Nat) (newCtx oldCtx : Ty) (p p' : Core.Pred) :
      SubstEquiv tc k newCtx p p' ->
      SubstEquiv tc k newCtx (Core.Pred.not oldCtx p) (Core.Pred.not newCtx p')
  -- quantifiers: reindexing commutes with Forall/Exist along the LIFTED map
  -- (depth k+1) — Beck–Chevalley.  Live counterparts: Forall_reindex
  -- (classical_first_order_logic_new.cor), Exist_reindex, Forall_ForallCong, and
  -- Forall_ExistCong (beta_basis.cor).
  | all (k : Nat) (newCtx oldCtx bound : Ty) (p p' : Core.Pred) :
      SubstEquiv tc (k + 1) (Ty.prod bound newCtx) p p' ->
      SubstEquiv tc k newCtx (Core.Pred.all bound oldCtx p) (Core.Pred.all bound newCtx p')
  | ex (k : Nat) (newCtx oldCtx bound : Ty) (p p' : Core.Pred) :
      SubstEquiv tc (k + 1) (Ty.prod bound newCtx) p p' ->
      SubstEquiv tc k newCtx (Core.Pred.ex bound oldCtx p) (Core.Pred.ex bound newCtx p')

-- ===== context-lookup arithmetic =====

theorem lookupVar_lt_length (y : Name) :
    forall (Ψ : Ctx) (n : Nat) (ty : Ty),
      lookupVar? y Ψ = some (n, ty) -> n < Ψ.length := by
  intro Ψ
  induction Ψ with
  | nil => intro n ty h; simp [lookupVar?] at h
  | cons b rest ih =>
      intro n ty h
      simp only [lookupVar?] at h
      by_cases hb : b.name = y
      · rw [if_pos hb] at h
        simp at h
        obtain ⟨h1, _⟩ := h
        simp [List.length_cons]
        omega
      · rw [if_neg hb] at h
        cases hRest : lookupVar? y rest with
        | none => rw [hRest] at h; simp at h
        | some p =>
            obtain ⟨idx, ty'⟩ := p
            rw [hRest] at h
            simp at h
            obtain ⟨h1, _⟩ := h
            have := ih idx ty' hRest
            simp [List.length_cons]
            omega

theorem lookupVar_append_left (y : Name) :
    forall (Ψ Δ : Ctx) (n : Nat) (ty : Ty),
      lookupVar? y Ψ = some (n, ty) ->
      lookupVar? y (Ψ ++ Δ) = some (n, ty) := by
  intro Ψ
  induction Ψ with
  | nil => intro Δ n ty h; simp [lookupVar?] at h
  | cons b rest ih =>
      intro Δ n ty h
      simp only [lookupVar?] at h
      simp only [List.cons_append, lookupVar?]
      by_cases hb : b.name = y
      · rw [if_pos hb] at h ⊢
        exact h
      · rw [if_neg hb] at h ⊢
        cases hRest : lookupVar? y rest with
        | none => rw [hRest] at h; simp at h
        | some p =>
            obtain ⟨idx, ty'⟩ := p
            rw [hRest] at h
            rw [ih Δ idx ty' hRest]
            exact h

theorem lookupVar_append_right (y : Name) :
    forall (Ψ Δ : Ctx),
      lookupVar? y Ψ = none ->
      lookupVar? y (Ψ ++ Δ) =
        (match lookupVar? y Δ with
          | none => none
          | some (n, ty) => some (n + Ψ.length, ty)) := by
  intro Ψ
  induction Ψ with
  | nil =>
      intro Δ _
      simp only [List.nil_append, List.length_nil]
      cases h : lookupVar? y Δ with
      | none => simp
      | some p =>
          obtain ⟨n, ty⟩ := p
          simp
  | cons b rest ih =>
      intro Δ h
      simp only [lookupVar?] at h
      by_cases hb : b.name = y
      · rw [if_pos hb] at h; simp at h
      · rw [if_neg hb] at h
        have hRestNone : lookupVar? y rest = none := by
          cases hRest : lookupVar? y rest with
          | none => rfl
          | some p => rw [hRest] at h; simp at h
        simp only [List.cons_append, lookupVar?]
        rw [if_neg hb, ih Δ hRestNone]
        cases hΔ : lookupVar? y Δ with
        | none => simp
        | some p =>
            obtain ⟨n, ty⟩ := p
            simp [List.length_cons, Nat.add_assoc]

-- ===== the term-level substitution lemma =====

theorem translateTerm_subst (env : Env) (x : Binding) (t : Term) (tc : Core.Term)
    (Ψ Γ : Ctx) (u : Term) (uc uc' : Core.Term)
    (hx : lookupVar? x.name Ψ = none)
    (ht : translateTerm? env Γ t = some tc)
    (htfresh : forall w, t = Term.var w -> lookupVar? w Ψ = none)
    (hu : translateTerm? env (Ψ ++ x :: Γ) u = some uc)
    (hu' : translateTerm? env (Ψ ++ Γ) (substTerm x.name t u) = some uc') :
    uc' = substCoreTerm Ψ.length (Ctx.obj (Ψ ++ Γ)) tc uc := by
  cases u with
  | var y =>
      by_cases hy : y = x.name
      · -- the substituted occurrence: old side reads proj k, new side reads t itself.
        subst hy
        simp [substTerm] at hu'
        have hLook : lookupVar? x.name (Ψ ++ x :: Γ) = some (Ψ.length, x.ty) := by
          rw [lookupVar_append_right x.name Ψ (x :: Γ) hx]
          simp [lookupVar?]
        simp [translateTerm?, hLook] at hu
        subst hu
        simp only [substCoreTerm]
        simp only [Nat.lt_irrefl, if_false]
        -- uc' is the translation of t in Ψ ++ Γ; show it is the k-shift of tc.
        cases t with
        | var w =>
            have hw := htfresh w rfl
            simp only [translateTerm?] at ht
            cases hΓw : lookupVar? w Γ with
            | none => rw [hΓw] at ht; simp at ht
            | some p =>
                obtain ⟨i, tyw⟩ := p
                rw [hΓw] at ht
                simp at ht
                have hLook' : lookupVar? w (Ψ ++ Γ) = some (i + Ψ.length, tyw) := by
                  rw [lookupVar_append_right w Ψ Γ hw]
                  simp [hΓw]
                simp [translateTerm?, hLook'] at hu'
                subst hu'
                rw [← ht]
                simp [shiftCoreTerm]
        | const c =>
            simp only [translateTerm?] at ht
            cases hc : lookupConst? env c with
            | none => rw [hc] at ht; simp at ht
            | some ty =>
                rw [hc] at ht
                simp at ht
                simp [translateTerm?, hc] at hu'
                subst hu'
                rw [← ht]
                simp [shiftCoreTerm]
        | raw n ty =>
            simp only [translateTerm?] at ht
            simp at ht
            simp [translateTerm?] at hu'
            subst hu'
            rw [← ht]
            simp [shiftCoreTerm]
      · -- an untouched variable: both sides read a projection; only the index moves.
        have hxny : ¬ (x.name = y) := fun h => hy h.symm
        simp [substTerm, hy] at hu'
        cases hΨy : lookupVar? y Ψ with
        | some p =>
            obtain ⟨n, tyy⟩ := p
            have h1 := lookupVar_append_left y Ψ (x :: Γ) n tyy hΨy
            have h2 := lookupVar_append_left y Ψ Γ n tyy hΨy
            simp [translateTerm?, h1] at hu
            simp [translateTerm?, h2] at hu'
            subst hu
            subst hu'
            have hlt := lookupVar_lt_length y Ψ n tyy hΨy
            simp [substCoreTerm, hlt]
        | none =>
            cases hΓy : lookupVar? y Γ with
            | none =>
                have hxy : lookupVar? y (x :: Γ) = none := by
                  simp [lookupVar?, hxny, hΓy]
                have h1 : lookupVar? y (Ψ ++ x :: Γ) = none := by
                  rw [lookupVar_append_right y Ψ (x :: Γ) hΨy]
                  simp [hxy]
                simp [translateTerm?, h1] at hu
            | some p =>
                obtain ⟨i, tyy⟩ := p
                have hxy : lookupVar? y (x :: Γ) = some (i + 1, tyy) := by
                  simp [lookupVar?, hxny, hΓy]
                have h1 : lookupVar? y (Ψ ++ x :: Γ) = some (i + 1 + Ψ.length, tyy) := by
                  rw [lookupVar_append_right y Ψ (x :: Γ) hΨy]
                  simp [hxy]
                have h2 : lookupVar? y (Ψ ++ Γ) = some (i + Ψ.length, tyy) := by
                  rw [lookupVar_append_right y Ψ Γ hΨy]
                  simp [hΓy]
                simp [translateTerm?, h1] at hu
                simp [translateTerm?, h2] at hu'
                subst hu
                subst hu'
                simp only [substCoreTerm]
                rw [if_neg (by omega), if_neg (by omega)]
                congr 1
                omega
  | const c =>
      simp [substTerm] at hu'
      simp only [translateTerm?] at hu hu'
      cases hc : lookupConst? env c with
      | none => rw [hc] at hu; simp at hu
      | some ty =>
          rw [hc] at hu hu'
          simp at hu hu'
          subst hu
          subst hu'
          simp [substCoreTerm]
  | raw n ty =>
      simp [substTerm] at hu'
      simp [translateTerm?] at hu hu'
      subst hu
      subst hu'
      simp [substCoreTerm]

-- ===== the substitution lemma =====

theorem translate_substFormula (env : Env) (x : Binding) (t : Term) (tc : Core.Term)
    (Γ : Ctx) (ht : translateTerm? env Γ t = some tc) :
    forall (phi : Formula) (Ψ : Ctx) (P Q : Core.Pred),
      lookupVar? x.name Ψ = none ->
      (forall w, t = Term.var w -> lookupVar? w Ψ = none) ->
      avoids x.name phi = true ->
      (forall w, t = Term.var w -> avoids w phi = true) ->
      translateFormula? env (Ψ ++ x :: Γ) phi = some P ->
      translateFormula? env (Ψ ++ Γ) (substFormula x.name t phi) = some Q ->
      SubstEquiv tc Ψ.length (Ctx.obj (Ψ ++ Γ)) P Q := by
  intro phi
  induction phi with
  | atom rel left right =>
      intro Ψ P Q hx htfresh _ _ hP hQ
      simp only [substFormula, translateFormula?] at hP hQ
      cases hRel : lookupRel? env rel <;> simp [hRel] at hP hQ
      case some sig =>
        cases hL : inferTerm? env (Ψ ++ x :: Γ) left <;> simp [hL] at hP
        case some leftTy =>
        cases hR : inferTerm? env (Ψ ++ x :: Γ) right <;> simp [hR] at hP
        case some rightTy =>
        cases hEL : expectTy leftTy sig.left <;> simp [hEL] at hP
        cases hER : expectTy rightTy sig.right <;> simp [hER] at hP
        cases hLC : translateTerm? env (Ψ ++ x :: Γ) left <;> simp [hLC] at hP
        case some lc =>
        cases hRC : translateTerm? env (Ψ ++ x :: Γ) right <;> simp [hRC] at hP
        case some rc =>
        cases hL' : inferTerm? env (Ψ ++ Γ) (substTerm x.name t left) <;> simp [hL'] at hQ
        case some leftTy' =>
        cases hR' : inferTerm? env (Ψ ++ Γ) (substTerm x.name t right) <;> simp [hR'] at hQ
        case some rightTy' =>
        cases hEL' : expectTy leftTy' sig.left <;> simp [hEL'] at hQ
        cases hER' : expectTy rightTy' sig.right <;> simp [hER'] at hQ
        cases hLC' : translateTerm? env (Ψ ++ Γ) (substTerm x.name t left) <;>
          simp [hLC'] at hQ
        case some lc' =>
        cases hRC' : translateTerm? env (Ψ ++ Γ) (substTerm x.name t right) <;>
          simp [hRC'] at hQ
        case some rc' =>
        have hlc := translateTerm_subst env x t tc Ψ Γ left lc lc' hx ht htfresh hLC hLC'
        have hrc := translateTerm_subst env x t tc Ψ Γ right rc rc' hx ht htfresh hRC hRC'
        subst hP
        subst hQ
        rw [hlc, hrc]
        exact SubstEquiv.atom _ _ _ _ _ _ _ _
  | papp pred arg =>
      intro Ψ P Q hx htfresh _ _ hP hQ
      simp only [substFormula, translateFormula?] at hP hQ
      cases hPred : lookupPred? env pred <;> simp [hPred] at hP hQ
      case some predTy =>
        cases hA : inferTerm? env (Ψ ++ x :: Γ) arg <;> simp [hA] at hP
        case some argTy =>
        cases hEA : expectTy argTy predTy <;> simp [hEA] at hP
        cases hAC : translateTerm? env (Ψ ++ x :: Γ) arg <;> simp [hAC] at hP
        case some ac =>
        cases hA' : inferTerm? env (Ψ ++ Γ) (substTerm x.name t arg) <;> simp [hA'] at hQ
        case some argTy' =>
        cases hEA' : expectTy argTy' predTy <;> simp [hEA'] at hQ
        cases hAC' : translateTerm? env (Ψ ++ Γ) (substTerm x.name t arg) <;>
          simp [hAC'] at hQ
        case some ac' =>
        have hac := translateTerm_subst env x t tc Ψ Γ arg ac ac' hx ht htfresh hAC hAC'
        subst hP
        subst hQ
        rw [hac]
        exact SubstEquiv.papp _ _ _ _ _ _
  | and p q ihP ihQ =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [substFormula, translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t p) <;>
        simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t q) <;>
        simp [hq'] at hQ
      subst hP
      subst hQ
      exact SubstEquiv.and _ _ _ _ _ _ _
        (ihP Ψ _ _ hx htfresh havoid.1
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.1)
          hp hp')
        (ihQ Ψ _ _ hx htfresh havoid.2
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.2)
          hq hq')
  | or p q ihP ihQ =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [substFormula, translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t p) <;>
        simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t q) <;>
        simp [hq'] at hQ
      subst hP
      subst hQ
      exact SubstEquiv.or _ _ _ _ _ _ _
        (ihP Ψ _ _ hx htfresh havoid.1
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.1)
          hp hp')
        (ihQ Ψ _ _ hx htfresh havoid.2
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.2)
          hq hq')
  | imp p q ihP ihQ =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [substFormula, translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t p) <;>
        simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t q) <;>
        simp [hq'] at hQ
      subst hP
      subst hQ
      exact SubstEquiv.imp _ _ _ _ _ _ _
        (ihP Ψ _ _ hx htfresh havoid.1
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.1)
          hp hp')
        (ihQ Ψ _ _ hx htfresh havoid.2
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.2)
          hq hq')
  | iff p q ihP ihQ =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids, Bool.and_eq_true] at havoid
      simp only [substFormula, translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t p) <;>
        simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t q) <;>
        simp [hq'] at hQ
      subst hP
      subst hQ
      exact SubstEquiv.iff _ _ _ _ _ _ _
        (ihP Ψ _ _ hx htfresh havoid.1
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.1)
          hp hp')
        (ihQ Ψ _ _ hx htfresh havoid.2
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.2)
          hq hq')
  | not p ihP =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids] at havoid
      simp only [substFormula, translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp] at hP
      cases hp' : translateFormula? env (Ψ ++ Γ) (substFormula x.name t p) <;>
        simp [hp'] at hQ
      subst hP
      subst hQ
      exact SubstEquiv.not _ _ _ _ _
        (ihP Ψ _ _ hx htfresh havoid
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids] at this
            exact this)
          hp hp')
  | all n ty body ihBody =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids, Bool.and_eq_true] at havoid
      have hnx : ¬ (n = x.name) := by simpa using havoid.1
      simp only [substFormula, translateFormula?] at hP hQ
      cases hb : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ x :: Γ)) body <;>
        simp [hb] at hP
      cases hb' : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ Γ))
          (substFormula x.name t body) <;>
        simp [hb'] at hQ
      subst hP
      subst hQ
      have hx' : lookupVar? x.name ({ name := n, ty := ty } :: Ψ) = none := by
        simp [lookupVar?, hnx, hx]
      have htfresh' : forall w, t = Term.var w ->
          lookupVar? w ({ name := n, ty := ty } :: Ψ) = none := by
        intro w hw
        have hAvoidW := htavoid w hw
        simp only [avoids, Bool.and_eq_true] at hAvoidW
        have hnw : ¬ (n = w) := by simpa using hAvoidW.1
        simp [lookupVar?, hnw, htfresh w hw]
      exact SubstEquiv.all _ _ _ _ _ _
        (ihBody ({ name := n, ty := ty } :: Ψ) _ _ hx' htfresh' havoid.2
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.2)
          hb hb')
  | ex n ty body ihBody =>
      intro Ψ P Q hx htfresh havoid htavoid hP hQ
      simp only [avoids, Bool.and_eq_true] at havoid
      have hnx : ¬ (n = x.name) := by simpa using havoid.1
      simp only [substFormula, translateFormula?] at hP hQ
      cases hb : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ x :: Γ)) body <;>
        simp [hb] at hP
      cases hb' : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ Γ))
          (substFormula x.name t body) <;>
        simp [hb'] at hQ
      subst hP
      subst hQ
      have hx' : lookupVar? x.name ({ name := n, ty := ty } :: Ψ) = none := by
        simp [lookupVar?, hnx, hx]
      have htfresh' : forall w, t = Term.var w ->
          lookupVar? w ({ name := n, ty := ty } :: Ψ) = none := by
        intro w hw
        have hAvoidW := htavoid w hw
        simp only [avoids, Bool.and_eq_true] at hAvoidW
        have hnw : ¬ (n = w) := by simpa using hAvoidW.1
        simp [lookupVar?, hnw, htfresh w hw]
      exact SubstEquiv.ex _ _ _ _ _ _
        (ihBody ({ name := n, ty := ty } :: Ψ) _ _ hx' htfresh' havoid.2
          (fun w hw => by
            have := htavoid w hw
            simp only [avoids, Bool.and_eq_true] at this
            exact this.2)
          hb hb')

-- the closed (top-level) instance: substituting into the head variable of the context.
theorem translate_substFormula_closed (env : Env) (x : Binding) (t : Term)
    (tc : Core.Term) (Γ : Ctx) (phi : Formula) (P Q : Core.Pred)
    (ht : translateTerm? env Γ t = some tc)
    (havoid : avoids x.name phi = true)
    (htavoid : forall w, t = Term.var w -> avoids w phi = true)
    (hP : translateFormula? env (x :: Γ) phi = some P)
    (hQ : translateFormula? env Γ (substFormula x.name t phi) = some Q) :
    SubstEquiv tc 0 (Ctx.obj Γ) P Q :=
  translate_substFormula env x t tc Γ ht phi [] P Q
    (by simp [lookupVar?]) (fun _ _ => by simp [lookupVar?])
    havoid htavoid hP hQ

end ContextualHOL
