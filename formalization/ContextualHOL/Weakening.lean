import ContextualHOL.SubstSound
import ContextualHOL.Calculus

/-!
# The weakening generator (M3.3): syntactic relation and CoreThm soundness

Mirror of the M3.2 substitution stack for the OTHER structurality generator:
inserting a fresh binding `x : X` at depth `k` into the context.  The map is
the k-fold binder lift of `snd X C[Γ] : C[Ψ ++ x :: Γ] → C[Ψ ++ Γ]`.

* `insertShiftTerm` / `WeakenEquiv` — the syntactic spec (projections at or
  past the insertion point move one deeper; one constructor per former);
* `translate_weakenFormula` — translating the SAME formula over the
  extended context yields a `WeakenEquiv`-related predicate.  The freshness
  condition is shadowing-aware: `x` must be shadowed by Ψ **or** not free
  in the formula — so weakening a sequent whose Δ contains `∀x.φ` (which
  BINDS x) is covered, which the `avoids`-style condition of the
  substitution lemma would reject;
* `weakenEquiv_sound` — the certificate is redeemable as CoreThm evidence
  at every depth.  No new `.cor` axioms are needed: the lift layers peel by
  the same `snd_pair_lift` facts (the base map is never inspected —
  `peelInside` is base-generic), and the `snd`-base boundary is pure
  `projNorm` spine normalization.
-/

namespace ContextualHOL

open CoreThm

-- ===== syntactic side =====

-- shift a Core term over C[Ψ ++ Γ] to C[Ψ ++ x :: Γ] (k = Ψ.length):
-- projections at or past the insertion point move one deeper, constants
-- re-target their stored context type.
def insertShiftTerm (k : Nat) (newCtx : Ty) : Core.Term -> Core.Term
  | Core.Term.proj n => if n < k then Core.Term.proj n else Core.Term.proj (n + 1)
  | Core.Term.weakening ty _ name => Core.Term.weakening ty newCtx name
  | Core.Term.raw name ty => Core.Term.raw name ty

-- WeakenEquiv k newCtx P P' : P lives over C[Ψ ++ Γ] (k = Ψ.length), P' is P
-- reindexed along the k-fold binder lift of `snd` — i.e. the translation of
-- the same formula over C[Ψ ++ x :: Γ] = newCtx.
inductive WeakenEquiv : Nat -> Ty -> Core.Pred -> Core.Pred -> Prop where
  | atom (k : Nat) (newCtx oldCtx left right : Ty) (rel : Name)
      (l r : Core.Term) :
      WeakenEquiv k newCtx
        (Core.Pred.atom oldCtx left right rel l r)
        (Core.Pred.atom newCtx left right rel
          (insertShiftTerm k newCtx l) (insertShiftTerm k newCtx r))
  | papp (k : Nat) (newCtx oldCtx argTy : Ty) (pred : Name) (arg : Core.Term) :
      WeakenEquiv k newCtx
        (Core.Pred.papp oldCtx argTy pred arg)
        (Core.Pred.papp newCtx argTy pred (insertShiftTerm k newCtx arg))
  | and (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      WeakenEquiv k newCtx p p' -> WeakenEquiv k newCtx q q' ->
      WeakenEquiv k newCtx (Core.Pred.and oldCtx p q) (Core.Pred.and newCtx p' q')
  | or (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      WeakenEquiv k newCtx p p' -> WeakenEquiv k newCtx q q' ->
      WeakenEquiv k newCtx (Core.Pred.or oldCtx p q) (Core.Pred.or newCtx p' q')
  | imp (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      WeakenEquiv k newCtx p p' -> WeakenEquiv k newCtx q q' ->
      WeakenEquiv k newCtx (Core.Pred.imp oldCtx p q) (Core.Pred.imp newCtx p' q')
  | iff (k : Nat) (newCtx oldCtx : Ty) (p p' q q' : Core.Pred) :
      WeakenEquiv k newCtx p p' -> WeakenEquiv k newCtx q q' ->
      WeakenEquiv k newCtx (Core.Pred.iff oldCtx p q) (Core.Pred.iff newCtx p' q')
  | not (k : Nat) (newCtx oldCtx : Ty) (p p' : Core.Pred) :
      WeakenEquiv k newCtx p p' ->
      WeakenEquiv k newCtx (Core.Pred.not oldCtx p) (Core.Pred.not newCtx p')
  | all (k : Nat) (newCtx oldCtx bound : Ty) (p p' : Core.Pred) :
      WeakenEquiv (k + 1) (Ty.prod bound newCtx) p p' ->
      WeakenEquiv k newCtx (Core.Pred.all bound oldCtx p) (Core.Pred.all bound newCtx p')
  | ex (k : Nat) (newCtx oldCtx bound : Ty) (p p' : Core.Pred) :
      WeakenEquiv (k + 1) (Ty.prod bound newCtx) p p' ->
      WeakenEquiv k newCtx (Core.Pred.ex bound oldCtx p) (Core.Pred.ex bound newCtx p')

-- ===== the term-level weakening lemma =====

theorem translateTerm_weaken (env : Env) (x : Binding) :
    forall (Ψ Γ : Ctx) (u : Term) (uc uc' : Core.Term),
      ((lookupVar? x.name Ψ).isSome = true ∨ occursFreeTerm x.name u = false) ->
      translateTerm? env (Ψ ++ Γ) u = some uc ->
      translateTerm? env (Ψ ++ x :: Γ) u = some uc' ->
      uc' = insertShiftTerm Ψ.length (Ctx.obj (Ψ ++ x :: Γ)) uc := by
  intro Ψ Γ u uc uc' hfree hu hu'
  cases u with
  | var y =>
      cases hΨy : lookupVar? y Ψ with
      | some p =>
          obtain ⟨n, tyy⟩ := p
          have h1 := lookupVar_append_left y Ψ Γ n tyy hΨy
          have h2 := lookupVar_append_left y Ψ (x :: Γ) n tyy hΨy
          simp [translateTerm?, h1] at hu
          simp [translateTerm?, h2] at hu'
          subst hu
          subst hu'
          have hlt := lookupVar_lt_length y Ψ n tyy hΨy
          simp only [insertShiftTerm]
          rw [if_pos hlt]
      | none =>
          have hyx : ¬ (y = x.name) := by
            rcases hfree with h | h
            · intro he
              rw [← he, hΨy] at h
              simp at h
            · simpa [occursFreeTerm] using h
          cases hΓy : lookupVar? y Γ with
          | none =>
              have hnone : lookupVar? y (Ψ ++ Γ) = none := by
                rw [lookupVar_append_right y Ψ Γ hΨy]
                simp [hΓy]
              simp [translateTerm?, hnone] at hu
          | some p =>
              obtain ⟨i, tyy⟩ := p
              have h1 : lookupVar? y (Ψ ++ Γ) = some (i + Ψ.length, tyy) := by
                rw [lookupVar_append_right y Ψ Γ hΨy]
                simp [hΓy]
              have hxy : lookupVar? y (x :: Γ) = some (i + 1, tyy) := by
                have hxny : ¬ (x.name = y) := fun h => hyx h.symm
                simp [lookupVar?, hxny, hΓy]
              have h2 : lookupVar? y (Ψ ++ x :: Γ) = some (i + 1 + Ψ.length, tyy) := by
                rw [lookupVar_append_right y Ψ (x :: Γ) hΨy]
                simp [hxy]
              simp [translateTerm?, h1] at hu
              simp [translateTerm?, h2] at hu'
              subst hu
              subst hu'
              have hge : ¬ (i + Ψ.length < Ψ.length) := by omega
              simp only [insertShiftTerm]
              rw [if_neg hge]
              simp only [Core.Term.proj.injEq]
              omega
  | const c =>
      simp only [translateTerm?] at hu hu'
      cases hc : lookupConst? env c with
      | none => rw [hc] at hu; simp at hu
      | some ty =>
          rw [hc] at hu hu'
          simp at hu hu'
          subst hu
          subst hu'
          rfl
  | raw n ty =>
      simp [translateTerm?] at hu hu'
      subst hu
      subst hu'
      rfl

-- ===== the formula-level weakening lemma =====

theorem translate_weakenFormula (env : Env) (x : Binding) :
    forall (psi : Formula) (Ψ Γ : Ctx) (P P' : Core.Pred),
      ((lookupVar? x.name Ψ).isSome = true ∨ occursFree x.name psi = false) ->
      translateFormula? env (Ψ ++ Γ) psi = some P ->
      translateFormula? env (Ψ ++ x :: Γ) psi = some P' ->
      WeakenEquiv Ψ.length (Ctx.obj (Ψ ++ x :: Γ)) P P' := by
  intro psi
  induction psi with
  | atom rel l r =>
      intro Ψ Γ P P' hfree hP hQ
      have hfreeL : (lookupVar? x.name Ψ).isSome = true ∨
          occursFreeTerm x.name l = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.1
      have hfreeR : (lookupVar? x.name Ψ).isSome = true ∨
          occursFreeTerm x.name r = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.2
      simp only [translateFormula?] at hP hQ
      cases hRel : lookupRel? env rel <;> simp [hRel] at hP hQ
      case some sig =>
        cases hL : inferTerm? env (Ψ ++ Γ) l <;> simp [hL] at hP
        case some lTy =>
        cases hR : inferTerm? env (Ψ ++ Γ) r <;> simp [hR] at hP
        case some rTy =>
        cases hEL : expectTy lTy sig.left <;> simp [hEL] at hP
        cases hER : expectTy rTy sig.right <;> simp [hER] at hP
        cases hLC : translateTerm? env (Ψ ++ Γ) l <;> simp [hLC] at hP
        case some lc =>
        cases hRC : translateTerm? env (Ψ ++ Γ) r <;> simp [hRC] at hP
        case some rc =>
        cases hL' : inferTerm? env (Ψ ++ x :: Γ) l <;> simp [hL'] at hQ
        case some lTy' =>
        cases hR' : inferTerm? env (Ψ ++ x :: Γ) r <;> simp [hR'] at hQ
        case some rTy' =>
        cases hEL' : expectTy lTy' sig.left <;> simp [hEL'] at hQ
        cases hER' : expectTy rTy' sig.right <;> simp [hER'] at hQ
        cases hLC' : translateTerm? env (Ψ ++ x :: Γ) l <;> simp [hLC'] at hQ
        case some lc' =>
        cases hRC' : translateTerm? env (Ψ ++ x :: Γ) r <;> simp [hRC'] at hQ
        case some rc' =>
        subst hP
        subst hQ
        rw [translateTerm_weaken env x Ψ Γ l lc lc' hfreeL hLC hLC',
          translateTerm_weaken env x Ψ Γ r rc rc' hfreeR hRC hRC']
        exact WeakenEquiv.atom _ _ _ _ _ _ _ _
  | papp pred arg =>
      intro Ψ Γ P P' hfree hP hQ
      have hfreeA : (lookupVar? x.name Ψ).isSome = true ∨
          occursFreeTerm x.name arg = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree] at h
          exact Or.inr h
      simp only [translateFormula?] at hP hQ
      cases hPred : lookupPred? env pred <;> simp [hPred] at hP hQ
      case some predTy =>
        cases hA : inferTerm? env (Ψ ++ Γ) arg <;> simp [hA] at hP
        case some argTy =>
        cases hEA : expectTy argTy predTy <;> simp [hEA] at hP
        cases hAC : translateTerm? env (Ψ ++ Γ) arg <;> simp [hAC] at hP
        case some ac =>
        cases hA' : inferTerm? env (Ψ ++ x :: Γ) arg <;> simp [hA'] at hQ
        case some argTy' =>
        cases hEA' : expectTy argTy' predTy <;> simp [hEA'] at hQ
        cases hAC' : translateTerm? env (Ψ ++ x :: Γ) arg <;> simp [hAC'] at hQ
        case some ac' =>
        subst hP
        subst hQ
        rw [translateTerm_weaken env x Ψ Γ arg ac ac' hfreeA hAC hAC']
        exact WeakenEquiv.papp _ _ _ _ _ _
  | and p q ihP ihQ =>
      intro Ψ Γ P P' hfree hP hQ
      have hfp : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name p = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.1
      have hfq : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name q = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.2
      simp only [translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq'] at hQ
      subst hP
      subst hQ
      exact WeakenEquiv.and _ _ _ _ _ _ _
        (ihP Ψ Γ _ _ hfp hp hp') (ihQ Ψ Γ _ _ hfq hq hq')
  | or p q ihP ihQ =>
      intro Ψ Γ P P' hfree hP hQ
      have hfp : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name p = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.1
      have hfq : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name q = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.2
      simp only [translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq'] at hQ
      subst hP
      subst hQ
      exact WeakenEquiv.or _ _ _ _ _ _ _
        (ihP Ψ Γ _ _ hfp hp hp') (ihQ Ψ Γ _ _ hfq hq hq')
  | imp p q ihP ihQ =>
      intro Ψ Γ P P' hfree hP hQ
      have hfp : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name p = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.1
      have hfq : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name q = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.2
      simp only [translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq'] at hQ
      subst hP
      subst hQ
      exact WeakenEquiv.imp _ _ _ _ _ _ _
        (ihP Ψ Γ _ _ hfp hp hp') (ihQ Ψ Γ _ _ hfq hq hq')
  | iff p q ihP ihQ =>
      intro Ψ Γ P P' hfree hP hQ
      have hfp : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name p = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.1
      have hfq : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name q = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree, Bool.or_eq_false_iff] at h
          exact Or.inr h.2
      simp only [translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ Γ) p <;> simp [hp] at hP
      cases hq : translateFormula? env (Ψ ++ Γ) q <;> simp [hq] at hP
      cases hp' : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp'] at hQ
      cases hq' : translateFormula? env (Ψ ++ x :: Γ) q <;> simp [hq'] at hQ
      subst hP
      subst hQ
      exact WeakenEquiv.iff _ _ _ _ _ _ _
        (ihP Ψ Γ _ _ hfp hp hp') (ihQ Ψ Γ _ _ hfq hq hq')
  | not p ihP =>
      intro Ψ Γ P P' hfree hP hQ
      have hfp : (lookupVar? x.name Ψ).isSome = true ∨
          occursFree x.name p = false := by
        rcases hfree with h | h
        · exact Or.inl h
        · simp only [occursFree] at h
          exact Or.inr h
      simp only [translateFormula?] at hP hQ
      cases hp : translateFormula? env (Ψ ++ Γ) p <;> simp [hp] at hP
      cases hp' : translateFormula? env (Ψ ++ x :: Γ) p <;> simp [hp'] at hQ
      subst hP
      subst hQ
      exact WeakenEquiv.not _ _ _ _ _ (ihP Ψ Γ _ _ hfp hp hp')
  | all n ty body ihBody =>
      intro Ψ Γ P P' hfree hP hQ
      simp only [translateFormula?] at hP hQ
      cases hb : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ Γ)) body <;>
        simp [hb] at hP
      cases hb' : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ x :: Γ)) body <;>
        simp [hb'] at hQ
      subst hP
      subst hQ
      have hcond : (lookupVar? x.name ({ name := n, ty := ty } :: Ψ)).isSome = true ∨
          occursFree x.name body = false := by
        by_cases hn : n = x.name
        · left
          simp [lookupVar?, hn]
        · rcases hfree with h | h
          · left
            simp only [lookupVar?]
            rw [if_neg hn]
            cases hx : lookupVar? x.name Ψ with
            | none => rw [hx] at h; simp at h
            | some p => obtain ⟨i, t⟩ := p; simp
          · right
            simp only [occursFree] at h
            simpa [hn] using h
      exact WeakenEquiv.all _ _ _ _ _ _
        (ihBody ({ name := n, ty := ty } :: Ψ) Γ _ _ hcond hb hb')
  | ex n ty body ihBody =>
      intro Ψ Γ P P' hfree hP hQ
      simp only [translateFormula?] at hP hQ
      cases hb : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ Γ)) body <;>
        simp [hb] at hP
      cases hb' : translateFormula? env ({ name := n, ty := ty } :: (Ψ ++ x :: Γ)) body <;>
        simp [hb'] at hQ
      subst hP
      subst hQ
      have hcond : (lookupVar? x.name ({ name := n, ty := ty } :: Ψ)).isSome = true ∨
          occursFree x.name body = false := by
        by_cases hn : n = x.name
        · left
          simp [lookupVar?, hn]
        · rcases hfree with h | h
          · left
            simp only [lookupVar?]
            rw [if_neg hn]
            cases hx : lookupVar? x.name Ψ with
            | none => rw [hx] at h; simp at h
            | some p => obtain ⟨i, t⟩ := p; simp
          · right
            simp only [occursFree] at h
            simpa [hn] using h
      exact WeakenEquiv.ex _ _ _ _ _ _
        (ihBody ({ name := n, ty := ty } :: Ψ) Γ _ _ hcond hb hb')

-- ===== soundness: no new axioms needed =====

-- peel exactly the telescope off a projection.
theorem projMapIs_peel (base : Ty) :
    forall (tele : List Ty) (i : Nat) (A : Ty)
      (m : CMap (tele.foldr Ty.prod base) A),
      ProjMapIs (tele.foldr Ty.prod base) (tele.length + i) A m ->
      exists m', ProjMapIs base i A m' := by
  intro tele
  induction tele with
  | nil =>
      intro i A m hm
      simp only [List.length_nil, Nat.zero_add] at hm
      exact ⟨m, hm⟩
  | cons T rest ih =>
      intro i A m hm
      have hlen : (T :: rest).length + i = (rest.length + i) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hlen] at hm
      cases hm with
      | succ _ _ _ _ m' hm' => exact ih i A m' hm'

namespace SlotObs

-- the snd-base boundary: a projection past the insertion point cleans by
-- peeling the lift layers, then pure spine normalization against the bare
-- `snd` (no pair to β at the base — projNorm finishes).
theorem peelWeakenBeyond {I A0 : Ty} (o : SlotObs I A0) (X G : Ty) :
    forall (tele : List Ty) (i : Nat)
      (m : CMap (tele.foldr Ty.prod G) A0)
      (w : CMap (I ×' Ty.final) (tele.foldr Ty.prod (X ×' G)))
      (w' : CMap (I ×' Ty.final) (X ×' G))
      (c : CMap (I ×' Ty.final) A0),
      ProjMapIs (tele.foldr Ty.prod G) (tele.length + i) A0 m ->
      SndSpineIs (X ×' G) tele w w' ->
      ProjCanonIs G i (CMap.comp (CMap.snd X G) w') A0 c ->
      CoreThm (Vy I (CPred.iff
        (o.view (CMap.comp m
          (CMap.comp (liftMapAlong tele (CMap.snd X G)) w)))
        (o.view c))) := by
  intro tele
  induction tele with
  | nil =>
      intro i m w w' c hm hspine hc
      cases hspine
      simp only [List.length_nil, Nat.zero_add] at hm
      exact o.projNorm _ c hm hc
  | cons T rest ih =>
      intro i m w w' c hm hspine hc
      have hlen : (T :: rest).length + i = (rest.length + i) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hlen] at hm
      cases hm with
      | succ _ _ _ _ m' hm' =>
          cases hspine with
          | cons _ _ _ _ hrest =>
              exact CoreThm.forallIffTransApply I _ _ _
                (o.sndPairLift _ _ _ _ m' _
                  (liftMapAlong rest (CMap.snd X G)) _ w)
                (ih i m' _ w' c hm' hrest hc)

-- the full Core-term weakening cleanup.
theorem termWeakenClean {I A0 : Ty} (o : SlotObs I A0) (X G : Ty) :
    forall (tele : List Ty) (u : Core.Term)
      (fl : CMap (tele.foldr Ty.prod G) A0)
      (fl' : CMap (tele.foldr Ty.prod (X ×' G)) A0)
      (w : CMap (I ×' Ty.final) (tele.foldr Ty.prod (X ×' G))),
      TermEmbedIs (tele.foldr Ty.prod G) u A0 fl ->
      TermEmbedIs (tele.foldr Ty.prod (X ×' G))
        (insertShiftTerm tele.length (tele.foldr Ty.prod (X ×' G)) u) A0 fl' ->
      CoreThm (Vy I (CPred.iff
        (o.view (CMap.comp fl
          (CMap.comp (liftMapAlong tele (CMap.snd X G)) w)))
        (o.view (CMap.comp fl' w)))) := by
  intro tele u fl fl' w hfl hfl'
  cases u with
  | raw name ty => cases hfl
  | weakening ty ctx0 c0 =>
      simp only [insertShiftTerm] at hfl'
      cases hfl
      cases hfl'
      exact CoreThm.forallIffTransApply I _ _ _
        (o.constComp (tele.foldr Ty.prod G) c0
          (CMap.comp (liftMapAlong tele (CMap.snd X G)) w))
        (CoreThm.forallIffSymApply I _ _
          (o.constComp (tele.foldr Ty.prod (X ×' G)) c0 w))
  | proj n =>
      cases hfl with
      | proj _ _ _ hm =>
      by_cases hlt : n < tele.length
      · -- before the insertion point: index unchanged
        simp only [insertShiftTerm] at hfl'
        rw [if_pos hlt] at hfl'
        cases hfl' with
        | proj _ _ _ hm' =>
            obtain ⟨c, hc⟩ := projCanonIs_exists hm' w
            exact CoreThm.forallIffTransApply I _ _ _
              (o.peelInside G (X ×' G) (CMap.snd X G) tele n _ w c hlt hm hc)
              (CoreThm.forallIffSymApply I _ _ (o.projNorm w c hm' hc))
      · -- at or past the insertion point: index moves one deeper
        simp only [insertShiftTerm] at hfl'
        rw [if_neg hlt] at hfl'
        cases hfl' with
        | proj _ _ _ hm' =>
            obtain ⟨w', hspine⟩ := sndSpineIs_exists (X ×' G) tele w
            have hn : n = tele.length + (n - tele.length) := by omega
            rw [hn] at hm
            obtain ⟨mG, hmG⟩ := projMapIs_peel G tele (n - tele.length) A0 _ hm
            obtain ⟨c, hc⟩ :=
              projCanonIs_exists hmG (CMap.comp (CMap.snd X G) w')
            have hn' : n + 1 = ((n - tele.length) + 1) + tele.length := by omega
            rw [hn'] at hm'
            exact CoreThm.forallIffTransApply I _ _ _
              (o.peelWeakenBeyond X G tele (n - tele.length) _ w w' c
                hm hspine hc)
              (CoreThm.forallIffSymApply I _ _
                (o.projNorm w c hm'
                  (projCanonIs_extend (X ×' G) tele ((n - tele.length) + 1)
                    w w' A0 c hspine
                    (ProjCanonIs.succ X G A0 (n - tele.length) w' c hc))))

end SlotObs

-- ===== the main weakening soundness theorem =====

theorem weakenEquiv_sound (X G : Ty) :
    forall (P : Core.Pred) (tele : List Ty) (Q : Core.Pred)
      (cP : CPred (tele.foldr Ty.prod G))
      (cQ : CPred (tele.foldr Ty.prod (X ×' G))),
      WeakenEquiv tele.length (tele.foldr Ty.prod (X ×' G)) P Q ->
      PredEmbedIs (tele.foldr Ty.prod G) P cP ->
      PredEmbedIs (tele.foldr Ty.prod (X ×' G)) Q cQ ->
      CoreThm (Vy (tele.foldr Ty.prod (X ×' G)) (CPred.iff
        (CPred.comp cP (CMap.comp (liftMapAlong tele (CMap.snd X G))
          (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final)))
        (CPred.comp cQ (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final)))) := by
  intro P
  induction P with
  | atom ctxP A B rel l r =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE
      cases hcP with
      | atom _ _ _ _ _ _ fl fr hl hr =>
      cases hcQ with
      | atom _ _ _ _ _ _ fl' fr' hl' hr' =>
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallSub2ReindexBeta _ _ _ _ (CPred.raw rel (A ×' B)) fl fr
          (CMap.comp (liftMapAlong tele (CMap.snd X G))
            (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final)))
        (CoreThm.forallIffTransApply _ _ _ _
          ((leftObs _ _ _ (CPred.raw rel (A ×' B))
              (CMap.comp fr (CMap.comp (liftMapAlong tele (CMap.snd X G))
                (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final)))).termWeakenClean
            X G tele l fl fl'
            (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final) hl hl')
          (CoreThm.forallIffTransApply _ _ _ _
            ((rightObs _ _ _ (CPred.raw rel (A ×' B))
                (CMap.comp fl'
                  (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final))).termWeakenClean
              X G tele r fr fr'
              (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final) hr hr')
            (CoreThm.forallIffSymApply _ _ _
              (CoreThm.forallSub2ReindexBeta _ _ _ _ (CPred.raw rel (A ×' B))
                fl' fr'
                (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final)))))
  | papp ctxP A p arg =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE
      cases hcP with
      | papp _ _ _ _ u hu =>
      cases hcQ with
      | papp _ _ _ _ u' hu' =>
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallUnaryReindexBeta _ _ _ (CPred.raw p A) u
          (CMap.comp (liftMapAlong tele (CMap.snd X G))
            (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final)))
        (CoreThm.forallIffTransApply _ _ _ _
          ((unaryObs _ _ (CPred.raw p A)).termWeakenClean X G tele
            arg u u' (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final) hu hu')
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.forallUnaryReindexBeta _ _ _ (CPred.raw p A) u'
              (CMap.fst (tele.foldr Ty.prod (X ×' G)) Ty.final))))
  | and ctxP p q ihp ihq =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | and _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | and _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | and _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compAndStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | or ctxP p q ihp ihq =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | or _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | or _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | or _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compOrStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | imp ctxP p q ihp ihq =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | imp _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | imp _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | imp _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compImpStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | iff ctxP p q ihp ihq =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | iff _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | iff _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | iff _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compIffStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | not ctxP p ihp =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | not _ _ _ _ p' hp =>
      cases hcP with
      | not _ _ cp hcp =>
      cases hcQ with
      | not _ _ cp' hcp' =>
      exact CoreThm.compNotStep _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
  | all bound ctxP p ihp =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | all _ _ _ _ _ p' hp =>
      cases hcP with
      | all _ _ _ cp hcp =>
      cases hcQ with
      | all _ _ _ cq hcq =>
      have ihFused :=
        CoreThm.forallLiftFuse bound (tele.foldr Ty.prod (X ×' G))
          (tele.foldr Ty.prod G)
          (liftMapAlong tele (CMap.snd X G)) cp cq
          (ihp (bound :: tele) p' cp cq hp hcp hcq)
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallReindex bound (tele.foldr Ty.prod G)
          (tele.foldr Ty.prod (X ×' G)) cp
          (liftMapAlong tele (CMap.snd X G)))
        (CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.mp
            (CoreThm.forallForallCong bound (tele.foldr Ty.prod (X ×' G)) _ _)
            ihFused)
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.forallClosureBeta bound (tele.foldr Ty.prod (X ×' G)) cq)))
  | ex bound ctxP p ihp =>
      intro tele Q cP cQ hWE hcP hcQ
      cases hWE with
      | ex _ _ _ _ _ p' hp =>
      cases hcP with
      | ex _ _ _ cp hcp =>
      cases hcQ with
      | ex _ _ _ cq hcq =>
      have ihFused :=
        CoreThm.forallLiftFuse bound (tele.foldr Ty.prod (X ×' G))
          (tele.foldr Ty.prod G)
          (liftMapAlong tele (CMap.snd X G)) cp cq
          (ihp (bound :: tele) p' cp cq hp hcp hcq)
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.existReindex bound (tele.foldr Ty.prod G)
          (tele.foldr Ty.prod (X ×' G)) cp
          (liftMapAlong tele (CMap.snd X G)))
        (CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.mp
            (CoreThm.forallExistCong bound (tele.foldr Ty.prod (X ×' G)) _ _)
            ihFused)
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.existClosureBeta bound (tele.foldr Ty.prod (X ×' G)) cq)))

-- the closed (top-level) instance: weakening by a fresh head binding.
theorem weakenEquiv_sound_closed (X G : Ty) (P Q : Core.Pred)
    (cP : CPred G) (cQ : CPred (X ×' G))
    (hWE : WeakenEquiv 0 (X ×' G) P Q)
    (hcP : PredEmbedIs G P cP)
    (hcQ : PredEmbedIs (X ×' G) Q cQ) :
    CoreThm (Vy (X ×' G) (CPred.iff
      (CPred.comp cP (CMap.comp (CMap.snd X G) (CMap.fst (X ×' G) Ty.final)))
      (CPred.comp cQ (CMap.fst (X ×' G) Ty.final)))) :=
  weakenEquiv_sound X G P [] Q cP cQ hWE hcP hcQ

end ContextualHOL
