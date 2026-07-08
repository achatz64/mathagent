import ContextualHOL.Elab

namespace ContextualHOL

namespace Core

inductive Term where
  | proj : Nat -> Term
  | weakening : Ty -> Ty -> Name -> Term
  | raw : Name -> Ty -> Term
  deriving Repr, BEq, DecidableEq

inductive Pred where
  | atom : Ty -> Ty -> Ty -> Name -> Term -> Term -> Pred
  | and : Ty -> Pred -> Pred -> Pred
  | or : Ty -> Pred -> Pred -> Pred
  | imp : Ty -> Pred -> Pred -> Pred
  | not : Ty -> Pred -> Pred
  | all : Ty -> Ty -> Pred -> Pred
  | ex : Ty -> Ty -> Pred -> Pred
  deriving Repr, BEq, DecidableEq

inductive Closed where
  | term : Pred -> Closed
  deriving Repr, BEq, DecidableEq

end Core

def translateTerm? (env : Env) (ctx : Ctx) : Term -> Option Core.Term
  | Term.var name => do
      let (idx, _) <- lookupVar? name ctx
      pure (Core.Term.proj idx)
  | Term.const name => do
      let ty <- lookupConst? env name
      pure (Core.Term.weakening ty (Ctx.obj ctx) name)
  | Term.raw name ty =>
      pure (Core.Term.raw name ty)

def translateFormula? (env : Env) (ctx : Ctx) : Formula -> Option Core.Pred
  | Formula.atom rel left right => do
      let sig <- lookupRel? env rel
      let leftTy <- inferTerm? env ctx left
      let rightTy <- inferTerm? env ctx right
      expectTy leftTy sig.left
      expectTy rightTy sig.right
      let leftCore <- translateTerm? env ctx left
      let rightCore <- translateTerm? env ctx right
      pure (Core.Pred.atom (Ctx.obj ctx) sig.left sig.right rel leftCore rightCore)
  | Formula.and p q => do
      pure (Core.Pred.and (Ctx.obj ctx)
        (<- translateFormula? env ctx p)
        (<- translateFormula? env ctx q))
  | Formula.or p q => do
      pure (Core.Pred.or (Ctx.obj ctx)
        (<- translateFormula? env ctx p)
        (<- translateFormula? env ctx q))
  | Formula.imp p q => do
      pure (Core.Pred.imp (Ctx.obj ctx)
        (<- translateFormula? env ctx p)
        (<- translateFormula? env ctx q))
  | Formula.not p => do
      pure (Core.Pred.not (Ctx.obj ctx)
        (<- translateFormula? env ctx p))
  | Formula.all name ty body => do
      let bodyCore <- translateFormula? env ({ name := name, ty := ty } :: ctx) body
      pure (Core.Pred.all ty (Ctx.obj ctx) bodyCore)
  | Formula.ex name ty body => do
      let bodyCore <- translateFormula? env ({ name := name, ty := ty } :: ctx) body
      pure (Core.Pred.ex ty (Ctx.obj ctx) bodyCore)

def assumptionsToBody (ctxTy : Ty) : List Core.Pred -> Core.Pred -> Core.Pred
  | [], conclusion => conclusion
  | assumption :: rest, conclusion =>
      Core.Pred.imp ctxTy assumption (assumptionsToBody ctxTy rest conclusion)

def translateAllFormulas? (env : Env) (ctx : Ctx) : List Formula -> Option (List Core.Pred)
  | [] => some []
  | formula :: rest => do
      let translated <- translateFormula? env ctx formula
      let translatedRest <- translateAllFormulas? env ctx rest
      pure (translated :: translatedRest)

def translateSequentBody? (env : Env) (seq : Sequent) : Option Core.Pred := do
  let assumptions <- translateAllFormulas? env seq.objectCtx seq.assumptions
  let conclusion <- translateFormula? env seq.objectCtx seq.conclusion
  pure (assumptionsToBody (Ctx.obj seq.objectCtx) assumptions conclusion)

def closeContext : Ctx -> Core.Pred -> Core.Closed
  | [], pred => Core.Closed.term pred
  | b :: rest, pred =>
      closeContext rest (Core.Pred.all b.ty (Ctx.obj rest) pred)

def translateClosedSequent? (env : Env) (seq : Sequent) : Option Core.Closed := do
  closeContext seq.objectCtx (<- translateSequentBody? env seq)

theorem closeContext_nil (pred : Core.Pred) :
    closeContext [] pred = Core.Closed.term pred := rfl

theorem closeContext_cons (b : Binding) (ctx : Ctx) (pred : Core.Pred) :
    closeContext (b :: ctx) pred =
      closeContext ctx (Core.Pred.all b.ty (Ctx.obj ctx) pred) := rfl

theorem inferTerm_translateTerm_isSome (env : Env) (ctx : Ctx) (term : Term) :
    (inferTerm? env ctx term).isSome = true ->
      (translateTerm? env ctx term).isSome = true := by
  intro h
  cases term with
  | var name =>
      simp [inferTerm?, translateTerm?] at h ⊢
      cases hLookup : lookupVar? name ctx <;> simp [hLookup] at h ⊢
  | const name =>
      simp [inferTerm?, translateTerm?] at h ⊢
      cases hLookup : lookupConst? env name <;> simp [hLookup] at h ⊢
  | raw _ _ =>
      simp [translateTerm?]

theorem checkFormula_isSome_translateFormula_isSome (env : Env) :
    forall (ctx : Ctx) (formula : Formula),
      (checkFormula? env ctx formula).isSome = true ->
        (translateFormula? env ctx formula).isSome = true := by
  intro ctx formula
  induction formula generalizing ctx with
  | atom rel left right =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      cases hRel : lookupRel? env rel <;> simp [hRel] at h ⊢
      case some sig =>
        cases hLeft : inferTerm? env ctx left <;> simp [hLeft] at h ⊢
        case some leftTy =>
          cases hRight : inferTerm? env ctx right <;> simp [hRight] at h ⊢
          case some rightTy =>
            cases hExpectLeft : expectTy leftTy sig.left <;> simp [hExpectLeft] at h ⊢
            cases hExpectRight : expectTy rightTy sig.right <;> simp [hExpectRight] at h ⊢
            have hLeftCore :
                (translateTerm? env ctx left).isSome = true :=
              inferTerm_translateTerm_isSome env ctx left (by simp [hLeft])
            have hRightCore :
                (translateTerm? env ctx right).isSome = true :=
              inferTerm_translateTerm_isSome env ctx right (by simp [hRight])
            cases hLeftTranslated : translateTerm? env ctx left <;>
              simp [hLeftTranslated] at hLeftCore ⊢
            cases hRightTranslated : translateTerm? env ctx right <;>
              simp [hRightTranslated] at hRightCore ⊢
  | and p q ihP ihQ =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      cases hP : checkFormula? env ctx p <;> simp [hP] at h
      have hTP := ihP ctx (by simp [hP])
      cases hPTranslated : translateFormula? env ctx p <;>
        simp [hPTranslated] at hTP ⊢
      cases hQ : checkFormula? env ctx q <;> simp [hQ] at h
      have hTQ := ihQ ctx (by simp [hQ])
      cases hQTranslated : translateFormula? env ctx q <;>
        simp [hQTranslated] at hTQ ⊢
  | or p q ihP ihQ =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      cases hP : checkFormula? env ctx p <;> simp [hP] at h
      have hTP := ihP ctx (by simp [hP])
      cases hPTranslated : translateFormula? env ctx p <;>
        simp [hPTranslated] at hTP ⊢
      cases hQ : checkFormula? env ctx q <;> simp [hQ] at h
      have hTQ := ihQ ctx (by simp [hQ])
      cases hQTranslated : translateFormula? env ctx q <;>
        simp [hQTranslated] at hTQ ⊢
  | imp p q ihP ihQ =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      cases hP : checkFormula? env ctx p <;> simp [hP] at h
      have hTP := ihP ctx (by simp [hP])
      cases hPTranslated : translateFormula? env ctx p <;>
        simp [hPTranslated] at hTP ⊢
      cases hQ : checkFormula? env ctx q <;> simp [hQ] at h
      have hTQ := ihQ ctx (by simp [hQ])
      cases hQTranslated : translateFormula? env ctx q <;>
        simp [hQTranslated] at hTQ ⊢
  | not p ihP =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      have hTP := ihP ctx h
      cases hPTranslated : translateFormula? env ctx p <;>
        simp [hPTranslated] at hTP ⊢
  | all name ty body ihBody =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      have hBody := ihBody ({ name := name, ty := ty } :: ctx) h
      cases hTranslated : translateFormula? env ({ name := name, ty := ty } :: ctx) body <;>
        simp [hTranslated] at hBody ⊢
  | ex name ty body ihBody =>
      intro h
      simp [checkFormula?, translateFormula?] at h ⊢
      have hBody := ihBody ({ name := name, ty := ty } :: ctx) h
      cases hTranslated : translateFormula? env ({ name := name, ty := ty } :: ctx) body <;>
        simp [hTranslated] at hBody ⊢

theorem checkFormula_translateFormula_isSome (env : Env) :
    forall (ctx : Ctx) (formula : Formula),
      checkFormula? env ctx formula = some () ->
        (translateFormula? env ctx formula).isSome = true := by
  intro ctx formula h
  exact checkFormula_isSome_translateFormula_isSome env ctx formula (by simp [h])

theorem checkAllFormulas_isSome_translateAllFormulas_isSome
    (env : Env) (ctx : Ctx) :
    forall (formulas : List Formula),
      (checkAllFormulas? env ctx formulas).isSome = true ->
        (translateAllFormulas? env ctx formulas).isSome = true := by
  intro formulas
  induction formulas with
  | nil =>
      intro _
      simp [translateAllFormulas?]
  | cons formula rest ih =>
      intro h
      simp [checkAllFormulas?, translateAllFormulas?] at h ⊢
      cases hFormula : checkFormula? env ctx formula <;> simp [hFormula] at h
      have hTranslatedFormula :
          (translateFormula? env ctx formula).isSome = true :=
        checkFormula_isSome_translateFormula_isSome env ctx formula (by simp [hFormula])
      cases hFormulaTranslated : translateFormula? env ctx formula <;>
        simp [hFormulaTranslated] at hTranslatedFormula ⊢
      have hTranslatedRest :
          (translateAllFormulas? env ctx rest).isSome = true :=
        ih h
      cases hRestTranslated : translateAllFormulas? env ctx rest <;>
        simp [hRestTranslated] at hTranslatedRest ⊢

theorem checkAllFormulas_translateAllFormulas_isSome
    (env : Env) (ctx : Ctx) :
    forall (formulas : List Formula),
      checkAllFormulas? env ctx formulas = some () ->
        (translateAllFormulas? env ctx formulas).isSome = true := by
  intro formulas h
  exact checkAllFormulas_isSome_translateAllFormulas_isSome env ctx formulas (by simp [h])

theorem checkSequent_isSome_translateSequentBody_isSome
    (env : Env) (seq : Sequent) :
    (checkSequent? env seq).isSome = true ->
      (translateSequentBody? env seq).isSome = true := by
  intro h
  simp [checkSequent?, translateSequentBody?] at h ⊢
  cases hAssumptions : checkAllFormulas? env seq.objectCtx seq.assumptions <;>
    simp [hAssumptions] at h
  have hTranslatedAssumptions :
      (translateAllFormulas? env seq.objectCtx seq.assumptions).isSome = true :=
    checkAllFormulas_isSome_translateAllFormulas_isSome
      env seq.objectCtx seq.assumptions (by simp [hAssumptions])
  cases hAssumptionsTranslated :
      translateAllFormulas? env seq.objectCtx seq.assumptions <;>
    simp [hAssumptionsTranslated] at hTranslatedAssumptions ⊢
  cases hConclusion : checkFormula? env seq.objectCtx seq.conclusion <;>
    simp [hConclusion] at h
  have hTranslatedConclusion :
      (translateFormula? env seq.objectCtx seq.conclusion).isSome = true :=
    checkFormula_isSome_translateFormula_isSome
      env seq.objectCtx seq.conclusion (by simp [hConclusion])
  cases hConclusionTranslated :
      translateFormula? env seq.objectCtx seq.conclusion <;>
    simp [hConclusionTranslated] at hTranslatedConclusion ⊢

theorem checkSequent_translateSequentBody_isSome (env : Env) (seq : Sequent) :
    checkSequent? env seq = some () ->
      (translateSequentBody? env seq).isSome = true := by
  intro h
  exact checkSequent_isSome_translateSequentBody_isSome env seq (by simp [h])

theorem checkSequent_translateClosedSequent_isSome (env : Env) (seq : Sequent) :
    checkSequent? env seq = some () ->
      (translateClosedSequent? env seq).isSome = true := by
  intro h
  have hBody : (translateSequentBody? env seq).isSome = true :=
    checkSequent_translateSequentBody_isSome env seq h
  simp [translateClosedSequent?]
  cases hBodyTranslated : translateSequentBody? env seq <;>
    simp [hBodyTranslated] at hBody ⊢

end ContextualHOL
