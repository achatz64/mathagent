import ContextualHOL.ProvesLift
import ContextualHOL.BasisMap

namespace ContextualHOL
namespace Search

/-
The initial proof-search boundary. This module deliberately contains only
finite syntax-level operations. It does not claim that Core terms themselves
are a finite search space, and it does not yet identify formulas using
semantic equality.
-/

def Formula.isPropositional : Formula -> Bool
  | .atom _ _ _ => true
  | .papp _ _ => true
  | .and p q => isPropositional p && isPropositional q
  | .or p q => isPropositional p && isPropositional q
  | .imp p q => isPropositional p && isPropositional q
  | .iff p q => isPropositional p && isPropositional q
  | .not p => isPropositional p
  | .all _ _ _ => false
  | .ex _ _ _ => false

def Formula.subformulas : Formula -> List Formula
  | .atom n t u => [.atom n t u]
  | .papp n t => [.papp n t]
  | .and q r => .and q r :: (subformulas q ++ subformulas r)
  | .or q r => .or q r :: (subformulas q ++ subformulas r)
  | .imp q r => .imp q r :: (subformulas q ++ subformulas r)
  | .iff q r => .iff q r :: (subformulas q ++ subformulas r)
  | .not q => .not q :: subformulas q
  | .all n x q => .all n x q :: subformulas q
  | .ex n x q => .ex n x q :: subformulas q

def Sequent.formulaClosure (s : Sequent) : List Formula :=
  s.assumptions.foldr (fun a acc => Formula.subformulas a ++ acc) (Formula.subformulas s.conclusion)

def Sequent.isPropositional (s : Sequent) : Bool :=
  s.assumptions.all Formula.isPropositional && Formula.isPropositional s.conclusion

/-
These are possible backwards moves by conclusion shape. hyp is included in
every state; checking whether it closes a state is a separate, finite lookup
in the state assumptions. There is intentionally no backwards modus-ponens
action: choosing its cut formula is precisely the non-analytic Hilbert search
that PS2 replaces with focused rules.
-/
inductive LogicalAction where
  | hyp
  | impIntro
  | andIntro
  | orIntroLeft
  | orIntroRight
  | iffIntro
  deriving Repr, BEq, DecidableEq

def logicalCandidates (s : Sequent) : List LogicalAction :=
  match s.conclusion with
  | .imp _ _ => [LogicalAction.hyp, LogicalAction.impIntro]
  | .and _ _ => [LogicalAction.hyp, LogicalAction.andIntro]
  | .or _ _ => [LogicalAction.hyp, LogicalAction.orIntroLeft, LogicalAction.orIntroRight]
  | .iff _ _ => [LogicalAction.hyp, LogicalAction.iffIntro]
  | .not _ => [LogicalAction.hyp]
  | .atom _ _ _ => [LogicalAction.hyp]
  | .papp _ _ => [LogicalAction.hyp]
  | .all _ _ _ => [LogicalAction.hyp]
  | .ex _ _ _ => [LogicalAction.hyp]

structure State where
  env : Env
  sequent : Sequent
  deriving Repr, BEq, DecidableEq

def State.formulaClosure (s : State) : List Formula :=
  Sequent.formulaClosure s.sequent

def State.isPropositional (s : State) : Bool :=
  Sequent.isPropositional s.sequent

def State.candidates (s : State) : List LogicalAction :=
  logicalCandidates s.sequent

def State.proves (s : State) : Prop :=
  Proves s.env s.sequent.objectCtx s.sequent.assumptions s.sequent.conclusion

/- N3 may change the list representation of assumptions only when it
   preserves membership exactly. This is needed because contextual binder
   rules carry freshness obligations over the full assumption list. -/
theorem proves_assumption_equiv {env : Env} {gamma : Ctx}
    {delta delta0 : List Formula} {phi : Formula}
    (hiff : forall psi, List.Mem psi delta ↔ List.Mem psi delta0) :
    Proves env gamma delta phi -> Proves env gamma delta0 phi := by
  intro proof
  induction proof generalizing delta0 with
  | hyp hmem => exact Proves.hyp ((hiff _).mp hmem)
  | impIntro hp proof ih =>
      apply Proves.impIntro hp
      apply ih
      intro chi
      constructor
      · intro hmem
        cases hmem with
        | head => exact List.Mem.head _
        | tail _ htail => exact List.Mem.tail _ ((hiff _).mp htail)
      · intro hmem
        cases hmem with
        | head => exact List.Mem.head _
        | tail _ htail => exact List.Mem.tail _ ((hiff _).mpr htail)
  | mp hp first second ihFirst ihSecond =>
      exact Proves.mp hp (ihFirst hiff) (ihSecond hiff)
  | axK hp hq => exact Proves.axK hp hq
  | axS hp hq hr => exact Proves.axS hp hq hr
  | axCP hp hq => exact Proves.axCP hp hq
  | axAndL hp hq => exact Proves.axAndL hp hq
  | axAndR hp hq => exact Proves.axAndR hp hq
  | axAndI hp hq => exact Proves.axAndI hp hq
  | axOrL hp hq => exact Proves.axOrL hp hq
  | axOrR hp hq => exact Proves.axOrR hp hq
  | axOrE hp hq hr => exact Proves.axOrE hp hq hr
  | axIffI hp hq => exact Proves.axIffI hp hq
  | axIffL hp hq => exact Proves.axIffL hp hq
  | axIffR hp hq => exact Proves.axIffR hp hq
  | allIntro hfree hlift proof ih =>
      apply Proves.allIntro
      · intro psi hmem
        exact hfree psi ((hiff psi).mpr hmem)
      · intro psi hmem
        exact hlift psi ((hiff psi).mpr hmem)
      · exact ih hiff
  | allCounit hav => exact Proves.allCounit hav
  | exElim hfree hpsi hphi hdelta hgoal first second ihFirst ihSecond =>
      apply Proves.exElim
      · intro chi hmem
        exact hfree chi ((hiff chi).mpr hmem)
      · exact hpsi
      · exact hphi
      · intro chi hmem
        exact hdelta chi ((hiff chi).mpr hmem)
      · exact hgoal
      · exact ihFirst hiff
      · apply ihSecond
        intro chi
        constructor
        · intro hmem
          cases hmem with
          | head => exact List.Mem.head _
          | tail _ htail => exact List.Mem.tail _ ((hiff _).mp htail)
        · intro hmem
          cases hmem with
          | head => exact List.Mem.head _
          | tail _ htail => exact List.Mem.tail _ ((hiff _).mpr htail)
  | exIntro ht hraw hav hvar hphi hsubst proof ih =>
      exact Proves.exIntro ht hraw hav hvar hphi hsubst (ih hiff)
  | ctxWeaken hphi hdelta hliftPhi hliftDelta proof ih =>
      apply Proves.ctxWeaken
      · exact hphi
      · intro psi hmem
        exact hdelta psi ((hiff psi).mpr hmem)
      · exact hliftPhi
      · intro psi hmem
        exact hliftDelta psi ((hiff psi).mpr hmem)
      · exact ih hiff
  | ctxSubst ht hraw hav hvar hdelta hphi hdeltaLift proof ih =>
      apply Proves.ctxSubst
      · exact ht
      · exact hraw
      · exact hav
      · exact hvar
      · intro psi hmem
        exact hdelta psi ((hiff psi).mpr hmem)
      · exact hphi
      · intro psi hmem
        exact hdeltaLift psi ((hiff psi).mpr hmem)
      · exact ih hiff

/- N3 assumption representation: retain the last occurrence of each formula. -/
def assumptionContains (phi : Formula) : List Formula -> Bool
  | [] => false
  | psi :: rest => if phi = psi then true else assumptionContains phi rest

theorem assumptionContains_true (phi : Formula) :
    forall rest : List Formula, assumptionContains phi rest = true ↔ phi ∈ rest := by
  intro rest
  induction rest with
  | nil => simp [assumptionContains]
  | cons psi rest ih =>
      by_cases heq : phi = psi
      · subst psi
        simp [assumptionContains]
      · simp [assumptionContains, heq, ih]

def dedupAssumptions : List Formula -> List Formula
  | [] => []
  | phi :: rest =>
      if assumptionContains phi rest then dedupAssumptions rest
      else phi :: dedupAssumptions rest

theorem mem_dedupAssumptions (psi : Formula) :
    forall delta : List Formula,
      List.Mem psi (dedupAssumptions delta) ↔ List.Mem psi delta := by
  intro delta
  induction delta with
  | nil => simp [dedupAssumptions]
  | cons phi rest ih =>
      by_cases hmem : assumptionContains phi rest = true
      · have hphi : phi ∈ rest := (assumptionContains_true phi rest).mp hmem
        simp only [dedupAssumptions, if_pos hmem]
        constructor
        · intro h
          exact List.Mem.tail _ (ih.mp h)
        · intro h
          cases h with
          | head => exact ih.mpr hphi
          | tail _ htail => exact ih.mpr htail
      · have hphi : phi ∉ rest := by
          intro h
          exact hmem ((assumptionContains_true phi rest).mpr h)
        simp only [dedupAssumptions, if_neg hmem]
        constructor
        · intro h
          cases h with
          | head => exact List.Mem.head _
          | tail _ htail => exact List.Mem.tail _ (ih.mp htail)
        · intro h
          cases h with
          | head => exact List.Mem.head _
          | tail _ htail => exact List.Mem.tail _ (ih.mpr htail)

theorem dedupAssumptions_noDup (delta : List Formula) :
    List.Nodup (dedupAssumptions delta) := by
  induction delta with
  | nil => simp [dedupAssumptions]
  | cons phi rest ih =>
      by_cases hmem : assumptionContains phi rest = true
      · simp only [dedupAssumptions, if_pos hmem]
        exact ih
      · simp only [dedupAssumptions, if_neg hmem]
        have hnot : phi ∉ dedupAssumptions rest := by
          intro h
          apply hmem
          exact (assumptionContains_true phi rest).mpr ((mem_dedupAssumptions phi rest).mp h)
        exact List.nodup_cons.mpr ⟨hnot, ih⟩

theorem dedupAssumptions_of_noDup :
    forall delta : List Formula, List.Nodup delta -> dedupAssumptions delta = delta := by
  intro delta hnodup
  induction delta with
  | nil => rfl
  | cons phi rest ih =>
      have hnot : phi ∉ rest := List.nodup_cons.mp hnodup |>.left
      have hrest : List.Nodup rest := List.nodup_cons.mp hnodup |>.right
      have hmem : assumptionContains phi rest ≠ true := by
        intro h
        exact hnot ((assumptionContains_true phi rest).mp h)
      simp only [dedupAssumptions, if_neg hmem]
      rw [ih hrest]

theorem dedupAssumptions_idempotent (delta : List Formula) :
    dedupAssumptions (dedupAssumptions delta) = dedupAssumptions delta :=
  dedupAssumptions_of_noDup (dedupAssumptions delta) (dedupAssumptions_noDup delta)

def State.n3 (s : State) : State :=
  { env := s.env,
    sequent :=
      { objectCtx := s.sequent.objectCtx,
        assumptions := dedupAssumptions s.sequent.assumptions,
        conclusion := s.sequent.conclusion } }

theorem State.n3_proves_iff (s : State) : State.proves s ↔ State.proves s.n3 := by
  constructor
  · intro h
    apply proves_assumption_equiv (env := s.env) (gamma := s.sequent.objectCtx)
    intro psi
    exact (mem_dedupAssumptions psi s.sequent.assumptions).symm
    exact h
  · intro h
    apply proves_assumption_equiv (env := s.env) (gamma := s.sequent.objectCtx)
    intro psi
    exact mem_dedupAssumptions psi s.sequent.assumptions
    exact h

theorem State.n3_idempotent (s : State) : s.n3.n3 = s.n3 := by
  cases s
  simp [State.n3, dedupAssumptions_idempotent]

def AllProves : List State -> Prop
  | [] => True
  | s :: rest => And (State.proves s) (AllProves rest)

/- A finite imported library supplies typed backward transitions. Each entry
   carries the contextual soundness argument required to use it. -/
structure Rule where
  name : Name
  transition : State -> Option (List State)
  sound : forall (s : State) (children : List State),
    transition s = some children -> AllProves children -> State.proves s

structure RuleApplication (s : State) where
  rule : Rule
  children : List State
  applies : rule.transition s = some children

theorem RuleApplication.sound {s : State} (app : RuleApplication s) :
    AllProves app.children -> State.proves s :=
  app.rule.sound s app.children app.applies

def ruleCandidates (library : List Rule) (s : State) : List (RuleApplication s) :=
  library.foldr (fun rule acc =>
    match h : rule.transition s with
    | none => acc
    | some children => { rule := rule, children := children, applies := h } :: acc) []

theorem RuleApplication.core_replay {s : State} (app : RuleApplication s)
    (hchildren : AllProves app.children) :
    forall (cdelta : List (CPred (Ctx.obj s.sequent.objectCtx)))
      (cphi : CPred (Ctx.obj s.sequent.objectCtx)),
      LiftsAll s.env s.sequent.objectCtx s.sequent.assumptions cdelta ->
      liftFormula? s.env s.sequent.objectCtx s.sequent.conclusion = some cphi ->
      CoreThm (SeqLift (Ctx.obj s.sequent.objectCtx) (cdelta.map cl) (cl cphi)) := by
  intro cdelta cphi hdelta hphi
  exact proves_lift s.env (app.sound hchildren) cdelta cphi hdelta hphi

inductive Step : State -> LogicalAction -> List State -> Prop where
  | hyp {env gamma delta phi} (hmem : List.Mem phi delta) :
      Step { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := phi } }
        .hyp []
  | impIntro {env gamma delta p q}
      (hp : (liftFormula? env gamma p).isSome = true) :
      Step { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .imp p q } }
        .impIntro
        [{ env := env, sequent := { objectCtx := gamma, assumptions := p :: delta, conclusion := q } }]
  | andIntro {env gamma delta p q}
      (hp : (liftFormula? env gamma p).isSome = true)
      (hq : (liftFormula? env gamma q).isSome = true) :
      Step { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .and p q } }
        .andIntro
        [{ env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := p } },
         { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := q } }]
  | orIntroLeft {env gamma delta p q}
      (hp : (liftFormula? env gamma p).isSome = true)
      (hq : (liftFormula? env gamma q).isSome = true) :
      Step { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .or p q } }
        .orIntroLeft
        [{ env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := p } }]
  | orIntroRight {env gamma delta p q}
      (hp : (liftFormula? env gamma p).isSome = true)
      (hq : (liftFormula? env gamma q).isSome = true) :
      Step { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .or p q } }
        .orIntroRight
        [{ env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := q } }]
  | iffIntro {env gamma delta p q}
      (hp : (liftFormula? env gamma p).isSome = true)
      (hq : (liftFormula? env gamma q).isSome = true) :
      Step { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .iff p q } }
        .iffIntro
        [{ env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .imp p q } },
         { env := env, sequent := { objectCtx := gamma, assumptions := delta, conclusion := .imp q p } }]

theorem step_sound {s : State} {a : LogicalAction} {children : List State}
    (hstep : Step s a children) :
    AllProves children -> State.proves s := by
  intro hchildren
  cases hstep with
  | hyp hmem =>
      exact Proves.hyp hmem
  | impIntro hp =>
      exact Proves.impIntro hp (by
        simpa [AllProves, State.proves] using hchildren)
  | andIntro hp hq =>
      simp [AllProves, State.proves] at hchildren
      exact Proves.mp hq
        (Proves.mp hp (Proves.axAndI hp hq) hchildren.left) hchildren.right
  | orIntroLeft hp hq =>
      simp [AllProves, State.proves] at hchildren
      exact Proves.mp hp (Proves.axOrL hp hq) hchildren
  | orIntroRight hp hq =>
      simp [AllProves, State.proves] at hchildren
      exact Proves.mp hq (Proves.axOrR hp hq) hchildren
  | iffIntro hp hq =>
      simp [AllProves, State.proves] at hchildren
      exact Proves.mp (by simp [liftFormula?_imp_isSome, hp, hq])
        (Proves.mp (by simp [liftFormula?_imp_isSome, hp, hq])
          (Proves.axIffI hp hq) hchildren.left) hchildren.right

theorem step_core_replay {s : State} {a : LogicalAction} {children : List State}
    (hstep : Step s a children) (hchildren : AllProves children) :
    forall (cdelta : List (CPred (Ctx.obj s.sequent.objectCtx)))
      (cphi : CPred (Ctx.obj s.sequent.objectCtx)),
      LiftsAll s.env s.sequent.objectCtx s.sequent.assumptions cdelta ->
      liftFormula? s.env s.sequent.objectCtx s.sequent.conclusion = some cphi ->
      CoreThm (SeqLift (Ctx.obj s.sequent.objectCtx) (cdelta.map cl) (cl cphi)) := by
  intro cdelta cphi hdelta hphi
  exact proves_lift s.env (step_sound hstep hchildren) cdelta cphi hdelta hphi

/- The logical core is also exposed through the generic finite library.
   A transition is present only when its liftability side conditions have
   been decided successfully. -/
def logicalTransition? : LogicalAction -> State -> Option (List State)
  | .hyp, s =>
      if assumptionContains s.sequent.conclusion s.sequent.assumptions = true then some [] else none
  | .impIntro, s =>
      match s.sequent.conclusion with
      | .imp p q =>
          if (liftFormula? s.env s.sequent.objectCtx p).isSome = true then
            some [State.mk s.env (Sequent.mk s.sequent.objectCtx
              (p :: s.sequent.assumptions) q)]
          else none
      | _ => none
  | .andIntro, s =>
      match s.sequent.conclusion with
      | .and p q =>
          if (liftFormula? s.env s.sequent.objectCtx p).isSome = true then
            if (liftFormula? s.env s.sequent.objectCtx q).isSome = true then
              some [State.mk s.env (Sequent.mk s.sequent.objectCtx s.sequent.assumptions p),
                State.mk s.env (Sequent.mk s.sequent.objectCtx s.sequent.assumptions q)]
            else none
          else none
      | _ => none
  | .orIntroLeft, s =>
      match s.sequent.conclusion with
      | .or p q =>
          if (liftFormula? s.env s.sequent.objectCtx p).isSome = true then
            if (liftFormula? s.env s.sequent.objectCtx q).isSome = true then
              some [State.mk s.env (Sequent.mk s.sequent.objectCtx s.sequent.assumptions p)]
            else none
          else none
      | _ => none
  | .orIntroRight, s =>
      match s.sequent.conclusion with
      | .or p q =>
          if (liftFormula? s.env s.sequent.objectCtx p).isSome = true then
            if (liftFormula? s.env s.sequent.objectCtx q).isSome = true then
              some [State.mk s.env (Sequent.mk s.sequent.objectCtx s.sequent.assumptions q)]
            else none
          else none
      | _ => none
  | .iffIntro, s =>
      match s.sequent.conclusion with
      | .iff p q =>
          if (liftFormula? s.env s.sequent.objectCtx p).isSome = true then
            if (liftFormula? s.env s.sequent.objectCtx q).isSome = true then
              some [State.mk s.env (Sequent.mk s.sequent.objectCtx s.sequent.assumptions (.imp p q)),
                State.mk s.env (Sequent.mk s.sequent.objectCtx s.sequent.assumptions (.imp q p))]
            else none
          else none
      | _ => none

theorem logicalTransition?_step (s : State) (action : LogicalAction)
    {children : List State} (h : logicalTransition? action s = some children) :
    Step s action children := by
  cases s with
  | mk env sequent =>
    cases sequent with
    | mk gamma delta conclusion =>
      cases action with
      | hyp =>
          simp [logicalTransition?] at h
          have hmem := h.1
          have hchildren := h.2
          subst children
          exact Step.hyp ((assumptionContains_true _ _).mp hmem)
      | impIntro =>
          cases conclusion <;> simp [logicalTransition?] at h
          have hp := h.1
          have hchildren := h.2
          subst children
          exact Step.impIntro hp
      | andIntro =>
          cases conclusion <;> simp [logicalTransition?] at h
          have hp := h.1
          have hq := h.2.1
          have hchildren := h.2.2
          subst children
          exact Step.andIntro hp hq
      | orIntroLeft =>
          cases conclusion <;> simp [logicalTransition?] at h
          have hp := h.1
          have hq := h.2.1
          have hchildren := h.2.2
          subst children
          exact Step.orIntroLeft hp hq
      | orIntroRight =>
          cases conclusion <;> simp [logicalTransition?] at h
          have hp := h.1
          have hq := h.2.1
          have hchildren := h.2.2
          subst children
          exact Step.orIntroRight hp hq
      | iffIntro =>
          cases conclusion <;> simp [logicalTransition?] at h
          have hp := h.1
          have hq := h.2.1
          have hchildren := h.2.2
          subst children
          exact Step.iffIntro hp hq

def logicalRule (action : LogicalAction) : Rule where
  name := reprStr action
  transition := logicalTransition? action
  sound := fun s _children htransition hchildren =>
    step_sound (logicalTransition?_step s action htransition) hchildren

def LogicalAction.all : List LogicalAction :=
  [.hyp, .impIntro, .andIntro, .orIntroLeft, .orIntroRight, .iffIntro]

theorem LogicalAction.mem_all (action : LogicalAction) : action ∈ LogicalAction.all := by
  cases action <;> simp [LogicalAction.all]

def logicalLibrary : List Rule :=
  LogicalAction.all.map logicalRule

def State.ruleCandidates (s : State) : List (RuleApplication s) :=
  ContextualHOL.Search.ruleCandidates logicalLibrary s

inductive N2Rule where
  | unaryReindex
  | andReindex
  | orReindex
  | impReindex
  | iffReindex
  | notReindex
  deriving Repr, BEq, DecidableEq

def N2Rule.basisName : N2Rule -> BasisName
  | .unaryReindex => .forallUnaryReindexBeta
  | .andReindex => .forallAndReindexBeta
  | .orReindex => .forallOrReindexBeta
  | .impReindex => .forallImpReindexBeta
  | .iffReindex => .forallIffReindexBeta
  | .notReindex => .forallNotReindexBeta

structure N2Edge (i : Ty) where
  lhs : CPred (Ty.prod i Ty.final)
  rhs : CPred (Ty.prod i Ty.final)
  rule : N2Rule
  certificate : CoreThm (Vy i (CPred.iff lhs rhs))

theorem N2Edge.replay {i : Ty} (edge : N2Edge i) :
    CoreThm (Vy i (CPred.iff edge.lhs edge.rhs)) := edge.certificate

def N2Edge.unaryReindex (i z a : Ty) (p : CPred a)
    (u : CMap z a) (s : CMap (Ty.prod i Ty.final) z) : N2Edge i where
  lhs := CPred.comp (CPred.comp p u) s
  rhs := CPred.comp p (CMap.comp u s)
  rule := .unaryReindex
  certificate := CoreThm.forallUnaryReindexBeta i z a p u s

def N2Edge.andReindex (i y : Ty) (s : CMap (Ty.prod i Ty.final) y)
    (p q : CPred y) : N2Edge i where
  lhs := CPred.comp (CPred.and p q) s
  rhs := CPred.and (CPred.comp p s) (CPred.comp q s)
  rule := .andReindex
  certificate := CoreThm.forallAndReindexBeta i y s p q

def N2Edge.orReindex (i y : Ty) (s : CMap (Ty.prod i Ty.final) y)
    (p q : CPred y) : N2Edge i where
  lhs := CPred.comp (CPred.or p q) s
  rhs := CPred.or (CPred.comp p s) (CPred.comp q s)
  rule := .orReindex
  certificate := CoreThm.forallOrReindexBeta i y s p q

def N2Edge.impReindex (i y : Ty) (s : CMap (Ty.prod i Ty.final) y)
    (p q : CPred y) : N2Edge i where
  lhs := CPred.comp (CPred.imp p q) s
  rhs := CPred.imp (CPred.comp p s) (CPred.comp q s)
  rule := .impReindex
  certificate := CoreThm.forallImpReindexBeta i y s p q

def N2Edge.iffReindex (i y : Ty) (s : CMap (Ty.prod i Ty.final) y)
    (p q : CPred y) : N2Edge i where
  lhs := CPred.comp (CPred.iff p q) s
  rhs := CPred.iff (CPred.comp p s) (CPred.comp q s)
  rule := .iffReindex
  certificate := CoreThm.forallIffReindexBeta i y s p q

def N2Edge.notReindex (i y : Ty) (s : CMap (Ty.prod i Ty.final) y)
    (p : CPred y) : N2Edge i where
  lhs := CPred.comp (CPred.not p) s
  rhs := CPred.not (CPred.comp p s)
  rule := .notReindex
  certificate := CoreThm.forallNotReindexBeta i y s p

/- The executable root matcher recognizes the six initial N2 left-hand sides.
   It returns only their forward orientation. Quantifier heads are excluded:
   moving reindexing through a binder is the later Beck-Chevalley problem. -/
def n2RootStep? {i : Ty} : CPred (Ty.prod i Ty.final) -> Option (N2Edge i)
  | .comp (.comp p u) s => some (N2Edge.unaryReindex i _ _ p u s)
  | .comp (.and p q) s => some (N2Edge.andReindex i _ s p q)
  | .comp (.or p q) s => some (N2Edge.orReindex i _ s p q)
  | .comp (.imp p q) s => some (N2Edge.impReindex i _ s p q)
  | .comp (.iff p q) s => some (N2Edge.iffReindex i _ s p q)
  | .comp (.not p) s => some (N2Edge.notReindex i _ s p)
  | _ => none

theorem n2RootStep?_replay {i : Ty} {p : CPred (Ty.prod i Ty.final)}
    {edge : N2Edge i} (_ : n2RootStep? p = some edge) :
    CoreThm (Vy i (CPred.iff edge.lhs edge.rhs)) := edge.certificate

inductive N2Path (i : Ty) :
    CPred (Ty.prod i Ty.final) -> CPred (Ty.prod i Ty.final) -> Prop where
  | refl (p : CPred (Ty.prod i Ty.final)) : N2Path i p p
  | edge (edge : N2Edge i) : N2Path i edge.lhs edge.rhs
  | trans {p q r : CPred (Ty.prod i Ty.final)} :
      N2Path i p q -> N2Path i q r -> N2Path i p r
  | andCong {p0 p1 q0 q1 : CPred (Ty.prod i Ty.final)} :
      N2Path i p0 p1 -> N2Path i q0 q1 -> N2Path i (CPred.and p0 q0) (CPred.and p1 q1)
  | orCong {p0 p1 q0 q1 : CPred (Ty.prod i Ty.final)} :
      N2Path i p0 p1 -> N2Path i q0 q1 -> N2Path i (CPred.or p0 q0) (CPred.or p1 q1)
  | impCong {p0 p1 q0 q1 : CPred (Ty.prod i Ty.final)} :
      N2Path i p0 p1 -> N2Path i q0 q1 -> N2Path i (CPred.imp p0 q0) (CPred.imp p1 q1)
  | iffCong {p0 p1 q0 q1 : CPred (Ty.prod i Ty.final)} :
      N2Path i p0 p1 -> N2Path i q0 q1 -> N2Path i (CPred.iff p0 q0) (CPred.iff p1 q1)
  | notCong {p0 p1 : CPred (Ty.prod i Ty.final)} :
      N2Path i p0 p1 -> N2Path i (CPred.not p0) (CPred.not p1)

theorem N2Path.replay {i : Ty} {p q : CPred (Ty.prod i Ty.final)}
    (path : N2Path i p q) : CoreThm (Vy i (CPred.iff p q)) := by
  induction path with
  | refl p => exact CoreThm.forallIffRefl i p
  | edge edge => exact edge.certificate
  | trans first second ihFirst ihSecond =>
      exact CoreThm.forallIffTransApply i _ _ _ ihFirst ihSecond
  | andCong first second ihFirst ihSecond =>
      exact CoreThm.mp (CoreThm.mp (CoreThm.forallAndCong i _ _ _ _) ihFirst) ihSecond
  | orCong first second ihFirst ihSecond =>
      exact CoreThm.mp (CoreThm.mp (CoreThm.forallOrCong i _ _ _ _) ihFirst) ihSecond
  | impCong first second ihFirst ihSecond =>
      exact CoreThm.mp (CoreThm.mp (CoreThm.forallImpCong i _ _ _ _) ihFirst) ihSecond
  | iffCong first second ihFirst ihSecond =>
      exact CoreThm.mp (CoreThm.mp (CoreThm.forallIffCong i _ _ _ _) ihFirst) ihSecond
  | notCong first ihFirst =>
      exact CoreThm.mp (CoreThm.forallNotCong i _ _) ihFirst

/- The N2 size counts only constructors through which this first pass
   descends. Quantifier bodies are opaque in the present domain. -/
def CPred.n2Size {ctx : Ty} : CPred ctx -> Nat
  | .raw _ _ => 0
  | .and p q => 1 + n2Size p + n2Size q
  | .or p q => 1 + n2Size p + n2Size q
  | .imp p q => 1 + n2Size p + n2Size q
  | .iff p q => 1 + n2Size p + n2Size q
  | .not p => 1 + n2Size p
  | .all _ _ => 0
  | .ex _ _ => 0
  | .comp p _ => 1 + n2Size p

def CPred.isN2Normal {ctx : Ty} : CPred ctx -> Bool
  | .raw _ _ => true
  | .and p q => isN2Normal p && isN2Normal q
  | .or p q => isN2Normal p && isN2Normal q
  | .imp p q => isN2Normal p && isN2Normal q
  | .iff p q => isN2Normal p && isN2Normal q
  | .not p => isN2Normal p
  | .all _ _ => true
  | .ex _ _ => true
  | .comp (.raw _ _) _ => true
  | .comp (.all _ _) _ => true
  | .comp (.ex _ _) _ => true
  | .comp _ _ => false

structure N2Result (i : Ty) (p : CPred (Ty.prod i Ty.final)) where
  rhs : CPred (Ty.prod i Ty.final)
  trace : N2Path i p rhs

/- A bounded structural N2 pass. Fuel bounds rewrite depth; every returned
   result carries a trace that replays through the checked Core basis. -/
def n2NormalizeFuel (i : Ty) :
    (fuel : Nat) -> (p : CPred (Ty.prod i Ty.final)) -> N2Result i p
  | 0, p => { rhs := p, trace := N2Path.refl p }
  | _ + 1, .raw n (Ty.prod i Ty.final) =>
      { rhs := .raw n (Ty.prod i Ty.final),
        trace := N2Path.refl (.raw n (Ty.prod i Ty.final)) }
  | fuel + 1, .and p q =>
      let hp := n2NormalizeFuel i fuel p
      let hq := n2NormalizeFuel i fuel q
      { rhs := .and hp.rhs hq.rhs, trace := N2Path.andCong hp.trace hq.trace }
  | fuel + 1, .or p q =>
      let hp := n2NormalizeFuel i fuel p
      let hq := n2NormalizeFuel i fuel q
      { rhs := .or hp.rhs hq.rhs, trace := N2Path.orCong hp.trace hq.trace }
  | fuel + 1, .imp p q =>
      let hp := n2NormalizeFuel i fuel p
      let hq := n2NormalizeFuel i fuel q
      { rhs := .imp hp.rhs hq.rhs, trace := N2Path.impCong hp.trace hq.trace }
  | fuel + 1, .iff p q =>
      let hp := n2NormalizeFuel i fuel p
      let hq := n2NormalizeFuel i fuel q
      { rhs := .iff hp.rhs hq.rhs, trace := N2Path.iffCong hp.trace hq.trace }
  | fuel + 1, .not p =>
      let hp := n2NormalizeFuel i fuel p
      { rhs := .not hp.rhs, trace := N2Path.notCong hp.trace }
  | _ + 1, .all x p =>
      { rhs := .all x p, trace := N2Path.refl (.all x p) }
  | _ + 1, .ex x p =>
      { rhs := .ex x p, trace := N2Path.refl (.ex x p) }
  | _ + 1, .comp (.raw n ctx) s =>
      { rhs := .comp (.raw n ctx) s, trace := N2Path.refl (.comp (.raw n ctx) s) }
  | fuel + 1, .comp (.comp p u) s =>
      let h := n2NormalizeFuel i fuel (CPred.comp p (CMap.comp u s))
      { rhs := h.rhs,
        trace := N2Path.trans (N2Path.edge (N2Edge.unaryReindex i _ _ p u s)) h.trace }
  | fuel + 1, .comp (.and p q) s =>
      let hp := n2NormalizeFuel i fuel (CPred.comp p s)
      let hq := n2NormalizeFuel i fuel (CPred.comp q s)
      { rhs := .and hp.rhs hq.rhs,
        trace := N2Path.trans (N2Path.edge (N2Edge.andReindex i _ s p q))
          (N2Path.andCong hp.trace hq.trace) }
  | fuel + 1, .comp (.or p q) s =>
      let hp := n2NormalizeFuel i fuel (CPred.comp p s)
      let hq := n2NormalizeFuel i fuel (CPred.comp q s)
      { rhs := .or hp.rhs hq.rhs,
        trace := N2Path.trans (N2Path.edge (N2Edge.orReindex i _ s p q))
          (N2Path.orCong hp.trace hq.trace) }
  | fuel + 1, .comp (.imp p q) s =>
      let hp := n2NormalizeFuel i fuel (CPred.comp p s)
      let hq := n2NormalizeFuel i fuel (CPred.comp q s)
      { rhs := .imp hp.rhs hq.rhs,
        trace := N2Path.trans (N2Path.edge (N2Edge.impReindex i _ s p q))
          (N2Path.impCong hp.trace hq.trace) }
  | fuel + 1, .comp (.iff p q) s =>
      let hp := n2NormalizeFuel i fuel (CPred.comp p s)
      let hq := n2NormalizeFuel i fuel (CPred.comp q s)
      { rhs := .iff hp.rhs hq.rhs,
        trace := N2Path.trans (N2Path.edge (N2Edge.iffReindex i _ s p q))
          (N2Path.iffCong hp.trace hq.trace) }
  | fuel + 1, .comp (.not p) s =>
      let hp := n2NormalizeFuel i fuel (CPred.comp p s)
      { rhs := .not hp.rhs,
        trace := N2Path.trans (N2Path.edge (N2Edge.notReindex i _ s p))
          (N2Path.notCong hp.trace) }
  | _ + 1, .comp (.all x p) s =>
      { rhs := .comp (.all x p) s, trace := N2Path.refl (.comp (.all x p) s) }
  | _ + 1, .comp (.ex x p) s =>
      { rhs := .comp (.ex x p) s, trace := N2Path.refl (.comp (.ex x p) s) }

theorem n2NormalizeFuel_replay (i : Ty) (fuel : Nat)
    (p : CPred (Ty.prod i Ty.final)) :
    CoreThm (Vy i (CPred.iff p (n2NormalizeFuel i fuel p).rhs)) :=
  (n2NormalizeFuel i fuel p).trace.replay

def n2Normalize (i : Ty) (p : CPred (Ty.prod i Ty.final)) : N2Result i p :=
  n2NormalizeFuel i (CPred.n2Size p) p

theorem n2Normalize_replay (i : Ty) (p : CPred (Ty.prod i Ty.final)) :
    CoreThm (Vy i (CPred.iff p (n2Normalize i p).rhs)) :=
  n2NormalizeFuel_replay i (CPred.n2Size p) p

theorem n2NormalizeFuel_normal (i : Ty) :
    forall (fuel : Nat) (p : CPred (Ty.prod i Ty.final)),
      CPred.n2Size p <= fuel ->
        CPred.isN2Normal (n2NormalizeFuel i fuel p).rhs = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro p h
      cases p with
      | raw n ctx => simp [n2NormalizeFuel, CPred.isN2Normal]
      | and p q => simp [CPred.n2Size] at h
      | or p q => simp [CPred.n2Size] at h
      | imp p q => simp [CPred.n2Size] at h
      | iff p q => simp [CPred.n2Size] at h
      | not p => simp [CPred.n2Size] at h
      | all x p => simp [n2NormalizeFuel, CPred.isN2Normal]
      | ex x p => simp [n2NormalizeFuel, CPred.isN2Normal]
      | comp p s => simp [CPred.n2Size] at h
  | succ fuel ih =>
      intro p h
      cases p with
      | raw n ctx => simp [n2NormalizeFuel, CPred.isN2Normal]
      | and p q =>
          have hpSize : CPred.n2Size p <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hqSize : CPred.n2Size q <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hp := ih p hpSize
          have hq := ih q hqSize
          simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
      | or p q =>
          have hpSize : CPred.n2Size p <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hqSize : CPred.n2Size q <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hp := ih p hpSize
          have hq := ih q hqSize
          simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
      | imp p q =>
          have hpSize : CPred.n2Size p <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hqSize : CPred.n2Size q <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hp := ih p hpSize
          have hq := ih q hqSize
          simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
      | iff p q =>
          have hpSize : CPred.n2Size p <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hqSize : CPred.n2Size q <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hp := ih p hpSize
          have hq := ih q hqSize
          simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
      | not p =>
          have hpSize : CPred.n2Size p <= fuel := by
            simp only [CPred.n2Size] at h ⊢; omega
          have hp := ih p hpSize
          simp [n2NormalizeFuel, CPred.isN2Normal, hp]
      | all x p => simp [n2NormalizeFuel, CPred.isN2Normal]
      | ex x p => simp [n2NormalizeFuel, CPred.isN2Normal]
      | comp r s =>
          cases r with
          | raw n ctx => simp [n2NormalizeFuel, CPred.isN2Normal]
          | and p q =>
              have hpSize : CPred.n2Size (CPred.comp p s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hqSize : CPred.n2Size (CPred.comp q s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hp := ih (CPred.comp p s) hpSize
              have hq := ih (CPred.comp q s) hqSize
              simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
          | or p q =>
              have hpSize : CPred.n2Size (CPred.comp p s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hqSize : CPred.n2Size (CPred.comp q s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hp := ih (CPred.comp p s) hpSize
              have hq := ih (CPred.comp q s) hqSize
              simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
          | imp p q =>
              have hpSize : CPred.n2Size (CPred.comp p s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hqSize : CPred.n2Size (CPred.comp q s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hp := ih (CPred.comp p s) hpSize
              have hq := ih (CPred.comp q s) hqSize
              simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
          | iff p q =>
              have hpSize : CPred.n2Size (CPred.comp p s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hqSize : CPred.n2Size (CPred.comp q s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hp := ih (CPred.comp p s) hpSize
              have hq := ih (CPred.comp q s) hqSize
              simp [n2NormalizeFuel, CPred.isN2Normal, hp, hq]
          | not p =>
              have hpSize : CPred.n2Size (CPred.comp p s) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              have hp := ih (CPred.comp p s) hpSize
              simp [n2NormalizeFuel, CPred.isN2Normal, hp]
          | all x p => simp [n2NormalizeFuel, CPred.isN2Normal]
          | ex x p => simp [n2NormalizeFuel, CPred.isN2Normal]
          | comp p u =>
              have hpSize : CPred.n2Size (CPred.comp p (CMap.comp u s)) <= fuel := by
                simp only [CPred.n2Size] at h ⊢; omega
              simpa [n2NormalizeFuel] using ih (CPred.comp p (CMap.comp u s)) hpSize

theorem n2Normalize_normal (i : Ty) (p : CPred (Ty.prod i Ty.final)) :
    CPred.isN2Normal (n2Normalize i p).rhs = true :=
  n2NormalizeFuel_normal i (CPred.n2Size p) p (Nat.le_refl _)

theorem n2NormalizeFuel_fixed (i : Ty) :
    forall (fuel : Nat) (p : CPred (Ty.prod i Ty.final)),
      CPred.isN2Normal p = true ->
        (n2NormalizeFuel i fuel p).rhs = p := by
  intro fuel
  induction fuel with
  | zero =>
      intro p h
      rfl
  | succ fuel ih =>
      intro p h
      cases p with
      | raw n ctx => rfl
      | and p q =>
          simp [CPred.isN2Normal] at h
          simp [n2NormalizeFuel, ih p h.left, ih q h.right]
      | or p q =>
          simp [CPred.isN2Normal] at h
          simp [n2NormalizeFuel, ih p h.left, ih q h.right]
      | imp p q =>
          simp [CPred.isN2Normal] at h
          simp [n2NormalizeFuel, ih p h.left, ih q h.right]
      | iff p q =>
          simp [CPred.isN2Normal] at h
          simp [n2NormalizeFuel, ih p h.left, ih q h.right]
      | not p =>
          simp [CPred.isN2Normal] at h
          simp [n2NormalizeFuel, ih p h]
      | all x p => rfl
      | ex x p => rfl
      | comp r s =>
          cases r with
          | raw n ctx => rfl
          | and p q => simp [CPred.isN2Normal] at h
          | or p q => simp [CPred.isN2Normal] at h
          | imp p q => simp [CPred.isN2Normal] at h
          | iff p q => simp [CPred.isN2Normal] at h
          | not p => simp [CPred.isN2Normal] at h
          | all x p => rfl
          | ex x p => rfl
          | comp p u => simp [CPred.isN2Normal] at h

theorem n2Normalize_idempotent (i : Ty) (p : CPred (Ty.prod i Ty.final)) :
    (n2Normalize i (n2Normalize i p).rhs).rhs = (n2Normalize i p).rhs :=
  n2NormalizeFuel_fixed i (CPred.n2Size (n2Normalize i p).rhs)
    (n2Normalize i p).rhs (n2Normalize_normal i p)

end Search
end ContextualHOL
