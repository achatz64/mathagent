import ContextualHOL.ProvesLift

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

def AllProves : List State -> Prop
  | [] => True
  | s :: rest => And (State.proves s) (AllProves rest)

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

end Search
end ContextualHOL
