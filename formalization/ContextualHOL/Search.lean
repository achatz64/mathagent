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

end Search
end ContextualHOL
