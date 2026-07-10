import ContextualHOL.Syntax

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
  | notIntro
  deriving Repr, BEq, DecidableEq

def logicalCandidates (s : Sequent) : List LogicalAction :=
  match s.conclusion with
  | .imp _ _ => [LogicalAction.hyp, LogicalAction.impIntro]
  | .and _ _ => [LogicalAction.hyp, LogicalAction.andIntro]
  | .or _ _ => [LogicalAction.hyp, LogicalAction.orIntroLeft, LogicalAction.orIntroRight]
  | .iff _ _ => [LogicalAction.hyp, LogicalAction.iffIntro]
  | .not _ => [LogicalAction.hyp, LogicalAction.notIntro]
  | .atom _ _ _ => [LogicalAction.hyp]
  | .papp _ _ => [LogicalAction.hyp]
  | .all _ _ _ => [LogicalAction.hyp]
  | .ex _ _ _ => [LogicalAction.hyp]

structure State where
  sequent : Sequent
  deriving Repr, BEq, DecidableEq

def State.formulaClosure (s : State) : List Formula :=
  Sequent.formulaClosure s.sequent

def State.isPropositional (s : State) : Bool :=
  Sequent.isPropositional s.sequent

def State.candidates (s : State) : List LogicalAction :=
  logicalCandidates s.sequent

end Search
end ContextualHOL
