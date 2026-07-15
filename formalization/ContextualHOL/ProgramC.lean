import ContextualHOL.Calculus

/-!
# Program C: proof-relevant contextual syntax

This module fixes the syntax and derivation-tree types that Core quotation will
target.  It deliberately coexists with the M3/PS syntax while that development
is migrated.  `TermShape` and `FormulaShape` are decidable erasures; the public
evidence judgments and `Deriv` are `Type`-valued.  In particular, a description
shape is accepted only by evidence containing a derivation of the matching
unique-existence formula.
-/

namespace ContextualHOL.ProgramC

abbrev Name := ContextualHOL.Name

inductive Ty where
  | base : Name -> Ty
  | final : Ty
  | prod : Ty -> Ty -> Ty
  | arr : Ty -> Ty -> Ty
  | prop : Ty
  deriving Repr, BEq, DecidableEq

structure Binding where
  name : Name
  ty : Ty
  deriving Repr, BEq, DecidableEq

abbrev Ctx := List Binding

structure FunSig where
  inputs : List Ty
  output : Ty
  deriving Repr, BEq, DecidableEq

structure PredSig where
  inputs : List Ty
  deriving Repr, BEq, DecidableEq

structure Signature where
  functions : List (Name × FunSig) := []
  predicates : List (Name × PredSig) := []
  deriving Repr, BEq, DecidableEq

/-! Shapes remain proof-erased so they can be compared and used as search keys.
The constructors for `theChar` and `theNeg` are not accepted terms by
themselves; acceptance is the `TermEvidence` judgment below. -/

mutual
  inductive TermShape where
    | var : Name -> TermShape
    | call : Name -> List TermShape -> TermShape
    | app : TermShape -> TermShape -> TermShape
    | theChar : Ty -> Name -> Name -> Name -> FormulaShape -> TermShape
    | theNeg : Ty -> Name -> TermShape
    deriving Repr, BEq

  inductive FormulaShape where
    | pred : Name -> List TermShape -> FormulaShape
    | and : FormulaShape -> FormulaShape -> FormulaShape
    | or : FormulaShape -> FormulaShape -> FormulaShape
    | imp : FormulaShape -> FormulaShape -> FormulaShape
    | iff : FormulaShape -> FormulaShape -> FormulaShape
    | not : FormulaShape -> FormulaShape
    | all : Name -> Ty -> FormulaShape -> FormulaShape
    | ex : Name -> Ty -> FormulaShape -> FormulaShape
    -- Exact mirrors of definite_description.cor, not arbitrary iota.
    | hasChar : Ty -> Name -> Name -> Name -> FormulaShape -> TermShape -> FormulaShape
    | existUniqueChar : Ty -> Name -> Name -> Name -> FormulaShape -> FormulaShape
    | hasCharNeg : Ty -> Name -> TermShape -> FormulaShape
    | existUniqueNeg : Ty -> Name -> FormulaShape
    deriving Repr, BEq
end

mutual
  def avoidsTerm (x : Name) (t : TermShape) : Bool :=
    match t with
    | .var _ => true
    | .call _ args => avoidsTerms x args
    | .app f a => avoidsTerm x f && avoidsTerm x a
    | .theChar _ _ w c body =>
        !(w == x) && !(c == x) && avoids x body
    | .theNeg _ _ => true
    termination_by structural t

  def avoidsTerms (x : Name) (ts : List TermShape) : Bool :=
    match ts with
    | [] => true
    | t :: rest => avoidsTerm x t && avoidsTerms x rest
    termination_by structural ts

  /-- `x` is never bound in the shape.  This is the named-binder discipline
  under which `substFormula` is capture-free. -/
  def avoids (x : Name) (p : FormulaShape) : Bool :=
    match p with
    | .pred _ args => avoidsTerms x args
    | .and p q | .or p q | .imp p q | .iff p q => avoids x p && avoids x q
    | .not p => avoids x p
    | .all y _ p | .ex y _ p => !(y == x) && avoids x p
    | .hasChar _ _ w c body subject =>
        avoidsTerm x subject && !(w == x) && !(c == x) && avoids x body
    | .existUniqueChar _ _ w c body =>
        !(w == x) && !(c == x) && avoids x body
    | .hasCharNeg _ _ subject => avoidsTerm x subject
    | .existUniqueNeg _ _ => true
    termination_by structural p
end

mutual
  def occursFreeTerm (x : Name) (t : TermShape) : Bool :=
    match t with
    | .var y => y == x
    | .call _ args => occursFreeTerms x args
    | .app f a => occursFreeTerm x f || occursFreeTerm x a
    | .theChar _ _ w c body =>
        if x == w || x == c then false else occursFree x body
    | .theNeg _ _ => false
    termination_by structural t

  def occursFreeTerms (x : Name) (ts : List TermShape) : Bool :=
    match ts with
    | [] => false
    | t :: rest => occursFreeTerm x t || occursFreeTerms x rest
    termination_by structural ts

  def occursFree (x : Name) (p : FormulaShape) : Bool :=
    match p with
    | .pred _ args => occursFreeTerms x args
    | .and p q | .or p q | .imp p q | .iff p q =>
        occursFree x p || occursFree x q
    | .not p => occursFree x p
    | .all y _ p | .ex y _ p => if y == x then false else occursFree x p
    | .hasChar _ _ w c body subject =>
        occursFreeTerm x subject ||
          (if x == w || x == c then false else occursFree x body)
    | .existUniqueChar _ _ w c body =>
        if x == w || x == c then false else occursFree x body
    | .hasCharNeg _ _ subject => occursFreeTerm x subject
    | .existUniqueNeg _ _ => false
    termination_by structural p
end

mutual
  def substTerm (x : Name) (replacement : TermShape) : TermShape -> TermShape
    | .var y => if y == x then replacement else .var y
    | .call f args => .call f (args.map (substTerm x replacement))
    | .app f a => .app (substTerm x replacement f) (substTerm x replacement a)
    | .theChar X elt w c body =>
        .theChar X elt w c
          (if x == w || x == c then body else substFormula x replacement body)
    | .theNeg X elt => .theNeg X elt

  def substFormula (x : Name) (replacement : TermShape) : FormulaShape -> FormulaShape
    | .pred p args => .pred p (args.map (substTerm x replacement))
    | .and p q => .and (substFormula x replacement p) (substFormula x replacement q)
    | .or p q => .or (substFormula x replacement p) (substFormula x replacement q)
    | .imp p q => .imp (substFormula x replacement p) (substFormula x replacement q)
    | .iff p q => .iff (substFormula x replacement p) (substFormula x replacement q)
    | .not p => .not (substFormula x replacement p)
    | .all y A p => .all y A (if y == x then p else substFormula x replacement p)
    | .ex y A p => .ex y A (if y == x then p else substFormula x replacement p)
    | .hasChar X elt w c body subject =>
        .hasChar X elt w c
          (if x == w || x == c then body else substFormula x replacement body)
          (substTerm x replacement subject)
    | .existUniqueChar X elt w c body =>
        .existUniqueChar X elt w c
          (if x == w || x == c then body else substFormula x replacement body)
    | .hasCharNeg X elt subject =>
        .hasCharNeg X elt (substTerm x replacement subject)
    | .existUniqueNeg X elt => .existUniqueNeg X elt
end

inductive VarHasType : Ctx -> Name -> Ty -> Type where
  | here {g : Ctx} {x : Name} {A : Ty} :
      VarHasType ({ name := x, ty := A } :: g) x A
  | there {g : Ctx} {b : Binding} {x : Name} {A : Ty} :
      b.name ≠ x -> VarHasType g x A -> VarHasType (b :: g) x A

/-! The four judgments below are mutually inductive.  This is the crucial
proof-relevance seam: `TermEvidence.theChar` and `.theNeg` contain `DerivRaw`
values, while `DerivRaw` conclusions are formula shapes whose accepted uses are
certified by `FormulaEvidence`. -/

mutual
  inductive TermEvidence (sig : Signature) (axioms : List FormulaShape) :
      Ctx -> List FormulaShape -> TermShape -> Ty -> Type where
    | var {x A} : VarHasType g x A -> TermEvidence sig axioms g d (.var x) A
    | call {f args argTys result} :
        (f, { inputs := argTys, output := result }) ∈ sig.functions ->
        TermsEvidence sig axioms g d args argTys ->
        TermEvidence sig axioms g d (.call f args) result
    | app {f a A B} :
        TermEvidence sig axioms g d f (.arr A B) ->
        TermEvidence sig axioms g d a A ->
        TermEvidence sig axioms g d (.app f a) B
    | theChar {X elt w c body} :
        DerivRaw sig axioms g d (.existUniqueChar X elt w c body) ->
        TermEvidence sig axioms g d (.theChar X elt w c body) X
    | theNeg {X elt} :
        DerivRaw sig axioms g d (.existUniqueNeg X elt) ->
        TermEvidence sig axioms g d (.theNeg X elt) X

  inductive TermsEvidence (sig : Signature) (axioms : List FormulaShape) :
      Ctx -> List FormulaShape -> List TermShape -> List Ty -> Type where
    | nil : TermsEvidence sig axioms g d [] []
    | cons {t ts A As} :
        TermEvidence sig axioms g d t A ->
        TermsEvidence sig axioms g d ts As ->
        TermsEvidence sig axioms g d (t :: ts) (A :: As)

  inductive FormulaEvidence (sig : Signature) (axioms : List FormulaShape) :
      Ctx -> List FormulaShape -> FormulaShape -> Type where
    | pred {p args argTys} :
        (p, { inputs := argTys }) ∈ sig.predicates ->
        TermsEvidence sig axioms g d args argTys ->
        FormulaEvidence sig axioms g d (.pred p args)
    | and {p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> FormulaEvidence sig axioms g d (.and p q)
    | or {p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> FormulaEvidence sig axioms g d (.or p q)
    | imp {p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> FormulaEvidence sig axioms g d (.imp p q)
    | iff {p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> FormulaEvidence sig axioms g d (.iff p q)
    | not {p} : FormulaEvidence sig axioms g d p -> FormulaEvidence sig axioms g d (.not p)
    | all {x A p} :
        FormulaEvidence sig axioms ({ name := x, ty := A } :: g) d p ->
        FormulaEvidence sig axioms g d (.all x A p)
    | ex {x A p} :
        FormulaEvidence sig axioms ({ name := x, ty := A } :: g) d p ->
        FormulaEvidence sig axioms g d (.ex x A p)
    | hasChar {X elt w c body subject} :
        (elt, { inputs := [X, X] }) ∈ sig.predicates ->
        FormulaEvidence sig axioms
          ({ name := w, ty := X } :: { name := c, ty := X } :: g) d body ->
        TermEvidence sig axioms g d subject X ->
        FormulaEvidence sig axioms g d (.hasChar X elt w c body subject)
    | existUniqueChar {X elt w c body} :
        (elt, { inputs := [X, X] }) ∈ sig.predicates ->
        FormulaEvidence sig axioms
          ({ name := w, ty := X } :: { name := c, ty := X } :: g) d body ->
        FormulaEvidence sig axioms g d (.existUniqueChar X elt w c body)
    | hasCharNeg {X elt subject} :
        (elt, { inputs := [X, X] }) ∈ sig.predicates ->
        TermEvidence sig axioms g d subject X ->
        FormulaEvidence sig axioms g d (.hasCharNeg X elt subject)
    | existUniqueNeg {X elt} :
        (elt, { inputs := [X, X] }) ∈ sig.predicates ->
        FormulaEvidence sig axioms g d (.existUniqueNeg X elt)

  inductive DerivRaw (sig : Signature) (axioms : List FormulaShape) :
      Ctx -> List FormulaShape -> FormulaShape -> Type where
    | hyp {g d p} : FormulaEvidence sig axioms g d p -> p ∈ d ->
        DerivRaw sig axioms g d p
    | theory {g d p} : FormulaEvidence sig axioms g d p -> p ∈ axioms ->
        DerivRaw sig axioms g d p
    | impIntro {g d p q} : FormulaEvidence sig axioms g d (.imp p q) ->
        DerivRaw sig axioms g (p :: d) q -> DerivRaw sig axioms g d (.imp p q)
    | mp {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q ->
        DerivRaw sig axioms g d (.imp p q) -> DerivRaw sig axioms g d p ->
        DerivRaw sig axioms g d q
    | axK {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q ->
        DerivRaw sig axioms g d (.imp p (.imp q p))
    | axS {g d p q r} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> FormulaEvidence sig axioms g d r ->
        DerivRaw sig axioms g d
          (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
    | axCP {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q ->
        DerivRaw sig axioms g d (.imp (.imp (.not q) (.not p)) (.imp p q))
    | axAndL {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp (.and p q) p)
    | axAndR {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp (.and p q) q)
    | axAndI {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp p (.imp q (.and p q)))
    | axOrL {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp p (.or p q))
    | axOrR {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp q (.or p q))
    | axOrE {g d p q r} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> FormulaEvidence sig axioms g d r ->
        DerivRaw sig axioms g d (.imp (.imp p r) (.imp (.imp q r) (.imp (.or p q) r)))
    | axIffI {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q ->
        DerivRaw sig axioms g d (.imp (.imp p q) (.imp (.imp q p) (.iff p q)))
    | axIffL {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp (.iff p q) (.imp p q))
    | axIffR {g d p q} : FormulaEvidence sig axioms g d p ->
        FormulaEvidence sig axioms g d q -> DerivRaw sig axioms g d (.imp (.iff p q) (.imp q p))
    | allIntro {g d x X p} : FormulaEvidence sig axioms g d (.all x X p) ->
        (forall q, q ∈ d -> occursFree x q = false) ->
        (forall q, q ∈ d -> FormulaEvidence sig axioms
          ({ name := x, ty := X } :: g) d q) ->
        DerivRaw sig axioms ({ name := x, ty := X } :: g) d p ->
        DerivRaw sig axioms g d (.all x X p)
    | allCounit {g d x X p} : FormulaEvidence sig axioms
        ({ name := x, ty := X } :: g) d (.imp (.all x X p) p) ->
        avoids x p = true ->
        DerivRaw sig axioms ({ name := x, ty := X } :: g) d (.imp (.all x X p) p)
    | exElim {g d x X p q} : FormulaEvidence sig axioms g d q ->
        (forall r, r ∈ d -> occursFree x r = false) -> occursFree x q = false ->
        FormulaEvidence sig axioms ({ name := x, ty := X } :: g) d p ->
        (forall r, r ∈ d -> FormulaEvidence sig axioms
          ({ name := x, ty := X } :: g) d r) ->
        FormulaEvidence sig axioms ({ name := x, ty := X } :: g) d q ->
        DerivRaw sig axioms g d (.ex x X p) ->
        DerivRaw sig axioms ({ name := x, ty := X } :: g) (p :: d) q ->
        DerivRaw sig axioms g d q
    | exIntro {g d x X p t} : FormulaEvidence sig axioms g d (.ex x X p) ->
        TermEvidence sig axioms g d t X ->
        avoids x p = true ->
        (forall y, t = .var y -> avoids y p = true) ->
        FormulaEvidence sig axioms ({ name := x, ty := X } :: g) d p ->
        FormulaEvidence sig axioms g d (substFormula x t p) ->
        DerivRaw sig axioms g d (substFormula x t p) ->
        DerivRaw sig axioms g d (.ex x X p)
    | ctxWeaken {g d x X p} : FormulaEvidence sig axioms
        ({ name := x, ty := X } :: g) d p -> occursFree x p = false ->
        (forall q, q ∈ d -> occursFree x q = false) ->
        FormulaEvidence sig axioms g d p ->
        (forall q, q ∈ d -> FormulaEvidence sig axioms g d q) ->
        DerivRaw sig axioms g d p ->
        DerivRaw sig axioms ({ name := x, ty := X } :: g) d p
    | ctxSubst {g d x X p t} : FormulaEvidence sig axioms g d (substFormula x t p) ->
        TermEvidence sig axioms g d t X ->
        avoids x p = true ->
        (forall y, t = .var y -> avoids y p = true) ->
        (forall q, q ∈ d -> occursFree x q = false) ->
        FormulaEvidence sig axioms ({ name := x, ty := X } :: g) d p ->
        (forall q, q ∈ d -> FormulaEvidence sig axioms
          ({ name := x, ty := X } :: g) d q) ->
        DerivRaw sig axioms ({ name := x, ty := X } :: g) d p ->
        DerivRaw sig axioms g d (substFormula x t p)
    | theSpec {g d X elt w c body}
        (helt : (elt, { inputs := [X, X] }) ∈ sig.predicates)
        (hbody : FormulaEvidence sig axioms
          ({ name := w, ty := X } :: { name := c, ty := X } :: g) d body)
        (h : DerivRaw sig axioms g d (.existUniqueChar X elt w c body)) :
        DerivRaw sig axioms g d
          (.hasChar X elt w c body (.theChar X elt w c body))
    | theNegSpec {g d X elt}
        (helt : (elt, { inputs := [X, X] }) ∈ sig.predicates)
        (h : DerivRaw sig axioms g d (.existUniqueNeg X elt)) :
        DerivRaw sig axioms g d (.hasCharNeg X elt (.theNeg X elt))
end

/-- Every derivation certifies that its conclusion is an accepted formula.
For description conclusions this reconstructs the term evidence from the
unique-existence subtree stored in the specification constructor. -/
def DerivRaw.formulaEvidence {sig : Signature} {axioms : List FormulaShape}
    {g : Ctx} {d : List FormulaShape} {p : FormulaShape}
    (h : DerivRaw sig axioms g d p) : FormulaEvidence sig axioms g d p :=
  match h with
  | .hyp hp _ => hp
  | .theory hp _ => hp
  | .impIntro hp _ => hp
  | .mp _ hq _ _ => hq
  | .axK hp hq => .imp hp (.imp hq hp)
  | .axS hp hq hr => .imp (.imp hp (.imp hq hr)) (.imp (.imp hp hq) (.imp hp hr))
  | .axCP hp hq => .imp (.imp (.not hq) (.not hp)) (.imp hp hq)
  | .axAndL hp hq => .imp (.and hp hq) hp
  | .axAndR hp hq => .imp (.and hp hq) hq
  | .axAndI hp hq => .imp hp (.imp hq (.and hp hq))
  | .axOrL hp hq => .imp hp (.or hp hq)
  | .axOrR hp hq => .imp hq (.or hp hq)
  | .axOrE hp hq hr => .imp (.imp hp hr) (.imp (.imp hq hr) (.imp (.or hp hq) hr))
  | .axIffI hp hq => .imp (.imp hp hq) (.imp (.imp hq hp) (.iff hp hq))
  | .axIffL hp hq => .imp (.iff hp hq) (.imp hp hq)
  | .axIffR hp hq => .imp (.iff hp hq) (.imp hq hp)
  | .allIntro hp _ _ _ => hp
  | .allCounit hp _ => hp
  | .exElim hq _ _ _ _ _ _ _ => hq
  | .exIntro hp _ _ _ _ _ _ => hp
  | .ctxWeaken hp _ _ _ _ _ => hp
  | .ctxSubst hp _ _ _ _ _ _ _ => hp
  | .theSpec helt hbody hu => .hasChar helt hbody (.theChar hu)
  | .theNegSpec helt hu => .hasCharNeg helt (.theNeg hu)

structure Env where
  signature : Signature
  axioms : List FormulaShape := []

abbrev TermEvidenceFor (E : Env) := TermEvidence E.signature E.axioms
abbrev FormulaEvidenceFor (E : Env) := FormulaEvidence E.signature E.axioms
abbrev Deriv (E : Env) := DerivRaw E.signature E.axioms

abbrev Proves (E : Env) (g : Ctx) (d : List FormulaShape) (p : FormulaShape) : Prop :=
  Nonempty (Deriv E g d p)

namespace Examples

def X : Ty := .base "X"
def w : Name := "w"
def c : Name := "c"
def elt : Name := "elt"
def bodyPred : Name := "body"

def sig : Signature :=
  { functions := [("f", { inputs := [X], output := X })],
    predicates :=
      [(elt, { inputs := [X, X] }), (bodyPred, { inputs := [X] })] }

def body : FormulaShape := .pred bodyPred [.var w]
def eu : FormulaShape := .existUniqueChar X elt w c body
def axioms : List FormulaShape := [eu]
def env : Env := { signature := sig, axioms := axioms }

def bodyEvidence : FormulaEvidence sig axioms
    [{ name := w, ty := X }, { name := c, ty := X }] [] body := by
  apply FormulaEvidence.pred (argTys := [X])
  · simp [sig, bodyPred, elt]
  · exact TermsEvidence.cons (TermEvidence.var VarHasType.here) TermsEvidence.nil

def euEvidence : FormulaEvidence sig axioms [] [] eu := by
  apply FormulaEvidence.existUniqueChar
  · simp [sig, elt, bodyPred]
  · exact bodyEvidence

def uniqueDeriv : Deriv env [] [] eu :=
  DerivRaw.theory euEvidence (by simp [env, axioms, eu])

/-- A description is accepted only because `uniqueDeriv` is stored here. -/
def descriptionEvidence :
    TermEvidenceFor env [] [] (.theChar X elt w c body) X :=
  TermEvidence.theChar uniqueDeriv

/-- Generic contextual counterpart of native `the_spec`. -/
def descriptionSpec : Deriv env [] []
    (.hasChar X elt w c body (.theChar X elt w c body)) := by
  apply DerivRaw.theSpec
  · simp [env, sig, elt, bodyPred]
  · exact bodyEvidence
  · exact uniqueDeriv

def functionEvidence : TermEvidenceFor env [{ name := "x", ty := X }] []
    (.call "f" [.var "x"]) X := by
  apply TermEvidence.call (argTys := [X])
  · simp [env, sig]
  · exact TermsEvidence.cons (TermEvidence.var VarHasType.here) TermsEvidence.nil

end Examples

/-! Partial erasure into the M3 syntax is intentionally explicit.  Function
application and description have no legacy image; returning `none` prevents an
accidental completeness claim while the PS development continues to compile. -/

namespace Legacy

def eraseTy? : Ty -> Option ContextualHOL.Ty
  | .base n => some (.base n)
  | .final => some .final
  | .prod A B => return .prod (← eraseTy? A) (← eraseTy? B)
  | .arr _ _ => none
  | .prop => some .prop

mutual
  def eraseTerm? : TermShape -> Option ContextualHOL.Term
    | .var x => some (.var x)
    | .call f [] => some (.const f)
    | .call _ (_ :: _) => none
    | .app _ _ => none
    | .theChar _ _ _ _ _ => none
    | .theNeg _ _ => none

  def eraseFormula? : FormulaShape -> Option ContextualHOL.Formula
    | .pred p [a] => return .papp p (← eraseTerm? a)
    | .pred r [a, b] => return .atom r (← eraseTerm? a) (← eraseTerm? b)
    | .pred _ _ => none
    | .and p q => return .and (← eraseFormula? p) (← eraseFormula? q)
    | .or p q => return .or (← eraseFormula? p) (← eraseFormula? q)
    | .imp p q => return .imp (← eraseFormula? p) (← eraseFormula? q)
    | .iff p q => return .iff (← eraseFormula? p) (← eraseFormula? q)
    | .not p => return .not (← eraseFormula? p)
    | .all x A p => return .all x (← eraseTy? A) (← eraseFormula? p)
    | .ex x A p => return .ex x (← eraseTy? A) (← eraseFormula? p)
    | .hasChar _ _ _ _ _ _ => none
    | .existUniqueChar _ _ _ _ _ => none
    | .hasCharNeg _ _ _ => none
    | .existUniqueNeg _ _ => none
end

end Legacy

end ContextualHOL.ProgramC
