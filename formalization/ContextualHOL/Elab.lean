import ContextualHOL.Syntax

namespace ContextualHOL

def lookupName (name : Name) : List (Name × α) -> Option α
  | [] => none
  | (key, value) :: rest =>
      if key = name then
        some value
      else
        lookupName name rest

def lookupVar? (name : Name) : Ctx -> Option (Nat × Ty)
  | [] => none
  | b :: rest =>
      if b.name = name then
        some (0, b.ty)
      else
        match lookupVar? name rest with
        | none => none
        | some (idx, ty) => some (idx + 1, ty)

def lookupConst? (env : Env) (name : Name) : Option Ty :=
  lookupName name env.consts

def lookupRel? (env : Env) (name : Name) : Option RelSig :=
  lookupName name env.rels

def lookupPred? (env : Env) (name : Name) : Option Ty :=
  lookupName name env.preds

def expectTy (actual expected : Ty) : Option Unit :=
  if actual = expected then some () else none

def inferTerm? (env : Env) (ctx : Ctx) : Term -> Option Ty
  | Term.var name => do
      let (_, ty) <- lookupVar? name ctx
      pure ty
  | Term.const name => lookupConst? env name
  | Term.raw _ ty => some ty

def checkFormula? (env : Env) (ctx : Ctx) : Formula -> Option Unit
  | Formula.atom rel left right => do
      let sig <- lookupRel? env rel
      let leftTy <- inferTerm? env ctx left
      let rightTy <- inferTerm? env ctx right
      expectTy leftTy sig.left
      expectTy rightTy sig.right
  | Formula.papp pred arg => do
      let predTy <- lookupPred? env pred
      let argTy <- inferTerm? env ctx arg
      expectTy argTy predTy
  | Formula.and p q => do
      checkFormula? env ctx p
      checkFormula? env ctx q
  | Formula.or p q => do
      checkFormula? env ctx p
      checkFormula? env ctx q
  | Formula.imp p q => do
      checkFormula? env ctx p
      checkFormula? env ctx q
  | Formula.iff p q => do
      checkFormula? env ctx p
      checkFormula? env ctx q
  | Formula.not p => checkFormula? env ctx p
  | Formula.all name ty body =>
      checkFormula? env ({ name := name, ty := ty } :: ctx) body
  | Formula.ex name ty body =>
      checkFormula? env ({ name := name, ty := ty } :: ctx) body

def checkAllFormulas? (env : Env) (ctx : Ctx) : List Formula -> Option Unit
  | [] => some ()
  | formula :: rest => do
      checkFormula? env ctx formula
      checkAllFormulas? env ctx rest

def checkSequent? (env : Env) (seq : Sequent) : Option Unit := do
  checkAllFormulas? env seq.objectCtx seq.assumptions
  checkFormula? env seq.objectCtx seq.conclusion

theorem checkFormula_all (env : Env) (ctx : Ctx) (name : Name) (ty : Ty) (body : Formula) :
    checkFormula? env ctx (Formula.all name ty body) =
      checkFormula? env ({ name := name, ty := ty } :: ctx) body := rfl

theorem checkFormula_ex (env : Env) (ctx : Ctx) (name : Name) (ty : Ty) (body : Formula) :
    checkFormula? env ctx (Formula.ex name ty body) =
      checkFormula? env ({ name := name, ty := ty } :: ctx) body := rfl

end ContextualHOL
