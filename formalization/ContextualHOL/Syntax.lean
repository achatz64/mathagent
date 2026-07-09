namespace ContextualHOL

abbrev Name := String

inductive Ty where
  | base : Name -> Ty
  | final : Ty
  | prod : Ty -> Ty -> Ty
  | prop : Ty
  deriving Repr, BEq, DecidableEq

structure Binding where
  name : Name
  ty : Ty
  deriving Repr, BEq, DecidableEq

abbrev Ctx := List Binding

namespace Ctx

def obj : Ctx -> Ty
  | [] => Ty.final
  | b :: rest => Ty.prod b.ty (obj rest)

theorem obj_nil : obj [] = Ty.final := rfl

theorem obj_cons (b : Binding) (ctx : Ctx) :
    obj (b :: ctx) = Ty.prod b.ty (obj ctx) := rfl

end Ctx

inductive Term where
  | var : Name -> Term
  | const : Name -> Term
  | raw : Name -> Ty -> Term
  deriving Repr, BEq, DecidableEq

inductive Formula where
  | atom : Name -> Term -> Term -> Formula
  | papp : Name -> Term -> Formula
  | and : Formula -> Formula -> Formula
  | or : Formula -> Formula -> Formula
  | imp : Formula -> Formula -> Formula
  | iff : Formula -> Formula -> Formula
  | not : Formula -> Formula
  | all : Name -> Ty -> Formula -> Formula
  | ex : Name -> Ty -> Formula -> Formula
  deriving Repr, BEq, DecidableEq

structure RelSig where
  left : Ty
  right : Ty
  deriving Repr, BEq, DecidableEq

structure Env where
  consts : List (Name × Ty) := []
  rels : List (Name × RelSig) := []
  preds : List (Name × Ty) := []
  deriving Repr, BEq, DecidableEq

structure Sequent where
  objectCtx : Ctx
  assumptions : List Formula
  conclusion : Formula
  deriving Repr, BEq, DecidableEq

end ContextualHOL
