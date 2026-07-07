import Std

namespace CoreChecker

abbrev Name := String

inductive Expr where
  | ident : Name -> Expr
  | hole : Expr
  | sortType : Expr
  | sortProp : Expr
  | arrow : Expr -> Expr -> Expr
  | prod : Expr -> Expr -> Expr
  | app : Expr -> Expr -> Expr
  | comp : Expr -> Expr -> Expr
deriving Repr, BEq, Inhabited

structure Param where
  name : Name
  type : Expr
deriving Repr, Inhabited

inductive DeclKind where
  | axiom | defn | abbrev
deriving Repr, BEq, Inhabited

structure Decl where
  name : Name
  kind : DeclKind
  params : Array Param
  type : Expr
  body : Option Expr
deriving Repr, Inhabited

inductive Command where
  | importCmd : Name -> Command
  | openCmd : Name -> Command
  | namespaceCmd : Name -> Command
  | endCmd : Option Name -> Command
  | checkCmd : Expr -> Command
  | declCmd : Decl -> Command
deriving Repr, Inhabited

structure Diagnostic where
  file : String
  line : Nat
  message : String
deriving Repr, Inhabited

def Expr.toCoreString : Expr -> String
  | .ident n => n
  | .hole => "_"
  | .sortType => "Type"
  | .sortProp => "Prop"
  | .arrow a b => "(" ++ a.toCoreString ++ " -> " ++ b.toCoreString ++ ")"
  | .prod a b => "(" ++ a.toCoreString ++ " x " ++ b.toCoreString ++ ")"
  | .app f a => "(" ++ f.toCoreString ++ " " ++ a.toCoreString ++ ")"
  | .comp f g => "(" ++ f.toCoreString ++ " o " ++ g.toCoreString ++ ")"

def Expr.appMany (f : Expr) (args : Array Expr) : Expr :=
  args.foldl Expr.app f

partial def Expr.headArgs : Expr -> Expr × Array Expr
  | .app f a =>
      let (h, args) := f.headArgs
      (h, args.push a)
  | e => (e, #[])

partial def Expr.subst (e : Expr) (x : Name) (v : Expr) : Expr :=
  match e with
  | .ident n => if n == x then v else .ident n
  | .hole => .hole
  | .sortType => .sortType
  | .sortProp => .sortProp
  | .arrow a b => .arrow (a.subst x v) (b.subst x v)
  | .prod a b => .prod (a.subst x v) (b.subst x v)
  | .app f a => .app (f.subst x v) (a.subst x v)
  | .comp f g => .comp (f.subst x v) (g.subst x v)

partial def Expr.substMany (e : Expr) (pairs : Array (Name × Expr)) : Expr :=
  match e with
  | .ident n =>
      match pairs.find? (fun p => p.1 == n) with
      | some p => p.2
      | none => .ident n
  | .hole => .hole
  | .sortType => .sortType
  | .sortProp => .sortProp
  | .arrow a b => .arrow (a.substMany pairs) (b.substMany pairs)
  | .prod a b => .prod (a.substMany pairs) (b.substMany pairs)
  | .app f a => .app (f.substMany pairs) (a.substMany pairs)
  | .comp f g => .comp (f.substMany pairs) (g.substMany pairs)

def isTypeSort : Expr -> Bool
  | .sortType => true
  | .sortProp => true
  | _ => false

end CoreChecker
