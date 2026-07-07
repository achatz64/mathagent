import CoreChecker.Parser

namespace CoreChecker

structure Env where
  decls : Std.HashMap Name Decl := {}
  opens : Array Name := #[]
  nsStack : Array Name := #[]
deriving Inhabited

abbrev CheckM := Except String

def currentPrefix (env : Env) : String :=
  ".".intercalate env.nsStack.toList

def qualify (env : Env) (n : Name) : Name :=
  let p := currentPrefix env
  if p.isEmpty then n else p ++ "." ++ n

def resolve (env : Env) (locals : Std.HashMap Name Expr) (n : Name) : Option (Name × Expr) :=
  if let some t := locals.get? n then
    some (n, t)
  else if n.startsWith "." then
    let root := n.drop 1 |>.toString
    if env.decls.contains root then some (root, .ident root) else none
  else
    let q := qualify env n
    if env.decls.contains q then
      some (q, .ident q)
    else if env.decls.contains n then
      some (n, .ident n)
    else
      env.opens.foldl
        (fun acc ns =>
          match acc with
          | some x => some x
          | none =>
              let q := ns ++ "." ++ n
              if env.decls.contains q then some (q, .ident q) else none)
        none

partial def normalize (env : Env) : Expr -> Expr
  | .ident n =>
      match env.decls.get? n with
      | some d =>
          if d.kind != .axiom && d.params.isEmpty then
            match d.body with
            | some b => normalize env b
            | none => .ident n
          else .ident n
      | none => .ident n
  | .app f a =>
      let e := Expr.app (normalize env f) (normalize env a)
      let (h, args) := Expr.headArgs e
      match h with
      | Expr.ident n =>
          match env.decls.get? n with
          | some d =>
              if d.kind != .axiom && args.size >= d.params.size then
                match d.body with
                | some b =>
                    let pairs := (d.params.map (fun p => p.name)).zip (args.extract 0 d.params.size)
                    let expanded := b.substMany pairs
                    Expr.appMany (normalize env expanded) (args.extract d.params.size args.size)
                | none => e
              else e
          | none => e
      | _ => e
  | .arrow a b => .arrow (normalize env a) (normalize env b)
  | .prod a b => .prod (normalize env a) (normalize env b)
  | .comp f g => .comp (normalize env f) (normalize env g)
  | e => e

partial def qualifyExpr (env : Env) (locals : Std.HashMap Name Expr) : Expr -> Expr
  | .ident n =>
      if locals.contains n then
        .ident n
      else
        match resolve env locals n with
        | some (q, _) => .ident q
        | none => .ident n
  | .hole => .hole
  | .sortType => .sortType
  | .sortProp => .sortProp
  | .arrow a b => .arrow (qualifyExpr env locals a) (qualifyExpr env locals b)
  | .prod a b => .prod (qualifyExpr env locals a) (qualifyExpr env locals b)
  | .app f a => .app (qualifyExpr env locals f) (qualifyExpr env locals a)
  | .comp f g => .comp (qualifyExpr env locals f) (qualifyExpr env locals g)

partial def compatible (env : Env) (a b : Expr) : Bool :=
  let a := normalize env a
  let b := normalize env b
  match a, b with
  | .hole, _ => true
  | _, .hole => true
  | .ident x, .ident y => x == y
  | .sortType, .sortType => true
  | .sortProp, .sortProp => true
  | .arrow a1 a2, .arrow b1 b2 => compatible env a1 b1 && compatible env a2 b2
  | .prod a1 a2, .prod b1 b2 => compatible env a1 b1 && compatible env a2 b2
  | .app a1 a2, .app b1 b2 => compatible env a1 b1 && compatible env a2 b2
  | .comp a1 a2, .comp b1 b2 => compatible env a1 b1 && compatible env a2 b2
  | _, _ => false

def ensureCompat (env : Env) (got expected : Expr) : CheckM Unit :=
  unless compatible env got expected do
    throw s!"type mismatch: got {got.toCoreString}, expected {expected.toCoreString}"

mutual
partial def infer (env : Env) (locals : Std.HashMap Name Expr) (e : Expr) : CheckM Expr := do
  match e with
  | .hole => pure .hole
  | .sortType => pure .sortType
  | .sortProp => pure .sortType
  | .ident n =>
      match locals.get? n with
      | some ty => pure ty
      | none =>
          match resolve env locals n with
          | some (_, ty) =>
              match ty with
              | .ident q =>
                  match env.decls.get? q with
                  | some d =>
                      if d.params.isEmpty then pure d.type
                      else throw s!"partial application of '{q}': expected {d.params.size} head parameter(s), got 0"
                  | none => pure ty
              | _ => pure ty
          | none => throw s!"unknown identifier '{n}'"
  | .arrow a b =>
      let ta <- infer env locals a
      let tb <- infer env locals b
      if compatible env ta .sortProp && compatible env tb .sortProp then
        pure .sortProp
      else
        pure .sortType
  | .prod a b =>
      discard <| infer env locals a
      discard <| infer env locals b
      pure .sortType
  | .comp f g =>
      let tf := normalize env (<- infer env locals f)
      let tg := normalize env (<- infer env locals g)
      match tf, tg with
      | .arrow y z, .arrow x y' =>
          ensureCompat env y' y
          pure (.arrow x z)
      | _, _ => throw s!"composition expects arrows, got {tf.toCoreString} and {tg.toCoreString}"
  | .app _ _ =>
      inferApp env locals e

partial def inferApp (env : Env) (locals : Std.HashMap Name Expr) (e : Expr) : CheckM Expr := do
  let (h, args) := Expr.headArgs e
  match h with
  | .ident n =>
      if let some (q, localTy) := resolve env locals n then
        if locals.contains q then
          inferOrdinary env locals localTy args
        else
          match env.decls.get? q with
          | some d =>
              if args.size < d.params.size then
                throw s!"partial application of '{q}': expected {d.params.size} head parameter(s), got {args.size}"
              let mut pairs := #[]
              for i in [0:d.params.size] do
                let p := d.params[i]!
                let expected := p.type.substMany pairs
                let got <- infer env locals args[i]!
                ensureCompat env got expected
                pairs := pairs.push (p.name, args[i]!)
              let resultTy := d.type.substMany pairs
              inferOrdinary env locals resultTy (args.extract d.params.size args.size)
          | none => inferOrdinary env locals localTy args
      else
        throw s!"unknown identifier '{n}'"
  | _ =>
      let th <- infer env locals h
      inferOrdinary env locals th args

partial def inferOrdinary (env : Env) (locals : Std.HashMap Name Expr) (ty : Expr) (args : Array Expr) : CheckM Expr := do
  let mut cur := ty
  for a in args do
    match normalize env cur with
    | .arrow dom cod =>
        let got <- infer env locals a
        ensureCompat env got dom
        cur := cod
    | other =>
        throw s!"cannot apply non-function of type {other.toCoreString}"
  pure cur
end

def checkParams (env : Env) (locals0 : Std.HashMap Name Expr) (params : Array Param) : CheckM (Std.HashMap Name Expr) := do
  let mut locals := locals0
  for p in params do
    discard <| infer env locals p.type
    locals := locals.insert p.name p.type
  pure locals

def checkDecl (env : Env) (d : Decl) : CheckM Decl := do
  let locals <- checkParams env {} d.params
  let ty :=
    match d.body, d.type with
    | some b, .hole => infer env locals b
    | _, t => pure t
  let ty <- ty
  discard <| infer env locals ty
  if let some b := d.body then
    let got <- infer env locals b
    ensureCompat env got ty
  let mut storeLocals : Std.HashMap Name Expr := {}
  let mut qparams := #[]
  for p in d.params do
    let qtype := qualifyExpr env storeLocals p.type
    qparams := qparams.push { p with type := qtype }
    storeLocals := storeLocals.insert p.name qtype
  pure { d with
    params := qparams,
    type := qualifyExpr env locals ty,
    body := d.body.map (qualifyExpr env locals) }

def checkCommand (env : Env) : Nat × Command -> Except Diagnostic Env
  | (line, cmd) =>
      match cmd with
      | .importCmd _ => pure env
      | .openCmd n => pure { env with opens := env.opens.push n }
      | .namespaceCmd n => pure { env with nsStack := env.nsStack.push n }
      | .endCmd _ => pure { env with nsStack := env.nsStack.pop }
      | .checkCmd e =>
          match e with
          | .ident n =>
              match resolve env {} n with
              | some (q, _) =>
                  if env.decls.contains q then pure env
                  else
                    match infer env {} e with
                    | .ok _ => pure env
                    | .error msg => throw { file := "", line, message := msg }
              | none => throw { file := "", line, message := s!"unknown identifier '{n}'" }
          | _ =>
              match infer env {} e with
              | .ok _ => pure env
              | .error msg => throw { file := "", line, message := msg }
      | .declCmd d =>
          let qn := qualify env d.name
          let d := { d with name := qn }
          match checkDecl env d with
          | .ok d => pure { env with decls := env.decls.insert qn d }
          | .error msg => throw { file := "", line, message := msg }

def checkCommandsIn (env0 : Env) (file : String) (cmds : Array (Nat × Command)) : Except Diagnostic Env := do
  let mut env : Env := env0
  for c in cmds do
    match checkCommand env c with
    | .ok env' => env := env'
    | .error d => throw { d with file := file }
  pure env

def checkCommands (file : String) (cmds : Array (Nat × Command)) : Except Diagnostic Env :=
  checkCommandsIn {} file cmds

def checkSource (file src : String) : Except Diagnostic Env := do
  let cmds <- parseFile file src
  checkCommands file cmds

def checkSourceIn (env : Env) (file src : String) : Except Diagnostic Env := do
  let cmds <- parseFile file src
  checkCommandsIn env file cmds

end CoreChecker
