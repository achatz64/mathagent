import ContextualHOL.Core

namespace ContextualHOL

namespace Cor

def parens (text : String) : String :=
  "(" ++ text ++ ")"

def joinSep (sep : String) : List String -> String
  | [] => ""
  | [item] => item
  | item :: rest => item ++ sep ++ joinSep sep rest

def addUnique (name : Name) : List Name -> List Name
  | [] => [name]
  | existing :: rest =>
      if existing = name then
        existing :: rest
      else
        existing :: addUnique name rest

def renderTy : Ty -> String
  | Ty.base name => name
  | Ty.final => "Final"
  | Ty.prod left right => parens (renderTy left ++ " × " ++ renderTy right)
  | Ty.prop => "PC"

def collectTyBases : Ty -> List Name -> List Name
  | Ty.base name, acc => addUnique name acc
  | Ty.final, acc => acc
  | Ty.prod left right, acc => collectTyBases right (collectTyBases left acc)
  | Ty.prop, acc => acc

def collectCtxBases : Ctx -> List Name -> List Name
  | [], acc => acc
  | binding :: rest, acc => collectCtxBases rest (collectTyBases binding.ty acc)

def collectTermBases (env : Env) : Term -> List Name -> List Name
  | Term.var _, acc => acc
  | Term.const name, acc =>
      match lookupConst? env name with
      | none => acc
      | some ty => collectTyBases ty acc
  | Term.raw _ ty, acc => collectTyBases ty acc

def collectFormulaBases (env : Env) : Formula -> List Name -> List Name
  | Formula.atom _ left right, acc =>
      collectTermBases env right (collectTermBases env left acc)
  | Formula.papp pred arg, acc =>
      let acc :=
        match lookupPred? env pred with
        | none => acc
        | some ty => collectTyBases ty acc
      collectTermBases env arg acc
  | Formula.and p q, acc => collectFormulaBases env q (collectFormulaBases env p acc)
  | Formula.or p q, acc => collectFormulaBases env q (collectFormulaBases env p acc)
  | Formula.imp p q, acc => collectFormulaBases env q (collectFormulaBases env p acc)
  | Formula.iff p q, acc => collectFormulaBases env q (collectFormulaBases env p acc)
  | Formula.not p, acc => collectFormulaBases env p acc
  | Formula.all _ ty body, acc => collectFormulaBases env body (collectTyBases ty acc)
  | Formula.ex _ ty body, acc => collectFormulaBases env body (collectTyBases ty acc)

def collectEnvBases (env : Env) (acc : List Name) : List Name :=
  let acc := env.consts.foldl (fun acc item => collectTyBases item.snd acc) acc
  let acc := env.preds.foldl (fun acc item => collectTyBases item.snd acc) acc
  env.rels.foldl
    (fun acc item => collectTyBases item.snd.right (collectTyBases item.snd.left acc))
    acc

def collectSequentBases (env : Env) (seq : Sequent) : List Name :=
  let acc := collectEnvBases env []
  let acc := collectCtxBases seq.objectCtx acc
  let acc := seq.assumptions.foldl (fun acc formula => collectFormulaBases env formula acc) acc
  collectFormulaBases env seq.conclusion acc

def renderTypeBinders (names : List Name) : List String :=
  names.map (fun name => parens (name ++ " : Type"))

def renderConstBinders (env : Env) : List String :=
  env.consts.map (fun item => parens (item.fst ++ " : " ++ renderTy item.snd))

def renderRelBinders (env : Env) : List String :=
  env.rels.map (fun item =>
    parens (item.fst ++ " : Pred " ++ parens (renderTy item.snd.left ++ " × " ++ renderTy item.snd.right)))

def renderPredBinders (env : Env) : List String :=
  env.preds.map (fun item => parens (item.fst ++ " : Pred " ++ renderTy item.snd))

def renderBinders (env : Env) (seq : Sequent) : String :=
  joinSep " " (renderTypeBinders (collectSequentBases env seq) ++
    renderConstBinders env ++ renderPredBinders env ++ renderRelBinders env)

def takeCtx : Nat -> Ty -> Except String (List Ty × Ty)
  | 0, ctx => Except.ok ([], ctx)
  | Nat.succ count, Ty.prod head rest => do
      let (heads, tail) <- takeCtx count rest
      pure (head :: heads, tail)
  | Nat.succ _, ctx =>
      Except.error ("cannot project from non-product context " ++ renderTy ctx)

def renderProjection (idx : Nat) (ctx : Ty) : Except String String := do
  if idx > 3 then
    Except.error ("projector v" ++ toString idx ++ " is not available in prod.cor yet")
  else
    let (heads, tail) <- takeCtx (idx + 1) ctx
    pure (parens ("v" ++ toString idx ++ " " ++
      joinSep " " ((heads.map renderTy) ++ [renderTy tail])))

def renderTerm (ctx : Ty) : Core.Term -> Except String String
  | Core.Term.proj idx => renderProjection idx ctx
  | Core.Term.weakening ty weakenedCtx name =>
      pure (parens ("Cart.weakening " ++ renderTy ty ++ " " ++ renderTy weakenedCtx ++ " " ++ name))
  | Core.Term.raw name _ => pure name

partial def renderPred : Core.Pred -> Except String String
  | Core.Pred.atom ctx left right rel leftTerm rightTerm => do
      let leftCore <- renderTerm ctx leftTerm
      let rightCore <- renderTerm ctx rightTerm
      pure (parens ("sub2 " ++ renderTy ctx ++ " " ++ renderTy left ++ " " ++ renderTy right ++
        " " ++ rel ++ " " ++ leftCore ++ " " ++ rightCore))
  | Core.Pred.papp ctx _ pred arg => do
      let argCore <- renderTerm ctx arg
      pure (parens (pred ++ " ∘ " ++ argCore))
  | Core.Pred.and ctx p q => do
      let pCore <- renderPred p
      let qCore <- renderPred q
      pure (parens ("Pred.and " ++ renderTy ctx ++ " " ++ pCore ++ " " ++ qCore))
  | Core.Pred.or ctx p q => do
      let pCore <- renderPred p
      let qCore <- renderPred q
      pure (parens ("Pred.or " ++ renderTy ctx ++ " " ++ pCore ++ " " ++ qCore))
  | Core.Pred.imp ctx p q => do
      let pCore <- renderPred p
      let qCore <- renderPred q
      pure (parens ("Pred.imply " ++ renderTy ctx ++ " " ++ pCore ++ " " ++ qCore))
  | Core.Pred.iff ctx p q => do
      let pCore <- renderPred p
      let qCore <- renderPred q
      pure (parens ("Pred.iff " ++ renderTy ctx ++ " " ++ pCore ++ " " ++ qCore))
  | Core.Pred.not ctx p => do
      let pCore <- renderPred p
      pure (parens ("Pred.not " ++ renderTy ctx ++ " " ++ pCore))
  | Core.Pred.all bound ctx body => do
      let bodyCore <- renderPred body
      pure (parens ("Forall " ++ renderTy bound ++ " " ++ renderTy ctx ++ " " ++ bodyCore))
  | Core.Pred.ex bound ctx body => do
      let bodyCore <- renderPred body
      pure (parens ("Exist " ++ renderTy bound ++ " " ++ renderTy ctx ++ " " ++ bodyCore))

def renderClosedProp : Core.Closed -> Except String String
  | Core.Closed.term pred => do
      let predCore <- renderPred pred
      pure ("Pred.term " ++ predCore)

def renderAxiom (declName : Name) (env : Env) (seq : Sequent) : Except String String := do
  if checkSequent? env seq == some () then
    let closed <- match translateClosedSequent? env seq with
      | some closed => Except.ok closed
      | none => Except.error ("translation failed after successful checking for " ++ declName)
    let prop <- renderClosedProp closed
    let binders := renderBinders env seq
    pure ("axiom " ++ declName ++
      (if binders.isEmpty then "" else " " ++ binders) ++ " :\n  " ++ prop)
  else
    Except.error ("source sequent does not check for " ++ declName)

def renderFile (decls : List String) : String :=
  "-- Generated by formalization/GenerateCoreExamples.lean.\n" ++
  "-- Do not edit by hand; edit the Lean source example instead.\n\n" ++
  "import classical_first_order_logic_new\n\n" ++
  joinSep "\n\n" decls ++ "\n"

end Cor

end ContextualHOL
