import ContextualHOL.ProgramC
import ContextualHOL.CoreFile

/-!
# Checked `set.cor` environment quotation

The native syntax occurs only on the left side of this boundary.  Successful
results are `ProgramC.Env` values containing a contextual signature and
contextual theory schemas; no native expression is retained.

The refunctionalizer below recognizes the canonical predicate/context
combinators used by `set.cor`: `Pred.term`, `Forall`, `Exist`, the predicate
connectives, `sub2`, `inst`, composition, projections, and weakening.  Named
definitions are unfolded one head step at a time.  There is no formula keyed
by an axiom name and no opaque fallback constructor.
-/

namespace ContextualHOL.ProgramC.SetTheoryQuote

abbrev NativeExpr := CoreChecker.Expr
abbrev NativeEnv := CoreChecker.Env

inductive Error where
  | missingDeclaration (name : String)
  | badDeclaration (name stage : String)
  | unsupported (stage head : String)
  | native (message : String)
  deriving Repr

abbrev Result (α : Type) := Except Error α

private def headView (expression : NativeExpr) : Option (String × List NativeExpr) :=
  let (head, arguments) := expression.headArgs
  match head with
  | .ident name => some (name, arguments.toList)
  | _ => none

private def headLabel (expression : NativeExpr) : String :=
  match headView expression with
  | some (name, _) => name
  | none => match expression with
    | .comp _ _ => "composition"
    | .arrow _ _ => "arrow"
    | .prod _ _ => "product"
    | .sortType => "Type"
    | .sortProp => "Prop"
    | .hole => "hole"
    | .app _ _ | .ident _ => "expression"

private def declaration (env : NativeEnv) (name : String) : Result CoreChecker.Decl :=
  match env.decls.get? name with
  | some declaration => pure declaration
  | none => throw (.missingDeclaration name)

/-- One transparent head expansion.  Logical primitives and opaque vocabulary
are never expanded because they have no body. -/
private def unfoldHead? (env : NativeEnv) (expression : NativeExpr) : Option NativeExpr :=
  let (head, arguments) := expression.headArgs
  match head with
  | .ident name =>
      match env.decls.get? name with
      | some declaration =>
          if declaration.kind == .axiom || arguments.size < declaration.params.size then none
          else match declaration.body with
            | none => none
            | some body =>
                let pairs := (declaration.params.map (fun parameter => parameter.name)).zip
                  (arguments.extract 0 declaration.params.size)
                let expanded := body.substMany pairs
                some (CoreChecker.Expr.appMany expanded
                  (arguments.extract declaration.params.size arguments.size))
      | none => none
  | _ => none

private partial def quoteTy (env : NativeEnv) (expression : NativeExpr) : Result Ty :=
  match CoreChecker.normalize env expression with
  | .sortProp => pure .prop
  | .ident "Final" => pure .final
  | .ident name => pure (.base name)
  | .prod left right => do
      pure (.prod (← quoteTy env left) (← quoteTy env right))
  | .arrow left right => do
      pure (.arr (← quoteTy env left) (← quoteTy env right))
  | other => throw (.unsupported "type" (headLabel other))

structure LocalInfo where
  objects : List (String × Name × Ty) := []
  symbols : List (String × Name × SchemaKind) := []

private def LocalInfo.object? (locals : LocalInfo) (source : String) : Option (Name × Ty) :=
  locals.objects.find? (fun item => item.1 == source) |>.map
    (fun item => (item.2.1, item.2.2))

private def LocalInfo.symbol? (locals : LocalInfo) (source : String) : Option (Name × SchemaKind) :=
  locals.symbols.find? (fun item => item.1 == source) |>.map
    (fun item => (item.2.1, item.2.2))

private def symbolName (schema source : String) : Name := schema ++ "." ++ source

private def arrowDomains (env : NativeEnv) (expression : NativeExpr) : List NativeExpr × NativeExpr :=
  let rec go : NativeExpr -> List NativeExpr -> List NativeExpr × NativeExpr
    | .arrow domain codomain, domains => go codomain (domains ++ [domain])
    | codomain, domains => (domains, codomain)
  go (CoreChecker.normalize env expression) []

private def classifyParameter (env : NativeEnv) (schema : String)
    (parameter : CoreChecker.Param) : Result (Sum Binding SchemaBinding ×
      Option (String × Name × SchemaKind)) := do
  let normalized := CoreChecker.normalize env parameter.type
  if normalized == .sortType then
    let binding : SchemaBinding := { name := symbolName schema parameter.name, kind := .type }
    pure (.inr binding, some (parameter.name, binding.name, binding.kind))
  else
    let (domains, codomain) := arrowDomains env normalized
    if codomain == .sortProp then
      let inputs ← domains.mapM (quoteTy env)
      let binding : SchemaBinding :=
        { name := symbolName schema parameter.name, kind := .predicate inputs }
      pure (.inr binding, some (parameter.name, binding.name, binding.kind))
    else if domains.isEmpty then
      pure (.inl { name := parameter.name, ty := ← quoteTy env normalized }, none)
    else
      let inputs ← domains.mapM (quoteTy env)
      let binding : SchemaBinding :=
        { name := symbolName schema parameter.name,
          kind := .function inputs (← quoteTy env codomain) }
      pure (.inr binding, some (parameter.name, binding.name, binding.kind))

private inductive ContextValue where
  | atom : TermShape -> ContextValue
  | pair : ContextValue -> ContextValue -> ContextValue
  | final
  deriving Repr

private def ContextValue.rightNested : List TermShape -> ContextValue
  | [] => .final
  | term :: rest => .pair (.atom term) (rightNested rest)

private def ContextValue.atom? : ContextValue -> Option TermShape
  | .atom term => some term
  | _ => none

private def ContextValue.left? : ContextValue -> Option ContextValue
  | .pair left _ => some left
  | _ => none

private def ContextValue.right? : ContextValue -> Option ContextValue
  | .pair _ right => some right
  | _ => none

private def ContextValue.nth? : ContextValue -> Nat -> Option ContextValue
  | value, 0 => value.left?
  | value, n + 1 => value.right?.bind (fun right => right.nth? n)

mutual
  private partial def quoteTerm (env : NativeEnv) (locals : LocalInfo)
      (expression : NativeExpr) : Result TermShape := do
    match expression with
    | .ident name =>
        match locals.object? name with
        | some (target, _) => pure (.var target)
        | none =>
            match locals.symbol? name with
            | some (target, .term _) => pure (.call target [])
            | _ =>
                match env.decls.get? name with
                | some declaration =>
                    if declaration.kind == .axiom && declaration.params.isEmpty then
                      pure (.call name [])
                    else match unfoldHead? env expression with
                      | some expanded => quoteTerm env locals expanded
                      | none => throw (.unsupported "term" name)
                | none => throw (.unsupported "term" name)
    | .app _ _ =>
        let (head, arguments) := expression.headArgs
        match head with
        | .ident name =>
            match locals.symbol? name with
            | some (target, .function _ _) =>
                pure (.call target (← arguments.toList.mapM (quoteTerm env locals)))
            | _ => match unfoldHead? env expression with
              | some expanded => quoteTerm env locals expanded
              | none => throw (.unsupported "term-application" name)
        | _ => throw (.unsupported "term-application" (headLabel expression))
    | .comp function argument =>
        pure (.comp (← quoteTerm env locals function) (← quoteTerm env locals argument))
    | _ => match unfoldHead? env expression with
      | some expanded => quoteTerm env locals expanded
      | none => throw (.unsupported "term" (headLabel expression))

  private partial def quoteMap (env : NativeEnv) (locals : LocalInfo)
      (expression : NativeExpr) (input : ContextValue) : Result ContextValue := do
    match expression with
    | .comp function argument =>
        quoteMap env locals function (← quoteMap env locals argument input)
    | _ =>
      match headView expression with
      | some ("v0", [_X, _Y]) =>
          match input.nth? 0 with
          | some value => pure value
          | none => throw (.unsupported "v0" "short-context")
      | some ("v1", [_X, _Y, _Z]) =>
          match input.nth? 1 with
          | some value => pure value
          | none => throw (.unsupported "v1" "short-context")
      | some ("v2", [_W, _X, _Y, _Z]) =>
          match input.nth? 2 with
          | some value => pure value
          | none => throw (.unsupported "v2" "short-context")
      | some ("v3", [_V, _W, _X, _Y, _Z]) =>
          match input.nth? 3 with
          | some value => pure value
          | none => throw (.unsupported "v3" "short-context")
      | some ("fst", [_A, _B]) =>
          match input.left? with
          | some value => pure value
          | none => throw (.unsupported "fst" "non-product-context")
      | some ("snd", [_A, _B]) =>
          match input.right? with
          | some value => pure value
          | none => throw (.unsupported "snd" "non-product-context")
      | some ("Cart.weakening", [_X, _Y, term]) =>
          pure (.atom (← quoteTerm env locals term))
      | some ("pair", [_T, _A, _B, left, right]) =>
          pure (.pair (← quoteMap env locals left input) (← quoteMap env locals right input))
      | _ => match unfoldHead? env expression with
        | some expanded => quoteMap env locals expanded input
        | none => throw (.unsupported "context-map" (headLabel expression))

  private partial def quotePredicate (env : NativeEnv) (locals : LocalInfo)
      (depth : Nat) (expression : NativeExpr) (input : ContextValue) : Result FormulaShape := do
    match expression with
    | .comp predicate map =>
        quotePredicate env locals depth predicate (← quoteMap env locals map input)
    | _ =>
      match headView expression with
      | some ("Forall", [type, _context, body]) =>
          let binder := s!"_x{depth}"
          let binderType ← quoteTy env type
          pure (.all binder binderType
            (← quotePredicate env locals (depth + 1) body
              (.pair (.atom (.var binder)) input)))
      | some ("Exist", [type, _context, body]) =>
          let binder := s!"_x{depth}"
          let binderType ← quoteTy env type
          pure (.ex binder binderType
            (← quotePredicate env locals (depth + 1) body
              (.pair (.atom (.var binder)) input)))
      | some ("Pred.and", [_context, left, right]) =>
          pure (.and (← quotePredicate env locals depth left input)
            (← quotePredicate env locals depth right input))
      | some ("Pred.or", [_context, left, right]) =>
          pure (.or (← quotePredicate env locals depth left input)
            (← quotePredicate env locals depth right input))
      | some ("Pred.imply", [_context, left, right]) =>
          pure (.imp (← quotePredicate env locals depth left input)
            (← quotePredicate env locals depth right input))
      | some ("Pred.iff", [_context, left, right]) =>
          pure (.iff (← quotePredicate env locals depth left input)
            (← quotePredicate env locals depth right input))
      | some ("Pred.not", [_context, body]) =>
          pure (.not (← quotePredicate env locals depth body input))
      | some ("sub2", [_T, _A, _B, relation, leftMap, rightMap]) =>
          let left ← quoteMap env locals leftMap input
          let right ← quoteMap env locals rightMap input
          quotePredicate env locals depth relation (.pair left right)
      | some ("inst", [_X, predicate, term]) =>
          quotePredicate env locals depth predicate
            (.pair (.atom (← quoteTerm env locals term)) input)
      | some ("uncurry", [_A, _B, _C, function]) =>
          match input with
          | .pair left right =>
              let left ← match left.atom? with
                | some term => pure term
                | none => throw (.unsupported "uncurry-left" "non-atom")
              let right ← match right.atom? with
                | some term => pure term
                | none => throw (.unsupported "uncurry-right" "non-atom")
              match function with
              | .ident name =>
                  match locals.symbol? name with
                  | some (target, .predicate [_left, _right]) => pure (.pred target [left, right])
                  | _ => pure (.pred name [left, right])
              | _ => throw (.unsupported "uncurry" (headLabel function))
          | _ => throw (.unsupported "uncurry" "non-pair-context")
      | some (name, []) =>
          match locals.symbol? name with
          | some (target, .predicate inputs) =>
              let rec collect : ContextValue -> List Ty -> Result (List TermShape)
                | value, [_] => match value.atom? with
                  | some term => pure [term]
                  | none => throw (.unsupported "predicate-context" target)
                | .pair left right, _ :: rest => do
                    let first ← match left.atom? with
                      | some term => pure term
                      | none => throw (.unsupported "predicate-context" target)
                    pure (first :: (← collect right rest))
                | _, [] => pure []
                | _, _ => throw (.unsupported "predicate-context" target)
              pure (.pred target (← collect input inputs))
          | _ => match unfoldHead? env expression with
            | some expanded => quotePredicate env locals depth expanded input
            | none => throw (.unsupported "predicate" name)
      | _ => match unfoldHead? env expression with
        | some expanded => quotePredicate env locals depth expanded input
        | none => throw (.unsupported "predicate" (headLabel expression))

  private partial def quoteFormula (env : NativeEnv) (locals : LocalInfo)
      (depth : Nat) (expression : NativeExpr) : Result FormulaShape := do
    match expression with
    | .arrow left right =>
        pure (.imp (← quoteFormula env locals depth left) (← quoteFormula env locals depth right))
    | _ =>
      match headView expression with
      | some ("Pred.term", [predicate]) =>
          quotePredicate env locals depth predicate .final
      | some ("imply", [left, right]) =>
          pure (.imp (← quoteFormula env locals depth left)
            (← quoteFormula env locals depth right))
      | some ("and", [left, right]) =>
          pure (.and (← quoteFormula env locals depth left)
            (← quoteFormula env locals depth right))
      | some ("or", [left, right]) =>
          pure (.or (← quoteFormula env locals depth left)
            (← quoteFormula env locals depth right))
      | some ("iff", [left, right]) =>
          pure (.iff (← quoteFormula env locals depth left)
            (← quoteFormula env locals depth right))
      | some ("not", [body]) => pure (.not (← quoteFormula env locals depth body))
      | _ => match unfoldHead? env expression with
        | some expanded => quoteFormula env locals depth expanded
        | none =>
            match expression with
            | .app predicate term =>
                quotePredicate env locals depth predicate (.atom (← quoteTerm env locals term))
            | _ => throw (.unsupported "formula" (headLabel expression))
end

private def addSchemaSymbols (signature : Signature) (parameters : SchemaCtx) : Signature :=
  parameters.foldl (fun current parameter =>
    match parameter.kind with
    | .type => current
    | .term output =>
        { current with functions := current.functions ++
            [(parameter.name, { inputs := [], output })] }
    | .function inputs output =>
        { current with functions := current.functions ++
            [(parameter.name, { inputs, output })] }
    | .predicate inputs =>
        { current with predicates := current.predicates ++
            [(parameter.name, { inputs })] }) signature

private structure QuotedSchema where
  schema : TheorySchema
  signature : Signature

private def quoteAxiom (env : NativeEnv) (signature : Signature)
    (name : String) : Result QuotedSchema := do
  let source ← declaration env name
  unless source.kind == .axiom do throw (.badDeclaration name "not-an-axiom")
  let mut objects : Ctx := []
  let mut parameters : SchemaCtx := []
  let mut locals : LocalInfo := {}
  for parameter in source.params do
    match ← classifyParameter env name parameter with
    | (.inl object, _) =>
        objects := objects ++ [object]
        locals := { locals with objects := locals.objects ++
          [(parameter.name, object.name, object.ty)] }
    | (.inr schemaParameter, some symbol) =>
        parameters := parameters ++ [schemaParameter]
        locals := { locals with symbols := locals.symbols ++ [symbol] }
    | (.inr schemaParameter, none) =>
        parameters := parameters ++ [schemaParameter]
  let conclusion ← quoteFormula env locals 0 source.type
  pure (QuotedSchema.mk (TheorySchema.mk name parameters objects conclusion)
    (addSchemaSymbols signature parameters))

def setAxiomNames : List String :=
  ["memCong_left_all", "pairing", "union_ax", "power_ax", "separation",
   "empty_ax", "Inf_spec", "regularity", "replacement", "choice"]

/-- Quote the checked declarations contributed by `set.cor`.  The result is
entirely contextual data.  Failure is classified; there is no raw or theorem-
specific escape hatch. -/
def quoteCheckedSetEnv (native : NativeEnv) : Result Env := do
  let sets ← declaration native "Sets"
  unless sets.kind == .axiom && sets.params.isEmpty && sets.type == .sortType do
    throw (.badDeclaration "Sets" "expected-opaque-type")
  let setTy : Ty := .base "Sets"
  let elem ← declaration native "elem"
  unless elem.kind == .axiom do throw (.badDeclaration "elem" "expected-opaque-relation")
  let inf ← declaration native "Inf"
  unless inf.kind == .axiom do throw (.badDeclaration "Inf" "expected-opaque-object")
  let mut signature : Signature :=
    { functions := [("Inf", { inputs := [], output := setTy })],
      predicates := [("elem", { inputs := [setTy, setTy] })] }
  let mut schemas : List TheorySchema := []
  for name in setAxiomNames do
    let quoted ← match quoteAxiom native signature name with
      | .ok quoted => pure quoted
      | .error error => throw (.badDeclaration name s!"{repr error}")
    signature := quoted.signature
    schemas := schemas ++ [quoted.schema]
  pure { signature, theory := { schemas } }

/-! ## Immediate contextual derivations

The quotation result is executable as a theory, not just printable syntax.
For every translated schema we reconstruct formula evidence and build the
dedicated `DerivRaw.schema` node. -/

private abbrev SomeVar (gamma : Ctx) (name : Name) :=
  Sigma fun type => VarHasType gamma name type

private def findVar (gamma : Ctx) (name : Name) : Result (SomeVar gamma name) :=
  match gamma with
  | [] => throw (.unsupported "context-variable" name)
  | binding :: rest =>
      if same : binding.name = name then
        pure (same ▸ Sigma.mk binding.ty VarHasType.here)
      else
        match findVar rest name with
        | .error error => throw error
        | .ok ⟨type, evidence⟩ =>
            pure ⟨type, VarHasType.there same evidence⟩

private structure FunctionLookup (signature : Signature) (name : Name) where
  spec : FunSig
  member : (name, spec) ∈ signature.functions

private def findFunction (signature : Signature) (name : Name) :
    Result (FunctionLookup signature name) :=
  let rec go : (functions : List (Name × FunSig)) -> Result
      ({ spec : FunSig // (name, spec) ∈ functions })
    | [] => throw (.unsupported "function-symbol" name)
    | (candidate, spec) :: rest =>
        if same : candidate = name then
          pure ⟨spec, by simp [same]⟩
        else do
          let found ← go rest
          pure ⟨found.1, by simp [found.2]⟩
  match go signature.functions with
  | .ok found => pure { spec := found.1, member := found.2 }
  | .error error => throw error

private structure PredicateLookup (signature : Signature) (name : Name) where
  spec : PredSig
  member : (name, spec) ∈ signature.predicates

private def findPredicate (signature : Signature) (name : Name) :
    Result (PredicateLookup signature name) :=
  let rec go : (predicates : List (Name × PredSig)) -> Result
      ({ spec : PredSig // (name, spec) ∈ predicates })
    | [] => throw (.unsupported "predicate-symbol" name)
    | (candidate, spec) :: rest =>
        if same : candidate = name then
          pure ⟨spec, by simp [same]⟩
        else do
          let found ← go rest
          pure ⟨found.1, by simp [found.2]⟩
  match go signature.predicates with
  | .ok found => pure { spec := found.1, member := found.2 }
  | .error error => throw error

private def buildTermAt (E : Env) (gamma : Ctx) (delta : List FormulaShape) :
    (term : TermShape) -> (expected : Ty) ->
    Result (TermEvidenceFor E gamma delta term expected)
  | .var name, expected => do
      match ← findVar gamma name with
      | ⟨actual, evidence⟩ =>
          if same : actual = expected then pure (.var (same ▸ evidence))
          else throw (.unsupported "term-evidence" "variable-type")
  | .call name [], expected => do
      let found ← findFunction E.signature name
      if inputsEmpty : found.spec.inputs = [] then
        if outputSame : found.spec.output = expected then
          pure (.call (argTys := []) (inputsEmpty ▸ outputSame ▸ found.member) .nil)
        else throw (.unsupported "term-evidence" "constant-output")
      else throw (.unsupported "term-evidence" "constant-arity")
  | _, _ => throw (.unsupported "term-evidence" "non-atomic-set-term")

private def buildTermsEvidence (E : Env) (gamma : Ctx)
    (delta : List FormulaShape) : (terms : List TermShape) -> (types : List Ty) ->
    Result (TermsEvidence E.signature E.theory gamma delta terms types)
  | [], [] => pure .nil
  | term :: terms, type :: types => do
      pure (.cons (← buildTermAt E gamma delta term type)
        (← buildTermsEvidence E gamma delta terms types))
  | _, _ => throw (.unsupported "term-evidence" "arity")

private def buildFormulaEvidence (E : Env) (gamma : Ctx)
    (delta : List FormulaShape) : (formula : FormulaShape) ->
    Result (FormulaEvidenceFor E gamma delta formula)
  | .pred name arguments => do
      match ← findPredicate E.signature name with
      | found =>
          pure (.pred found.member
            (← buildTermsEvidence E gamma delta arguments found.spec.inputs))
  | .holds term => do
      pure (.holds (← buildTermAt E gamma delta term .prop))
  | .and left right => do
      pure (.and (← buildFormulaEvidence E gamma delta left)
        (← buildFormulaEvidence E gamma delta right))
  | .or left right => do
      pure (.or (← buildFormulaEvidence E gamma delta left)
        (← buildFormulaEvidence E gamma delta right))
  | .imp left right => do
      pure (.imp (← buildFormulaEvidence E gamma delta left)
        (← buildFormulaEvidence E gamma delta right))
  | .iff left right => do
      pure (.iff (← buildFormulaEvidence E gamma delta left)
        (← buildFormulaEvidence E gamma delta right))
  | .not body => do pure (.not (← buildFormulaEvidence E gamma delta body))
  | .all name type body => do
      pure (.all (← buildFormulaEvidence E ({ name, ty := type } :: gamma) delta body))
  | .ex name type body => do
      pure (.ex (← buildFormulaEvidence E ({ name, ty := type } :: gamma) delta body))
  | .hasChar _ _ _ _ _ _ | .existUniqueChar _ _ _ _ _ |
      .hasCharNeg _ _ _ | .existUniqueNeg _ _ =>
      throw (.unsupported "formula-evidence" "description")

structure SchemaDerivation (E : Env) where
  schema : TheorySchema
  member : schema ∈ E.theory.schemas
  derivation : Deriv E schema.objects [] schema.conclusion

def deriveTheory (E : Env) : Result (List (SchemaDerivation E)) :=
  let rec go : (remaining : List TheorySchema) ->
      (∀ schema, schema ∈ remaining -> schema ∈ E.theory.schemas) ->
      Result (List (SchemaDerivation E))
    | [], _ => pure []
    | schema :: rest, included => do
        let evidence ← buildFormulaEvidence E schema.objects [] schema.conclusion
        let member := included schema (by simp)
        let head : SchemaDerivation E :=
          { schema, member,
            derivation := .schema evidence member (.exact schema) }
        let tail ← go rest (fun candidate candidateMember =>
          included candidate (by simp [candidateMember]))
        pure (head :: tail)
  go E.theory.schemas (fun _ member => member)

/-- Runnable entry point for the Windows checkout through WSL. -/
def quoteSetFile (repositoryRoot : String) : ExceptT String IO Env := do
  let file := repositoryRoot ++ "/ma1/set.cor"
  let loaded ← (CoreFile.load [repositoryRoot ++ "/ma1"] file).run
  let native ← match loaded with
    | .ok native => pure native
    | .error error => throw s!"load: {repr error}"
  match quoteCheckedSetEnv native with
  | .ok quoted => pure quoted
  | .error error => throw s!"quote: {repr error}"

end ContextualHOL.ProgramC.SetTheoryQuote
