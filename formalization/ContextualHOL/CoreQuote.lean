import ContextualHOL.ProgramC
import CoreChecker.Checker

/-!
# Minimal checked Core-to-Deriv quotation

This module is the first functional Core-to-Deriv boundary. It deliberately
does not contain a raw-Core derivation constructor. A declaration is checked by
the native checker first. Its proposition parameters become object variables,
its proof parameters become assumptions, native axiom instances become generic
theory axioms, proof application becomes `mp`, and proof composition is expanded
through contextual `K` and `S`.

The function returns classified failures for the next beta/refunctionalization
cases. In particular, it does not claim that descriptions or arbitrary
predicate terms have already been quoted.
-/

namespace ContextualHOL.ProgramC.CoreQuote

noncomputable section

noncomputable local instance termShapeDecidableEq : DecidableEq TermShape :=
  Classical.typeDecidableEq _
noncomputable local instance formulaShapeDecidableEq : DecidableEq FormulaShape :=
  Classical.typeDecidableEq _

inductive MissingCase where
  | objectTerm
  | predicateApplication
  | proofProducingObjectFunction
  | descriptionBeta
  | contextualBinderBeta
  deriving Repr, DecidableEq

inductive QuoteError where
  | checker (message : String)
  | hole
  | unknownIdentifier (name : String)
  | expectedProposition (expression : CoreChecker.Expr)
  | expectedProof (expression expected : CoreChecker.Expr)
  | expectedProofArrow (expression type : CoreChecker.Expr)
  | formulaMismatch (actual expected : FormulaShape)
  | missingVariable (name : Name)
  | missingHypothesis (formula : FormulaShape)
  | missingTheoryAxiom (formula : FormulaShape)
  | missingCase (case : MissingCase)
  | declarationHasNoProof (name : String)
  deriving Repr

instance : Nonempty QuoteError := ⟨.hole⟩

abbrev Result (alpha : Type) := Except QuoteError alpha
abbrev CoreLocals := List (String × CoreChecker.Expr)

def CoreLocals.toMap (locals : CoreLocals) : Std.HashMap String CoreChecker.Expr :=
  locals.foldr (fun pair out => out.insert pair.1 pair.2) {}

def CoreLocals.lookup (locals : CoreLocals) (name : String) : Option CoreChecker.Expr :=
  match List.find? (fun pair => pair.1 == name) locals with
  | some pair => some pair.2
  | none => none

def rejectHoles (expression : CoreChecker.Expr) : Result Unit :=
  if expression.hasHole then .error .hole else .ok ()

def infer (env : CoreChecker.Env) (locals : CoreLocals)
    (expression : CoreChecker.Expr) : Result CoreChecker.Expr :=
  match CoreChecker.infer env locals.toMap expression with
  | .ok type => .ok type
  | .error message => .error (.checker message)

def isProofType (env : CoreChecker.Env) (locals : CoreLocals)
    (type : CoreChecker.Expr) : Result Bool := do
  rejectHoles type
  let sort <- infer env locals type
  pure (CoreChecker.n1DefEq env sort .sortProp)

def quoteObjectTyNormalized : CoreChecker.Expr -> Result Ty
  | .sortProp => pure .prop
  | .ident "Final" => pure .final
  | .ident name => pure (.base name)
  | .prod left right => do
      pure (.prod (<- quoteObjectTyNormalized left) (<- quoteObjectTyNormalized right))
  | .arrow left right => do
      pure (.arr (<- quoteObjectTyNormalized left) (<- quoteObjectTyNormalized right))
  | _ => throw (.missingCase .objectTerm)

def quoteObjectTy (env : CoreChecker.Env) (type : CoreChecker.Expr) : Result Ty := do
  rejectHoles type
  quoteObjectTyNormalized (CoreChecker.normalize env type)

def connective? (expression : CoreChecker.Expr) : Option (String × Array CoreChecker.Expr) :=
  let (head, args) := expression.headArgs
  match head with
  | .ident name => some (name, args)
  | _ => none

mutual
  partial def quoteFormula (env : CoreChecker.Env) (locals : CoreLocals)
      (expression0 : CoreChecker.Expr) : Result FormulaShape := do
    rejectHoles expression0
    let expression := CoreChecker.normalize env expression0
    let sort <- infer env locals expression
    unless CoreChecker.n1DefEq env sort .sortProp do
      throw (.expectedProposition expression)
    match expression with
    | .ident name =>
        match locals.lookup name with
        | some localType =>
            if CoreChecker.n1DefEq env localType .sortProp then
              pure (.holds (.var name))
            else throw (.expectedProposition expression)
        | none => throw (.missingCase .predicateApplication)
    | .arrow left right =>
        pure (.imp (<- quoteFormula env locals left) (<- quoteFormula env locals right))
    | _ =>
        match connective? expression with
        | some ("imply", args) => quoteBinary env locals FormulaShape.imp args
        | some ("and", args) => quoteBinary env locals FormulaShape.and args
        | some ("or", args) => quoteBinary env locals FormulaShape.or args
        | some ("not", args) =>
            if sizeEq : args.size = 1 then
              pure (.not (<- quoteFormula env locals args[0]))
            else throw (.expectedProposition expression)
        | _ => throw (.missingCase .predicateApplication)

  partial def quoteBinary (env : CoreChecker.Env) (locals : CoreLocals)
      (constructor : FormulaShape -> FormulaShape -> FormulaShape)
      (args : Array CoreChecker.Expr) : Result FormulaShape := do
    if sizeEq : args.size = 2 then
      pure (constructor (<- quoteFormula env locals args[0])
        (<- quoteFormula env locals args[1]))
    else throw (.expectedProposition (.ident "bad-connective-arity"))
end

inductive ProofPlan where
  | hyp (formula : FormulaShape)
  | theory (formula : FormulaShape)
  | mp (premise conclusion : FormulaShape) (function argument : ProofPlan)
  | comp (premise middle conclusion : FormulaShape) (left right : ProofPlan)
  deriving Repr

def ProofPlan.conclusion : ProofPlan -> FormulaShape
  | .hyp formula => formula
  | .theory formula => formula
  | .mp _ conclusion _ _ => conclusion
  | .comp premise _ conclusion _ _ => .imp premise conclusion

def ProofPlan.axioms : ProofPlan -> List FormulaShape
  | .hyp _ => []
  | .theory formula => [formula]
  | .mp _ _ function argument => function.axioms ++ argument.axioms
  | .comp _ _ _ left right => left.axioms ++ right.axioms

structure QuotedPlan where
  formula : FormulaShape
  plan : ProofPlan
  deriving Repr

instance : Nonempty QuotedPlan :=
  ⟨QuotedPlan.mk default (.hyp default)⟩

def mergePremise (current : ProofPlan) (premise conclusion : FormulaShape)
    (argument : ProofPlan) : ProofPlan :=
  .mp premise conclusion current argument

mutual
  partial def quoteProof (env : CoreChecker.Env) (locals : CoreLocals)
      (expected0 expression0 : CoreChecker.Expr) : Result QuotedPlan := do
    rejectHoles expected0
    rejectHoles expression0
    let expected := CoreChecker.normalize env expected0
    let expression := CoreChecker.normalize env expression0
    let got <- infer env locals expression
    unless CoreChecker.n1DefEq env got expected do
      throw (.expectedProof expression expected)
    unless <- isProofType env locals expected do
      throw (.expectedProposition expected)
    let expectedFormula <- quoteFormula env locals expected
    match expression with
    | .ident name =>
        match locals.lookup name with
        | some localType =>
            unless CoreChecker.n1DefEq env localType expected do
              throw (.expectedProof expression expected)
            pure (QuotedPlan.mk expectedFormula (.hyp expectedFormula))
        | none => quoteAxiom env locals expected expression expectedFormula
    | .app _ _ =>
        let (head, _) := expression.headArgs
        match head with
        | .ident name =>
            match CoreChecker.resolve env locals.toMap name with
            | some (qualified, _) =>
                match env.decls.get? qualified with
                | some declaration =>
                    if declaration.kind == CoreChecker.DeclKind.axiom then
                      quoteAxiom env locals expected expression expectedFormula
                    else quoteApplication env locals expected expression expectedFormula
                | none => quoteApplication env locals expected expression expectedFormula
            | none => quoteApplication env locals expected expression expectedFormula
        | _ => quoteApplication env locals expected expression expectedFormula
    | .comp left right =>
        let leftType := CoreChecker.normalize env (<- infer env locals left)
        let rightType := CoreChecker.normalize env (<- infer env locals right)
        match leftType, rightType with
        | .arrow middle conclusion, .arrow premise middleAgain =>
            unless CoreChecker.n1DefEq env middle middleAgain do
              throw (.expectedProof expression expected)
            let premiseFormula <- quoteFormula env locals premise
            let middleFormula <- quoteFormula env locals middle
            let conclusionFormula <- quoteFormula env locals conclusion
            let quotedLeft <- quoteProof env locals leftType left
            let quotedRight <- quoteProof env locals rightType right
            pure (QuotedPlan.mk (FormulaShape.imp premiseFormula conclusionFormula)
              (.comp premiseFormula middleFormula conclusionFormula
                quotedLeft.plan quotedRight.plan))
        | _, _ => throw (.expectedProofArrow expression expected)
    | _ => throw (.expectedProof expression expected)

  partial def quoteApplication (env : CoreChecker.Env) (locals : CoreLocals)
      (expected expression : CoreChecker.Expr) (expectedFormula : FormulaShape) :
      Result QuotedPlan := do
    match expression with
    | .app function argument =>
        let functionType := CoreChecker.normalize env (<- infer env locals function)
        match functionType with
        | .arrow premise conclusion =>
            unless <- isProofType env locals premise do
              throw (.missingCase .proofProducingObjectFunction)
            unless CoreChecker.n1DefEq env conclusion expected do
              throw (.expectedProof expression expected)
            let premiseFormula <- quoteFormula env locals premise
            let quotedFunction <- quoteProof env locals functionType function
            let quotedArgument <- quoteProof env locals premise argument
            pure (QuotedPlan.mk expectedFormula
              (.mp premiseFormula expectedFormula
                quotedFunction.plan quotedArgument.plan))
        | _ => throw (.expectedProofArrow function functionType)
    | _ => throw (.expectedProof expression expected)

  partial def quoteAxiom (env : CoreChecker.Env) (locals : CoreLocals)
      (expected expression : CoreChecker.Expr) (expectedFormula : FormulaShape) :
      Result QuotedPlan := do
    let (head, args) := expression.headArgs
    let name <- match head with
      | .ident name => pure name
      | _ => throw (.expectedProof expression expected)
    let qualified <- match CoreChecker.resolve env locals.toMap name with
      | some (qualified, _) => pure qualified
      | none => throw (.unknownIdentifier name)
    let declaration <- match env.decls.get? qualified with
      | some declaration => pure declaration
      | none => throw (.unknownIdentifier qualified)
    unless declaration.kind == CoreChecker.DeclKind.axiom do
      throw (.expectedProof expression expected)
    if args.size < declaration.params.size then
      throw (.expectedProof expression expected)
    let mut substitutions : Array (String × CoreChecker.Expr) := #[]
    let mut premises : List QuotedPlan := []
    for i in [0:declaration.params.size] do
      let parameter := declaration.params[i]!
      let argument := args[i]!
      let premiseType := parameter.type.substMany substitutions
      if <- isProofType env locals premiseType then
        premises := premises ++ [<- quoteProof env locals premiseType argument]
      substitutions := substitutions.push (parameter.name, argument)
    let mut resultType := declaration.type.substMany substitutions
    for i in [declaration.params.size:args.size] do
      match CoreChecker.normalize env resultType with
      | .arrow premise conclusion =>
          unless <- isProofType env locals premise do
            throw (.missingCase .proofProducingObjectFunction)
          premises := premises ++ [<- quoteProof env locals premise args[i]!]
          resultType := conclusion
      | _ => throw (.expectedProof expression expected)
    unless CoreChecker.n1DefEq env resultType expected do
      throw (.expectedProof expression expected)
    let premiseFormulas := premises.map QuotedPlan.formula
    let schema := premiseFormulas.foldr FormulaShape.imp expectedFormula
    let mut current : ProofPlan := .theory schema
    let mut remaining := schema
    for premise in premises do
      match remaining with
      | .imp left right =>
          current := mergePremise current left right premise.plan
          remaining := right
      | _ => throw (.expectedProof expression expected)
    pure (QuotedPlan.mk expectedFormula current)
end

abbrev SomeVarEvidence (gamma : Ctx) (name : Name) :=
  Sigma fun type => VarHasType gamma name type

def findVariable (gamma : Ctx) (name : Name) : Result (SomeVarEvidence gamma name) :=
  match gamma with
  | [] => .error (.missingVariable name)
  | binding :: tail =>
      if same : binding.name = name then
        same ▸ .ok (Sigma.mk binding.ty VarHasType.here)
      else
        match findVariable tail name with
        | .error error => .error error
        | .ok (Sigma.mk type evidence) =>
            .ok (Sigma.mk type (VarHasType.there same evidence))

def buildFormulaEvidence (E : Env) (gamma : Ctx) (delta : List FormulaShape) :
    (formula : FormulaShape) -> Result (FormulaEvidenceFor E gamma delta formula)
  | .holds (.var name) => do
      match <- findVariable gamma name with
      | Sigma.mk type evidence =>
          if same : type = .prop then
            pure (.holds (.var (same ▸ evidence)))
          else throw (.missingCase .objectTerm)
  | .holds _ => throw (.missingCase .predicateApplication)
  | .pred _ _ => throw (.missingCase .predicateApplication)
  | .and left right => do
      pure (.and (<- buildFormulaEvidence E gamma delta left)
        (<- buildFormulaEvidence E gamma delta right))
  | .or left right => do
      pure (.or (<- buildFormulaEvidence E gamma delta left)
        (<- buildFormulaEvidence E gamma delta right))
  | .imp left right => do
      pure (.imp (<- buildFormulaEvidence E gamma delta left)
        (<- buildFormulaEvidence E gamma delta right))
  | .iff left right => do
      pure (.iff (<- buildFormulaEvidence E gamma delta left)
        (<- buildFormulaEvidence E gamma delta right))
  | .not formula => do
      pure (.not (<- buildFormulaEvidence E gamma delta formula))
  | .all _ _ _ | .ex _ _ _ => throw (.missingCase .contextualBinderBeta)
  | .hasChar _ _ _ _ _ _ | .existUniqueChar _ _ _ _ _ |
      .hasCharNeg _ _ _ | .existUniqueNeg _ _ =>
      throw (.missingCase .descriptionBeta)

abbrev SomeDeriv (E : Env) (gamma : Ctx) (delta : List FormulaShape) :=
  Sigma fun formula => Deriv E gamma delta formula

def compilePlan (E : Env) (gamma : Ctx) (delta : List FormulaShape) :
    (plan : ProofPlan) -> Result (SomeDeriv E gamma delta)
  | .hyp formula => do
      let evidence <- buildFormulaEvidence E gamma delta formula
      match Classical.propDecidable (List.Mem formula delta) with
      | .isTrue member => pure (Sigma.mk formula (.hyp evidence member))
      | .isFalse _ => throw (.missingHypothesis formula)
  | .theory formula => do
      let evidence <- buildFormulaEvidence E gamma delta formula
      match Classical.propDecidable (List.Mem formula E.axioms) with
      | .isTrue member => pure (Sigma.mk formula (.theory evidence member))
      | .isFalse _ => throw (.missingTheoryAxiom formula)
  | .mp premise conclusion function argument => do
      match <- compilePlan E gamma delta function with
      | Sigma.mk functionFormula functionDeriv =>
          match <- compilePlan E gamma delta argument with
          | Sigma.mk argumentFormula argumentDeriv =>
              if functionEq : functionFormula = .imp premise conclusion then
                if argumentEq : argumentFormula = premise then
                  let premiseEvidence <- buildFormulaEvidence E gamma delta premise
                  let conclusionEvidence <- buildFormulaEvidence E gamma delta conclusion
                  pure (Sigma.mk conclusion (.mp premiseEvidence conclusionEvidence
                    (functionEq ▸ functionDeriv) (argumentEq ▸ argumentDeriv)))
                else throw (.formulaMismatch argumentFormula premise)
              else throw (.formulaMismatch functionFormula (.imp premise conclusion))
  | .comp premise middle conclusion left right => do
      match <- compilePlan E gamma delta left with
      | Sigma.mk leftFormula leftDeriv =>
          match <- compilePlan E gamma delta right with
          | Sigma.mk rightFormula rightDeriv =>
              if leftEq : leftFormula = .imp middle conclusion then
                if rightEq : rightFormula = .imp premise middle then
                  let hp <- buildFormulaEvidence E gamma delta premise
                  let hm <- buildFormulaEvidence E gamma delta middle
                  let hc <- buildFormulaEvidence E gamma delta conclusion
                  let liftedLeft := DerivRaw.mp
                    (FormulaEvidence.imp hm hc)
                    (FormulaEvidence.imp hp (FormulaEvidence.imp hm hc))
                    (DerivRaw.axK (FormulaEvidence.imp hm hc) hp)
                    (leftEq ▸ leftDeriv)
                  let sApplied := DerivRaw.mp
                    (FormulaEvidence.imp hp (FormulaEvidence.imp hm hc))
                    (FormulaEvidence.imp (FormulaEvidence.imp hp hm)
                      (FormulaEvidence.imp hp hc))
                    (DerivRaw.axS hp hm hc) liftedLeft
                  let result := DerivRaw.mp
                    (FormulaEvidence.imp hp hm) (FormulaEvidence.imp hp hc)
                    sApplied (rightEq ▸ rightDeriv)
                  pure (Sigma.mk (.imp premise conclusion) result)
                else throw (.formulaMismatch rightFormula (.imp premise middle))
              else throw (.formulaMismatch leftFormula (.imp middle conclusion))

structure ParameterQuote where
  locals : CoreLocals
  gamma : Ctx
  delta : List FormulaShape
  deriving Repr

def quoteParameters (env : CoreChecker.Env)
    (parameters : Array CoreChecker.Param) : Result ParameterQuote := do
  let mut locals : CoreLocals := []
  let mut gamma : Ctx := []
  let mut delta : List FormulaShape := []
  for parameter in parameters do
    if CoreChecker.n1DefEq env parameter.type .sortType then
      pure ()
    else if <- isProofType env locals parameter.type then
      delta := (<- quoteFormula env locals parameter.type) :: delta
    else
      let type <- quoteObjectTy env parameter.type
      gamma := { name := parameter.name, ty := type } :: gamma
    locals := (parameter.name, parameter.type) :: locals
  pure (ParameterQuote.mk locals gamma delta)

structure QuotedDeriv where
  sourceName : String
  coreType : CoreChecker.Expr
  coreBody : CoreChecker.Expr
  E : Env
  gamma : Ctx
  delta : List FormulaShape
  formula : FormulaShape
  derivation : Deriv E gamma delta formula

def quoteCheckedDecl (nativeEnv : CoreChecker.Env)
    (declaration : CoreChecker.Decl) : Result QuotedDeriv := do
  let checked <- match CoreChecker.checkDecl nativeEnv declaration with
    | .ok checked => pure checked
    | .error message => throw (.checker message)
  let body <- match checked.body with
    | some body => pure body
    | none => throw (.declarationHasNoProof checked.name)
  let parameters <- quoteParameters nativeEnv checked.params
  let quoted <- quoteProof nativeEnv parameters.locals checked.type body
  let axioms := quoted.plan.axioms
  let E : Env := { signature := { functions := [], predicates := [] }, axioms }
  match <- compilePlan E parameters.gamma parameters.delta quoted.plan with
  | Sigma.mk formula derivation =>
      if same : formula = quoted.formula then
        pure (QuotedDeriv.mk checked.name checked.type body E
          parameters.gamma parameters.delta quoted.formula (same ▸ derivation))
      else throw (.formulaMismatch formula quoted.formula)

namespace Examples

def identityDecl : CoreChecker.Decl where
  name := "identityProof"
  kind := .defn
  params := #[{ name := "P", type := .sortProp },
    { name := "h", type := .ident "P" }]
  type := .ident "P"
  body := some (.ident "h")

/-- A concrete invocation of the checked Core-to-Deriv function. -/
noncomputable def identityQuote : Result QuotedDeriv :=
  quoteCheckedDecl {} identityDecl

end Examples

end

end ContextualHOL.ProgramC.CoreQuote
