import ContextualHOL.CorePrinter

open ContextualHOL

def U : Ty :=
  Ty.base "U"

def reflexiveEnv : Env :=
  { rels := [("R", { left := U, right := U })] }

def reflexiveSeq : Sequent :=
  { objectCtx := [{ name := "x", ty := U }]
    assumptions := []
    conclusion := Formula.atom "R" (Term.var "x") (Term.var "x") }

def symmetricStepSeq : Sequent :=
  { objectCtx := [{ name := "x", ty := U }, { name := "y", ty := U }]
    assumptions := [Formula.atom "R" (Term.var "x") (Term.var "y")]
    conclusion := Formula.atom "R" (Term.var "y") (Term.var "x") }

def setsTy : Ty :=
  Ty.base "Sets"

-- set.cor's memCong_left_all:  schema b z; object a; assume SetEq(a,b);
-- show a∈z ↔ b∈z.  Closes as  Pred.term (Forall Sets Final (memCongBody b z)).
def memCongEnv : Env :=
  { consts := [("b", setsTy), ("z", setsTy)]
    rels := [("Elem", { left := setsTy, right := setsTy }),
             ("SetEq", { left := setsTy, right := setsTy })] }

def memCongSeq : Sequent :=
  { objectCtx := [{ name := "a", ty := setsTy }]
    assumptions := [Formula.atom "SetEq" (Term.var "a") (Term.const "b")]
    conclusion := Formula.iff
      (Formula.atom "Elem" (Term.var "a") (Term.const "z"))
      (Formula.atom "Elem" (Term.const "b") (Term.const "z")) }

-- set.cor's separation:  schema A, phi; closed formula ∃B. ∀x. (x∈B ↔ (x∈A ∧ φ x)).
-- The φ-slot exercises Formula.papp.
def sepEnv : Env :=
  { consts := [("A", setsTy)]
    preds := [("phi", setsTy)]
    rels := [("Elem", { left := setsTy, right := setsTy })] }

def sepSeq : Sequent :=
  { objectCtx := []
    assumptions := []
    conclusion := Formula.ex "B" setsTy (Formula.all "x" setsTy
      (Formula.iff
        (Formula.atom "Elem" (Term.var "x") (Term.var "B"))
        (Formula.and
          (Formula.atom "Elem" (Term.var "x") (Term.const "A"))
          (Formula.papp "phi" (Term.var "x"))))) }

def renderOrFail (result : Except String String) : IO String :=
  match result with
  | Except.ok text => pure text
  | Except.error err => throw (IO.userError err)

def outputPath (args : List String) : System.FilePath :=
  match args with
  | path :: _ => System.FilePath.mk path
  | [] => System.FilePath.mk "/home/andre/mathagent/ma1/generated_contextual_hol_examples.cor"

def main (args : List String) : IO Unit := do
  let reflexive <- renderOrFail <|
    Cor.renderAxiom "generated_reflexive_schema" reflexiveEnv reflexiveSeq
  let symmetricStep <- renderOrFail <|
    Cor.renderAxiom "generated_symmetric_step_schema" reflexiveEnv symmetricStepSeq
  let memCong <- renderOrFail <|
    Cor.renderAxiom "generated_memCong_left_all" memCongEnv memCongSeq
  let separation <- renderOrFail <|
    Cor.renderAxiom "generated_separation" sepEnv sepSeq
  IO.FS.writeFile (outputPath args)
    (Cor.renderFile [reflexive, symmetricStep, memCong, separation])
