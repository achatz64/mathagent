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
  IO.FS.writeFile (outputPath args) (Cor.renderFile [reflexive, symmetricStep])
