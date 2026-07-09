import ContextualHOL.BasisMap

namespace ContextualHOL

namespace Evidence

inductive ArgKind where
  | ty
  | term
  | pred
  | prop
  | proof
  deriving Repr, BEq, DecidableEq

structure Arg where
  kind : ArgKind
  text : String
  deriving Repr, BEq, DecidableEq

namespace Arg

def ty (text : String) : Arg :=
  { kind := ArgKind.ty, text := text }

def term (text : String) : Arg :=
  { kind := ArgKind.term, text := text }

def pred (text : String) : Arg :=
  { kind := ArgKind.pred, text := text }

def prop (text : String) : Arg :=
  { kind := ArgKind.prop, text := text }

def proof (text : String) : Arg :=
  { kind := ArgKind.proof, text := text }

end Arg

def parens (text : String) : String :=
  "(" ++ text ++ ")"

def joinSep (sep : String) : List String -> String
  | [] => ""
  | [item] => item
  | item :: rest => item ++ sep ++ joinSep sep rest

inductive Proof where
  | basis : BasisName -> List Arg -> Proof
  | app : Proof -> Proof -> Proof
  | iffTrans : String -> String -> String -> Proof -> Proof -> Proof
  | iffSym : String -> String -> Proof -> Proof
  | implyElim : String -> String -> Proof -> Proof -> Proof
  | rawChecked : String -> List BasisName -> Proof
  deriving Repr

namespace Proof

def basisNames : Proof -> List BasisName
  | basis name _ => [name]
  | app fn arg => basisNames fn ++ basisNames arg
  | iffTrans _ _ _ left right => basisNames left ++ basisNames right
  | iffSym _ _ proof => basisNames proof
  | implyElim _ _ fn arg => basisNames fn ++ basisNames arg
  | rawChecked _ names => names

def usesOnlyAllowed (proof : Proof) : Bool :=
  proof.basisNames.all (fun name => BasisName.all.contains name)

def renderArgs (args : List Arg) : String :=
  joinSep " " (args.map (fun arg => arg.text))

partial def render : Proof -> String
  | basis name [] => BasisName.coreName name
  | basis name args => parens (BasisName.coreName name ++ " " ++ renderArgs args)
  | app fn arg => parens (render fn ++ " " ++ render arg)
  | iffTrans left middle right first second =>
      parens ("iff_trans " ++ left ++ " " ++ middle ++ " " ++ right ++ " " ++
        render first ++ " " ++ render second)
  | iffSym left right proof =>
      parens ("iff_sym " ++ left ++ " " ++ right ++ " " ++ render proof)
  | implyElim premise conclusion fn arg =>
      parens ("imply_elim " ++ premise ++ " " ++ conclusion ++ " " ++
        render fn ++ " " ++ render arg)
  | rawChecked text _ => text

end Proof

end Evidence

end ContextualHOL
