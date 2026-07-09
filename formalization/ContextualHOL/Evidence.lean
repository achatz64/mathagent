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
  | call : BasisName -> List Arg -> List Proof -> Proof
  | app : Proof -> Proof -> Proof
  | iffTrans : String -> String -> String -> Proof -> Proof -> Proof
  | iffSym : String -> String -> Proof -> Proof
  | implyElim : String -> String -> Proof -> Proof -> Proof
  | rawChecked : String -> List BasisName -> Proof
  deriving Repr

namespace Proof

def basisNames : Proof -> List BasisName
  | basis name _ => [name]
  | call name _ proofs => name :: proofs.foldr (fun proof names => basisNames proof ++ names) []
  | app fn arg => basisNames fn ++ basisNames arg
  | iffTrans _ _ _ left right => BasisName.iffTrans :: basisNames left ++ basisNames right
  | iffSym _ _ proof => BasisName.iffSym :: basisNames proof
  | implyElim _ _ fn arg => BasisName.implyElim :: basisNames fn ++ basisNames arg
  | rawChecked _ names => names

partial def containsRawChecked : Proof -> Bool
  | basis _ _ => false
  | call _ _ proofs => proofs.any containsRawChecked
  | app fn arg => containsRawChecked fn || containsRawChecked arg
  | iffTrans _ _ _ left right => containsRawChecked left || containsRawChecked right
  | iffSym _ _ proof => containsRawChecked proof
  | implyElim _ _ fn arg => containsRawChecked fn || containsRawChecked arg
  | rawChecked _ _ => true

def usesOnlyAllowed (proof : Proof) : Bool :=
  !proof.containsRawChecked &&
    proof.basisNames.all (fun name => BasisName.all.contains name)

def renderArgs (args : List Arg) : String :=
  joinSep " " (args.map (fun arg => arg.text))

partial def render : Proof -> String
  | basis name [] => BasisName.coreName name
  | basis name args => parens (BasisName.coreName name ++ " " ++ renderArgs args)
  | call name args proofs =>
      let renderedArgs := renderArgs args
      let renderedProofs := joinSep " " (proofs.map render)
      let renderedInputs :=
        match renderedArgs, renderedProofs with
        | "", "" => ""
        | "", proofs => " " ++ proofs
        | args, "" => " " ++ args
        | args, proofs => " " ++ args ++ " " ++ proofs
      parens (BasisName.coreName name ++ renderedInputs)
  | app fn arg => parens (render fn ++ " " ++ render arg)
  | iffTrans left middle right first second =>
      parens (BasisName.coreName BasisName.iffTrans ++ " " ++ left ++ " " ++
        middle ++ " " ++ right ++ " " ++
        render first ++ " " ++ render second)
  | iffSym left right proof =>
      parens (BasisName.coreName BasisName.iffSym ++ " " ++ left ++ " " ++
        right ++ " " ++ render proof)
  | implyElim premise conclusion fn arg =>
      parens (BasisName.coreName BasisName.implyElim ++ " " ++ premise ++
        " " ++ conclusion ++ " " ++ render fn ++ " " ++ render arg)
  | rawChecked text _ => text

end Proof

end Evidence

end ContextualHOL
