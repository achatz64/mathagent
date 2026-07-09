import ContextualHOL.Evidence
import ContextualHOL.Syntax

namespace ContextualHOL

namespace SubstEvidenceBuilder

abbrev Proof := Evidence.Proof

namespace Arg

def ty (text : String) : Evidence.Arg := Evidence.Arg.ty text
def term (text : String) : Evidence.Arg := Evidence.Arg.term text
def pred (text : String) : Evidence.Arg := Evidence.Arg.pred text

end Arg

structure ForallCert where
  source : String
  original : String
  clean : String
  proof : Proof
  deriving Repr

def failureCert : ForallCert :=
  { source := "(generation_failed)"
    original := "(generation_failed)"
    clean := "(generation_failed)"
    proof := Evidence.Proof.rawChecked "(generation_failed)" [] }

def parens (text : String) : String :=
  "(" ++ text ++ ")"

def comp (pred map : String) : String :=
  parens (pred ++ " ∘ " ++ map)

structure SubstShape where
  oldCtx : String
  newCtx : String
  map : String
  oldVar : String
  cleanVar : String
  pairRightTy : String
  tailPair : String
  deriving Repr, BEq, DecidableEq

def smapShape : SubstShape :=
  { oldCtx := "(X × (X × Final))"
    newCtx := "(X × Final)"
    map := "(smap X s)"
    oldVar := "(v0 X (X × Final))"
    cleanVar := "(v0 X Final)"
    pairRightTy := "(X × Final)"
    tailPair := "(pair (X × Final) X Final (Cart.weakening X (X × Final) s) (snd X Final))" }

def atomSource (shape : SubstShape) (rel constName : String) : String :=
  "(sub2 " ++ shape.oldCtx ++ " X X " ++ rel ++ " " ++ shape.oldVar ++ " " ++
  "(Cart.weakening X " ++ shape.oldCtx ++ " " ++ constName ++ "))"

def atomReindexed (shape : SubstShape) (rel constName : String) : String :=
  "(sub2 " ++ shape.newCtx ++ " X X " ++ rel ++ " (" ++ shape.oldVar ++ " ∘ " ++
  shape.map ++ ") " ++
  "((Cart.weakening X " ++ shape.oldCtx ++ " " ++ constName ++ ") ∘ " ++
  shape.map ++ "))"

def atomFstClean (shape : SubstShape) (rel constName : String) : String :=
  "(sub2 " ++ shape.newCtx ++ " X X " ++ rel ++ " " ++ shape.cleanVar ++ " " ++
  "((Cart.weakening X " ++ shape.oldCtx ++ " " ++ constName ++ ") ∘ " ++
  shape.map ++ "))"

def atomClean (shape : SubstShape) (rel constName : String) : String :=
  "(sub2 " ++ shape.newCtx ++ " X X " ++ rel ++ " " ++ shape.cleanVar ++ " " ++
  "(Cart.weakening X " ++ shape.newCtx ++ " " ++ constName ++ "))"

def atomSub2Reindex (shape : SubstShape) (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallSub2ReindexBeta [
    Arg.ty "X",
    Arg.ty shape.oldCtx,
    Arg.ty "X",
    Arg.ty "X",
    Arg.pred rel,
    Arg.term shape.oldVar,
    Arg.term ("(Cart.weakening X " ++ shape.oldCtx ++ " " ++ constName ++ ")"),
    Arg.term shape.map
  ]

def atomFstBeta (shape : SubstShape) (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairBetaLeft [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty shape.pairRightTy,
    Arg.ty "X",
    Arg.pred rel,
    Arg.term shape.cleanVar,
    Arg.term shape.tailPair,
    Arg.term ("((Cart.weakening X " ++ shape.oldCtx ++ " " ++ constName ++ ") ∘ " ++
      shape.map ++ ")")
  ]

def atomConstBeta (shape : SubstShape) (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallConstCompBetaRight [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty shape.oldCtx,
    Arg.pred rel,
    Arg.term shape.cleanVar,
    Arg.term constName,
    Arg.term shape.map
  ]

def atomEvidence (shape : SubstShape) (rel constName : String) : ForallCert :=
  let source := atomSource shape rel constName
  let reindexed := atomReindexed shape rel constName
  let fstClean := atomFstClean shape rel constName
  let clean := atomClean shape rel constName
  let tail :=
    Evidence.Proof.call BasisName.forallIffTransApply [
      Arg.ty "X",
      Arg.pred reindexed,
      Arg.pred fstClean,
      Arg.pred clean
    ] [atomFstBeta shape rel constName, atomConstBeta shape rel constName]
  { source := source
    original := comp source shape.map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source shape.map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [atomSub2Reindex shape rel constName, tail] }

def pappSource (shape : SubstShape) (pred : String) : String :=
  parens (pred ++ " ∘ " ++ shape.oldVar)

def pappReindexed (shape : SubstShape) (pred : String) : String :=
  parens (pred ++ " ∘ (" ++ shape.oldVar ++ " ∘ " ++ shape.map ++ ")")

def pappClean (shape : SubstShape) (pred : String) : String :=
  parens (pred ++ " ∘ " ++ shape.cleanVar)

def pappEvidence (shape : SubstShape) (pred : String) : ForallCert :=
  let source := pappSource shape pred
  let reindexed := pappReindexed shape pred
  let clean := pappClean shape pred
  { source := source
    original := comp source shape.map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source shape.map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [
        Evidence.Proof.basis BasisName.forallUnaryReindexBeta [
          Arg.ty "X",
          Arg.ty shape.oldCtx,
          Arg.ty "X",
          Arg.pred pred,
          Arg.term shape.oldVar,
          Arg.term shape.map
        ],
        Evidence.Proof.basis BasisName.forallFstPairUnaryBetaGrouped [
          Arg.ty "X",
          Arg.ty "X",
          Arg.ty shape.pairRightTy,
          Arg.pred pred,
          Arg.term shape.cleanVar,
          Arg.term shape.tailPair
        ]
      ] }

inductive BinaryKind where
  | and
  | or
  | imp
  | iff

namespace BinaryKind

def predName : BinaryKind -> String
  | and => "Pred.and"
  | or => "Pred.or"
  | imp => "Pred.imply"
  | iff => "Pred.iff"

def reindexName : BinaryKind -> BasisName
  | and => BasisName.forallAndReindexBeta
  | or => BasisName.forallOrReindexBeta
  | imp => BasisName.forallImpReindexBeta
  | iff => BasisName.forallIffReindexBeta

def congName : BinaryKind -> BasisName
  | and => BasisName.forallAndCong
  | or => BasisName.forallOrCong
  | imp => BasisName.forallImpCong
  | iff => BasisName.forallIffCong

end BinaryKind

def binaryPred (kind : BinaryKind) (ctx left right : String) : String :=
  parens (kind.predName ++ " " ++ ctx ++ " " ++ left ++ " " ++ right)

def binaryEvidence (shape : SubstShape) (kind : BinaryKind) (left right : ForallCert) : ForallCert :=
  let source := binaryPred kind shape.oldCtx left.source right.source
  let reindexed := binaryPred kind shape.newCtx left.original right.original
  let clean := binaryPred kind shape.newCtx left.clean right.clean
  let reindex :=
    Evidence.Proof.basis kind.reindexName [
      Arg.ty "X",
      Arg.ty shape.oldCtx,
      Arg.term shape.map,
      Arg.pred left.source,
      Arg.pred right.source
    ]
  let cong :=
    Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.implyElim "_" "_"
        (Evidence.Proof.basis kind.congName [
          Arg.ty "X",
          Arg.pred left.original,
          Arg.pred left.clean,
          Arg.pred right.original,
          Arg.pred right.clean
        ])
        left.proof)
      right.proof
  { source := source
    original := comp source shape.map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source shape.map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [reindex, cong] }

def notEvidence (shape : SubstShape) (child : ForallCert) : ForallCert :=
  let source := parens ("Pred.not " ++ shape.oldCtx ++ " " ++ child.source)
  let reindexed := parens ("Pred.not " ++ shape.newCtx ++ " " ++ child.original)
  let clean := parens ("Pred.not " ++ shape.newCtx ++ " " ++ child.clean)
  let reindex :=
    Evidence.Proof.basis BasisName.forallNotReindexBeta [
      Arg.ty "X",
      Arg.ty shape.oldCtx,
      Arg.term shape.map,
      Arg.pred child.source
    ]
  let cong :=
    Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallNotCong [
        Arg.ty "X",
        Arg.pred child.original,
        Arg.pred child.clean
      ])
      child.proof
  { source := source
    original := comp source shape.map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source shape.map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [reindex, cong] }

partial def buildSubstEvidenceWith? (shape : SubstShape) : Formula -> Option ForallCert
  | Formula.atom "R" (Term.var "w") (Term.const constName) =>
      some (atomEvidence shape "R" constName)
  | Formula.papp "phi" (Term.var "w") =>
      some (pappEvidence shape "phi")
  | Formula.and left right => do
      pure (binaryEvidence shape BinaryKind.and
        (<- buildSubstEvidenceWith? shape left)
        (<- buildSubstEvidenceWith? shape right))
  | Formula.or left right => do
      pure (binaryEvidence shape BinaryKind.or
        (<- buildSubstEvidenceWith? shape left)
        (<- buildSubstEvidenceWith? shape right))
  | Formula.imp left right => do
      pure (binaryEvidence shape BinaryKind.imp
        (<- buildSubstEvidenceWith? shape left)
        (<- buildSubstEvidenceWith? shape right))
  | Formula.iff left right => do
      pure (binaryEvidence shape BinaryKind.iff
        (<- buildSubstEvidenceWith? shape left)
        (<- buildSubstEvidenceWith? shape right))
  | Formula.not body => do
      pure (notEvidence shape (<- buildSubstEvidenceWith? shape body))
  | Formula.atom _ _ _ => none
  | Formula.papp _ _ => none
  | Formula.all _ _ _ => none
  | Formula.ex _ _ _ => none

def buildSmapSubstEvidence? : Formula -> Option ForallCert :=
  buildSubstEvidenceWith? smapShape

def buildSubstEvidence? : Formula -> Option ForallCert :=
  buildSmapSubstEvidence?

end SubstEvidenceBuilder

end ContextualHOL
