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

def oldCtx : String := "(X × (X × Final))"
def newCtx : String := "(X × Final)"
def map : String := "(smap X s)"
def tailPair : String :=
  "(pair (X × Final) X Final (Cart.weakening X (X × Final) s) (snd X Final))"

def atomSource (rel constName : String) : String :=
  "(sub2 (X × (X × Final)) X X " ++ rel ++
  " (v0 X (X × Final)) " ++
  "(Cart.weakening X (X × (X × Final)) " ++ constName ++ "))"

def atomReindexed (rel constName : String) : String :=
  "(sub2 (X × Final) X X " ++ rel ++
  " ((v0 X (X × Final)) ∘ smap X s) " ++
  "((Cart.weakening X (X × (X × Final)) " ++ constName ++ ") ∘ smap X s))"

def atomFstClean (rel constName : String) : String :=
  "(sub2 (X × Final) X X " ++ rel ++
  " (v0 X Final) " ++
  "((Cart.weakening X (X × (X × Final)) " ++ constName ++ ") ∘ smap X s))"

def atomClean (rel constName : String) : String :=
  "(sub2 (X × Final) X X " ++ rel ++
  " (v0 X Final) " ++
  "(Cart.weakening X (X × Final) " ++ constName ++ "))"

def atomSub2Reindex (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallSub2ReindexBeta [
    Arg.ty "X",
    Arg.ty oldCtx,
    Arg.ty "X",
    Arg.ty "X",
    Arg.pred rel,
    Arg.term "(v0 X (X × Final))",
    Arg.term ("(Cart.weakening X (X × (X × Final)) " ++ constName ++ ")"),
    Arg.term map
  ]

def atomFstBeta (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairBetaLeft [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "(X × Final)",
    Arg.ty "X",
    Arg.pred rel,
    Arg.term "(v0 X Final)",
    Arg.term tailPair,
    Arg.term ("((Cart.weakening X (X × (X × Final)) " ++ constName ++ ") ∘ smap X s)")
  ]

def atomConstBeta (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallConstCompBetaRight [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty oldCtx,
    Arg.pred rel,
    Arg.term "(v0 X Final)",
    Arg.term constName,
    Arg.term map
  ]

def atomEvidence (rel constName : String) : ForallCert :=
  let source := atomSource rel constName
  let reindexed := atomReindexed rel constName
  let fstClean := atomFstClean rel constName
  let clean := atomClean rel constName
  let tail :=
    Evidence.Proof.call BasisName.forallIffTransApply [
      Arg.ty "X",
      Arg.pred reindexed,
      Arg.pred fstClean,
      Arg.pred clean
    ] [atomFstBeta rel constName, atomConstBeta rel constName]
  { source := source
    original := comp source map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [atomSub2Reindex rel constName, tail] }

def pappSource (pred : String) : String :=
  parens (pred ++ " ∘ (v0 X (X × Final))")

def pappReindexed (pred : String) : String :=
  parens (pred ++ " ∘ ((v0 X (X × Final)) ∘ smap X s)")

def pappClean (pred : String) : String :=
  parens (pred ++ " ∘ (v0 X Final)")

def pappEvidence (pred : String) : ForallCert :=
  let source := pappSource pred
  let reindexed := pappReindexed pred
  let clean := pappClean pred
  { source := source
    original := comp source map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [
        Evidence.Proof.basis BasisName.forallUnaryReindexBeta [
          Arg.ty "X",
          Arg.ty oldCtx,
          Arg.ty "X",
          Arg.pred pred,
          Arg.term "(v0 X (X × Final))",
          Arg.term map
        ],
        Evidence.Proof.basis BasisName.forallFstPairUnaryBetaGrouped [
          Arg.ty "X",
          Arg.ty "X",
          Arg.ty "(X × Final)",
          Arg.pred pred,
          Arg.term "(v0 X Final)",
          Arg.term tailPair
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

def binaryEvidence (kind : BinaryKind) (left right : ForallCert) : ForallCert :=
  let source := binaryPred kind oldCtx left.source right.source
  let reindexed := binaryPred kind newCtx left.original right.original
  let clean := binaryPred kind newCtx left.clean right.clean
  let reindex :=
    Evidence.Proof.basis kind.reindexName [
      Arg.ty "X",
      Arg.ty oldCtx,
      Arg.term map,
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
    original := comp source map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [reindex, cong] }

def notEvidence (child : ForallCert) : ForallCert :=
  let source := parens ("Pred.not " ++ oldCtx ++ " " ++ child.source)
  let reindexed := parens ("Pred.not " ++ newCtx ++ " " ++ child.original)
  let clean := parens ("Pred.not " ++ newCtx ++ " " ++ child.clean)
  let reindex :=
    Evidence.Proof.basis BasisName.forallNotReindexBeta [
      Arg.ty "X",
      Arg.ty oldCtx,
      Arg.term map,
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
    original := comp source map
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred (comp source map),
        Arg.pred reindexed,
        Arg.pred clean
      ] [reindex, cong] }

partial def buildSmapSubstEvidence? : Formula -> Option ForallCert
  | Formula.atom "R" (Term.var "w") (Term.const constName) =>
      some (atomEvidence "R" constName)
  | Formula.papp "phi" (Term.var "w") =>
      some (pappEvidence "phi")
  | Formula.and left right => do
      pure (binaryEvidence BinaryKind.and (<- buildSmapSubstEvidence? left) (<- buildSmapSubstEvidence? right))
  | Formula.or left right => do
      pure (binaryEvidence BinaryKind.or (<- buildSmapSubstEvidence? left) (<- buildSmapSubstEvidence? right))
  | Formula.imp left right => do
      pure (binaryEvidence BinaryKind.imp (<- buildSmapSubstEvidence? left) (<- buildSmapSubstEvidence? right))
  | Formula.iff left right => do
      pure (binaryEvidence BinaryKind.iff (<- buildSmapSubstEvidence? left) (<- buildSmapSubstEvidence? right))
  | Formula.not body => do
      pure (notEvidence (<- buildSmapSubstEvidence? body))
  | Formula.atom _ _ _ => none
  | Formula.papp _ _ => none
  | Formula.all _ _ _ => none
  | Formula.ex _ _ _ => none

def buildSubstEvidence? : Formula -> Option ForallCert :=
  buildSmapSubstEvidence?

end SubstEvidenceBuilder

end ContextualHOL
