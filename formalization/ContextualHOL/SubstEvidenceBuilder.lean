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

structure PrefixCert where
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

def ctxReindexName : BinaryKind -> BasisName
  | and => BasisName.forallCtxAndReindexBeta
  | or => BasisName.forallCtxOrReindexBeta
  | imp => BasisName.forallCtxImpReindexBeta
  | iff => BasisName.forallCtxIffReindexBeta

def ctxCongName : BinaryKind -> BasisName
  | and => BasisName.forallCtxAndCong
  | or => BasisName.forallCtxOrCong
  | imp => BasisName.forallCtxImpCong
  | iff => BasisName.forallCtxIffCong

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

def smapPointFunction : String :=
  "(pair X X (X × Final) (Cart.i_comb X) (pair X X Final (Cart.weakening X X s) (Final.bang X)))"

def smapPointLift : String :=
  parens (smapPointFunction ++ " ∘ fst X Final")

def smapQuantTail : String :=
  parens (smapPointFunction ++ " ∘ (fst X Final ∘ snd X (X × Final))")

def smapQuantLift : String :=
  "(pair (X × (X × Final)) X (X × (X × Final)) " ++
  "(fst X (X × Final)) " ++ smapQuantTail ++ ")"

def quantAtomBodySource (rel constName : String) : String :=
  "(sub2 (X × (X × (X × Final))) X X " ++ rel ++
  " (v0 X (X × (X × Final))) " ++
  "(Cart.weakening X (X × (X × (X × Final))) " ++ constName ++ "))"

def forallShellEvidence (rel constName : String) : ForallCert :=
  let body := quantAtomBodySource rel constName
  let source := parens ("Forall X (X × (X × Final)) " ++ body)
  let clean := parens ("Forall X (X × Final) " ++ comp body smapQuantLift)
  { source := source
    original := comp source smapPointLift
    clean := clean
    proof :=
      Evidence.Proof.basis BasisName.forallReindex [
        Arg.ty "X",
        Arg.ty "(X × (X × Final))",
        Arg.ty "X",
        Arg.pred body,
        Arg.term smapPointFunction
      ] }

def existShellEvidence (rel constName : String) : ForallCert :=
  let body := quantAtomBodySource rel constName
  let source := parens ("Exist X (X × (X × Final)) " ++ body)
  let clean := parens ("Exist X (X × Final) " ++ comp body smapQuantLift)
  { source := source
    original := comp source smapPointLift
    clean := clean
    proof :=
      Evidence.Proof.basis BasisName.existReindex [
        Arg.ty "X",
        Arg.ty "(X × (X × Final))",
        Arg.ty "X",
        Arg.pred body,
        Arg.term smapPointFunction
      ] }

def quantAtomBodyReindexed (rel constName : String) : String :=
  "(sub2 (X × (X × Final)) X X " ++ rel ++
  " ((v0 X (X × (X × Final))) ∘ " ++ smapQuantLift ++ ") " ++
  "((Cart.weakening X (X × (X × (X × Final))) " ++ constName ++ ") ∘ " ++
  smapQuantLift ++ "))"

def quantAtomBodyFstClean (rel constName : String) : String :=
  "(sub2 (X × (X × Final)) X X " ++ rel ++
  " (v0 X (X × Final)) " ++
  "((Cart.weakening X (X × (X × (X × Final))) " ++ constName ++ ") ∘ " ++
  smapQuantLift ++ "))"

def quantAtomBodyClean (rel constName : String) : String :=
  "(sub2 (X × (X × Final)) X X " ++ rel ++
  " (v0 X (X × Final)) " ++
  "(Cart.weakening X (X × (X × Final)) " ++ constName ++ "))"

def quantAtomBodySub2Reindex (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallCtxSub2ReindexBeta [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "(X × (X × (X × Final)))",
    Arg.ty "X",
    Arg.ty "X",
    Arg.pred rel,
    Arg.term "(v0 X (X × (X × Final)))",
    Arg.term ("(Cart.weakening X (X × (X × (X × Final))) " ++ constName ++ ")"),
    Arg.term smapQuantLift
  ]

def quantAtomBodyFstBeta (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallCtxFstPairBetaLeft [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "(X × (X × Final))",
    Arg.ty "X",
    Arg.pred rel,
    Arg.term "(v0 X (X × Final))",
    Arg.term smapQuantTail,
    Arg.term ("((Cart.weakening X (X × (X × (X × Final))) " ++ constName ++
      ") ∘ " ++ smapQuantLift ++ ")")
  ]

def quantAtomBodyConstBeta (rel constName : String) : Proof :=
  Evidence.Proof.basis BasisName.forallCtxConstCompBetaRight [
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "X",
    Arg.ty "(X × (X × (X × Final)))",
    Arg.pred rel,
    Arg.term "(v0 X (X × Final))",
    Arg.term constName,
    Arg.term smapQuantLift
  ]

def quantAtomBodyEvidence (rel constName : String) : PrefixCert :=
  let source := quantAtomBodySource rel constName
  let original := comp source smapQuantLift
  let reindexed := quantAtomBodyReindexed rel constName
  let fstClean := quantAtomBodyFstClean rel constName
  let clean := quantAtomBodyClean rel constName
  let tail :=
    Evidence.Proof.call BasisName.forallCtxIffTransApply [
      Arg.ty "X",
      Arg.ty "X",
      Arg.pred reindexed,
      Arg.pred fstClean,
      Arg.pred clean
    ] [quantAtomBodyFstBeta rel constName, quantAtomBodyConstBeta rel constName]
  { source := source
    original := original
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallCtxIffTransApply [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred original,
        Arg.pred reindexed,
        Arg.pred clean
      ] [quantAtomBodySub2Reindex rel constName, tail] }

def quantPappSource (pred : String) : String :=
  parens (pred ++ " ∘ (v0 X (X × (X × Final)))")

def quantPappReindexed (pred : String) : String :=
  parens (pred ++ " ∘ ((v0 X (X × (X × Final))) ∘ " ++ smapQuantLift ++ ")")

def quantPappClean (pred : String) : String :=
  parens (pred ++ " ∘ (v0 X (X × Final))")

def quantPappEvidence (pred : String) : PrefixCert :=
  let source := quantPappSource pred
  let reindexed := quantPappReindexed pred
  let clean := quantPappClean pred
  { source := source
    original := comp source smapQuantLift
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallCtxIffTransApply [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred (comp source smapQuantLift),
        Arg.pred reindexed,
        Arg.pred clean
      ] [
        Evidence.Proof.basis BasisName.forallCtxUnaryReindexBeta [
          Arg.ty "X",
          Arg.ty "X",
          Arg.ty "(X × (X × (X × Final)))",
          Arg.ty "X",
          Arg.pred pred,
          Arg.term "(v0 X (X × (X × Final)))",
          Arg.term smapQuantLift
        ],
        Evidence.Proof.basis BasisName.forallCtxFstPairUnaryBetaGrouped [
          Arg.ty "X",
          Arg.ty "X",
          Arg.ty "X",
          Arg.ty "(X × (X × Final))",
          Arg.pred pred,
          Arg.term "(v0 X (X × Final))",
          Arg.term smapQuantTail
        ]
      ] }

def prefixBinaryEvidence (kind : BinaryKind) (left right : PrefixCert) : PrefixCert :=
  let source :=
    binaryPred kind "(X × (X × (X × Final)))" left.source right.source
  let reindexed :=
    binaryPred kind "(X × (X × Final))" left.original right.original
  let clean :=
    binaryPred kind "(X × (X × Final))" left.clean right.clean
  let reindex :=
    Evidence.Proof.basis kind.ctxReindexName [
      Arg.ty "X",
      Arg.ty "X",
      Arg.ty "(X × (X × (X × Final)))",
      Arg.term smapQuantLift,
      Arg.pred left.source,
      Arg.pred right.source
    ]
  let congruence :=
    Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.implyElim "_" "_"
        (Evidence.Proof.basis kind.ctxCongName [
          Arg.ty "X",
          Arg.ty "X",
          Arg.pred left.original,
          Arg.pred left.clean,
          Arg.pred right.original,
          Arg.pred right.clean
        ])
        left.proof)
      right.proof
  { source := source
    original := comp source smapQuantLift
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallCtxIffTransApply [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred (comp source smapQuantLift),
        Arg.pred reindexed,
        Arg.pred clean
      ] [reindex, congruence] }

def prefixNotEvidence (child : PrefixCert) : PrefixCert :=
  let source := parens ("Pred.not (X × (X × (X × Final))) " ++ child.source)
  let reindexed := parens ("Pred.not (X × (X × Final)) " ++ child.original)
  let clean := parens ("Pred.not (X × (X × Final)) " ++ child.clean)
  let reindex :=
    Evidence.Proof.basis BasisName.forallCtxNotReindexBeta [
      Arg.ty "X",
      Arg.ty "X",
      Arg.ty "(X × (X × (X × Final)))",
      Arg.term smapQuantLift,
      Arg.pred child.source
    ]
  let congruence :=
    Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallCtxNotCong [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred child.original,
        Arg.pred child.clean
      ])
      child.proof
  { source := source
    original := comp source smapQuantLift
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallCtxIffTransApply [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred (comp source smapQuantLift),
        Arg.pred reindexed,
        Arg.pred clean
      ] [reindex, congruence] }

partial def buildSmapPrefixEvidence? (bound : String) : Formula -> Option PrefixCert
  | Formula.atom "R" (Term.var varName) (Term.const constName) =>
      if varName = bound then
        some (quantAtomBodyEvidence "R" constName)
      else
        none
  | Formula.papp "phi" (Term.var varName) =>
      if varName = bound then
        some (quantPappEvidence "phi")
      else
        none
  | Formula.and left right => do
      pure (prefixBinaryEvidence BinaryKind.and
        (<- buildSmapPrefixEvidence? bound left)
        (<- buildSmapPrefixEvidence? bound right))
  | Formula.or left right => do
      pure (prefixBinaryEvidence BinaryKind.or
        (<- buildSmapPrefixEvidence? bound left)
        (<- buildSmapPrefixEvidence? bound right))
  | Formula.imp left right => do
      pure (prefixBinaryEvidence BinaryKind.imp
        (<- buildSmapPrefixEvidence? bound left)
        (<- buildSmapPrefixEvidence? bound right))
  | Formula.iff left right => do
      pure (prefixBinaryEvidence BinaryKind.iff
        (<- buildSmapPrefixEvidence? bound left)
        (<- buildSmapPrefixEvidence? bound right))
  | Formula.not body => do
      pure (prefixNotEvidence (<- buildSmapPrefixEvidence? bound body))
  | Formula.atom _ _ _ => none
  | Formula.papp _ _ => none
  | Formula.all _ _ _ => none
  | Formula.ex _ _ _ => none

def forallShellFromPrefix (body : PrefixCert) : ForallCert :=
  let source := parens ("Forall X (X × (X × Final)) " ++ body.source)
  { source := source
    original := comp source smapPointLift
    clean := parens ("Forall X (X × Final) " ++ body.original)
    proof :=
      Evidence.Proof.basis BasisName.forallReindex [
        Arg.ty "X",
        Arg.ty "(X × (X × Final))",
        Arg.ty "X",
        Arg.pred body.source,
        Arg.term smapPointFunction
      ] }

def existShellFromPrefix (body : PrefixCert) : ForallCert :=
  let source := parens ("Exist X (X × (X × Final)) " ++ body.source)
  { source := source
    original := comp source smapPointLift
    clean := parens ("Exist X (X × Final) " ++ body.original)
    proof :=
      Evidence.Proof.basis BasisName.existReindex [
        Arg.ty "X",
        Arg.ty "(X × (X × Final))",
        Arg.ty "X",
        Arg.pred body.source,
        Arg.term smapPointFunction
      ] }

def forallCleanFromPrefix (body : PrefixCert) : ForallCert :=
  let shell := forallShellFromPrefix body
  let clean := parens ("Forall X (X × Final) " ++ body.clean)
  let congruence :=
    Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallForallCong [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred body.original,
        Arg.pred body.clean
      ])
      body.proof
  { source := shell.source
    original := shell.original
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred shell.original,
        Arg.pred shell.clean,
        Arg.pred clean
      ] [shell.proof, congruence] }

def existCleanFromPrefix (body : PrefixCert) : ForallCert :=
  let shell := existShellFromPrefix body
  let clean := parens ("Exist X (X × Final) " ++ body.clean)
  let congruence :=
    Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallExistCong [
        Arg.ty "X",
        Arg.ty "X",
        Arg.pred body.original,
        Arg.pred body.clean
      ])
      body.proof
  { source := shell.source
    original := shell.original
    clean := clean
    proof :=
      Evidence.Proof.call BasisName.forallIffTransApply [
        Arg.ty "X",
        Arg.pred shell.original,
        Arg.pred shell.clean,
        Arg.pred clean
      ] [shell.proof, congruence] }

def forallCleanEvidence (rel constName : String) : ForallCert :=
  forallCleanFromPrefix (quantAtomBodyEvidence rel constName)

def existCleanEvidence (rel constName : String) : ForallCert :=
  existCleanFromPrefix (quantAtomBodyEvidence rel constName)

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
  | Formula.all bound (Ty.base "X") body =>
      if shape == smapShape then
        Option.map forallCleanFromPrefix (buildSmapPrefixEvidence? bound body)
      else
        none
  | Formula.ex bound (Ty.base "X") body =>
      if shape == smapShape then
        Option.map existCleanFromPrefix (buildSmapPrefixEvidence? bound body)
      else
        none
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
