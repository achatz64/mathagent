import ContextualHOL.SubstEvidenceBuilder

open ContextualHOL

namespace ContextualHOL
namespace BasisDerivations

abbrev Arg := Evidence.Arg
abbrev Proof := Evidence.Proof
abbrev ForallCert := SubstEvidenceBuilder.ForallCert

def requireCert (result : Option ForallCert) : ForallCert :=
  match result with
  | some cert => cert
  | none => SubstEvidenceBuilder.failureCert

def betaSub2PointMem : Proof :=
  Evidence.Proof.basis BasisName.betaSub2Point [
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "elt",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(Cart.weakening X (X × Final) s)",
    Evidence.Arg.term "(pointAt X t)"
  ]

def betaV0PointMem : Proof :=
  Evidence.Proof.basis BasisName.betaV0PointArg1 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "(curry X X PC elt)",
    Evidence.Arg.term "t",
    Evidence.Arg.term "(Final.term X ((Cart.weakening X (X × Final) s) ∘ pointAt X t))"
  ]

def betaWeakeningMem : Proof :=
  Evidence.Proof.basis BasisName.betaWeakeningArg2 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.pred "(curry X X PC elt)",
    Evidence.Arg.term "t",
    Evidence.Arg.term "s",
    Evidence.Arg.term "(pointAt X t)"
  ]

def memBetaProof : Proof :=
  Evidence.Proof.iffTrans "_" "_" "_" betaSub2PointMem
    (Evidence.Proof.iffTrans "_" "_" "_" betaV0PointMem betaWeakeningMem)

def betaSub2PointMemRev : Proof :=
  Evidence.Proof.basis BasisName.betaSub2Point [
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "elt",
    Evidence.Arg.term "(Cart.weakening X (X × Final) z)",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(pointAt X t)"
  ]

def betaWeakeningMemRev : Proof :=
  Evidence.Proof.basis BasisName.betaWeakeningArg1 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.pred "(curry X X PC elt)",
    Evidence.Arg.term "z",
    Evidence.Arg.term "(Final.term X ((v0 X Final) ∘ pointAt X t))",
    Evidence.Arg.term "(pointAt X t)"
  ]

def betaV0PointMemRev : Proof :=
  Evidence.Proof.basis BasisName.betaV0PointArg2 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "(curry X X PC elt)",
    Evidence.Arg.term "z",
    Evidence.Arg.term "t"
  ]

def memBetaRevProof : Proof :=
  Evidence.Proof.iffTrans "_" "_" "_" betaSub2PointMemRev
    (Evidence.Proof.iffTrans "_" "_" "_" betaWeakeningMemRev betaV0PointMemRev)

def betaSub2PointConstAtom : Proof :=
  Evidence.Proof.basis BasisName.betaSub2Point [
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "elt",
    Evidence.Arg.term "(Cart.weakening X (X × Final) c)",
    Evidence.Arg.term "(Cart.weakening X (X × Final) d)",
    Evidence.Arg.term "(pointAt X t)"
  ]

def betaWeakeningConstAtomLeft : Proof :=
  Evidence.Proof.basis BasisName.betaWeakeningArg1 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.pred "(curry X X PC elt)",
    Evidence.Arg.term "c",
    Evidence.Arg.term "(Final.term X ((Cart.weakening X (X × Final) d) ∘ pointAt X t))",
    Evidence.Arg.term "(pointAt X t)"
  ]

def betaWeakeningConstAtomRight : Proof :=
  Evidence.Proof.basis BasisName.betaWeakeningArg2 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.pred "(curry X X PC elt)",
    Evidence.Arg.term "c",
    Evidence.Arg.term "d",
    Evidence.Arg.term "(pointAt X t)"
  ]

def constAtomBetaProof : Proof :=
  Evidence.Proof.iffTrans "_" "_" "_" betaSub2PointConstAtom
    (Evidence.Proof.iffTrans "_" "_" "_"
      betaWeakeningConstAtomLeft
      betaWeakeningConstAtomRight)

def betaFstPairSepPhi : Proof :=
  Evidence.Proof.basis BasisName.betaFstPairPointUnary [
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.pred "phi",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(pair (X × Final) X Final (Cart.weakening X (X × Final) s) (snd X Final))",
    Evidence.Arg.term "(pointAt X t)"
  ]

def betaV0SepPhi : Proof :=
  Evidence.Proof.basis BasisName.betaV0PointUnary [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "phi",
    Evidence.Arg.term "t"
  ]

def sepPhiBetaProof : Proof :=
  Evidence.Proof.iffTrans "_" "_" "_" betaFstPairSepPhi betaV0SepPhi

def betaSub2PointAtom : Proof :=
  Evidence.Proof.basis BasisName.betaSub2Point [
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X (X × Final))",
    Evidence.Arg.term "(Cart.weakening X (X × (X × Final)) c)",
    Evidence.Arg.term "(smap X s ∘ pointAt X t)"
  ]

def betaWeakeningAtomRight : Proof :=
  Evidence.Proof.basis BasisName.betaWeakeningArg2 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.pred "(curry X X PC R)",
    Evidence.Arg.term "(Final.term X ((v0 X (X × Final)) ∘ (smap X s ∘ pointAt X t)))",
    Evidence.Arg.term "c",
    Evidence.Arg.term "(smap X s ∘ pointAt X t)"
  ]

def betaFstPairAtomLeft : Proof :=
  Evidence.Proof.basis BasisName.betaFstPairPointArg1 [
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "(curry X X PC R)",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(pair (X × Final) X Final (Cart.weakening X (X × Final) s) (snd X Final))",
    Evidence.Arg.term "(pointAt X t)",
    Evidence.Arg.term "c"
  ]

def betaV0AtomLeft : Proof :=
  Evidence.Proof.basis BasisName.betaV0PointArg1 [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "(curry X X PC R)",
    Evidence.Arg.term "t",
    Evidence.Arg.term "c"
  ]

def atomBetaProof : Proof :=
  Evidence.Proof.iffTrans "_" "_" "_" betaSub2PointAtom
    (Evidence.Proof.iffTrans "_" "_" "_" betaWeakeningAtomRight
      (Evidence.Proof.iffTrans "_" "_" "_" betaFstPairAtomLeft betaV0AtomLeft))

def rawSmapAtomFor (name : String) : String :=
  "(sub2 (X × (X × Final)) X X R (v0 X (X × Final)) " ++
  "(Cart.weakening X (X × (X × Final)) " ++ name ++ "))"

def atomSmapOriginalFor (name : String) : String :=
  "(" ++ rawSmapAtomFor name ++ " ∘ smap X s)"

def atomSmapReindexedFor (name : String) : String :=
  "(sub2 (X × Final) X X R " ++
  "((v0 X (X × Final)) ∘ smap X s) " ++
  "((Cart.weakening X (X × (X × Final)) " ++ name ++ ") ∘ smap X s))"

def atomSmapFstCleanFor (name : String) : String :=
  "(sub2 (X × Final) X X R " ++
  "(v0 X Final) " ++
  "((Cart.weakening X (X × (X × Final)) " ++ name ++ ") ∘ smap X s))"

def atomSmapCleanFor (name : String) : String :=
  "(sub2 (X × Final) X X R " ++
  "(v0 X Final) " ++
  "(Cart.weakening X (X × Final) " ++ name ++ "))"

def atomSmapOriginal : String := atomSmapOriginalFor "a"
def atomSmapReindexed : String := atomSmapReindexedFor "a"
def atomSmapFstClean : String := atomSmapFstCleanFor "a"
def atomSmapClean : String := atomSmapCleanFor "a"

def forallAtomSmapSub2ReindexFor (name : String) : Proof :=
  Evidence.Proof.basis BasisName.forallSub2ReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X (X × Final))",
    Evidence.Arg.term ("(Cart.weakening X (X × (X × Final)) " ++ name ++ ")"),
    Evidence.Arg.term "(smap X s)"
  ]

def forallAtomSmapFstCleanFor (name : String) : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairBetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(pair (X × Final) X Final (Cart.weakening X (X × Final) s) (snd X Final))",
    Evidence.Arg.term ("((Cart.weakening X (X × (X × Final)) " ++ name ++ ") ∘ smap X s)")
  ]

def forallAtomSmapConstCleanFor (name : String) : Proof :=
  Evidence.Proof.basis BasisName.forallConstCompBetaRight [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term name,
    Evidence.Arg.term "(smap X s)"
  ]

def forallAtomSmapSub2Reindex : Proof := forallAtomSmapSub2ReindexFor "a"
def forallAtomSmapFstClean : Proof := forallAtomSmapFstCleanFor "a"
def forallAtomSmapConstClean : Proof := forallAtomSmapConstCleanFor "a"

def forallAtomSmapTailFor (name : String) : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred (atomSmapReindexedFor name),
    Evidence.Arg.pred (atomSmapFstCleanFor name),
    Evidence.Arg.pred (atomSmapCleanFor name)
  ] [forallAtomSmapFstCleanFor name, forallAtomSmapConstCleanFor name]

def forallAtomSmapTail : Proof := forallAtomSmapTailFor "a"

def forallAtomSmapCleanProofFor (name : String) : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred (atomSmapOriginalFor name),
    Evidence.Arg.pred (atomSmapReindexedFor name),
    Evidence.Arg.pred (atomSmapCleanFor name)
  ] [forallAtomSmapSub2ReindexFor name, forallAtomSmapTailFor name]

def forallAtomSmapCleanProof : Proof := forallAtomSmapCleanProofFor "a"

def orAtomsOriginal : String :=
  "((Pred.or (X × (X × Final)) " ++
  rawSmapAtomFor "a" ++ " " ++
  rawSmapAtomFor "b" ++ ") ∘ smap X s)"

def orAtomsReindexed : String :=
  "(Pred.or (X × Final) " ++
  atomSmapOriginalFor "a" ++ " " ++
  atomSmapOriginalFor "b" ++ ")"

def orAtomsClean : String :=
  "(Pred.or (X × Final) " ++
  atomSmapCleanFor "a" ++ " " ++
  atomSmapCleanFor "b" ++ ")"

def forallOrAtomsReindex : Proof :=
  Evidence.Proof.basis BasisName.forallOrReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.term "(smap X s)",
    Evidence.Arg.pred (rawSmapAtomFor "a"),
    Evidence.Arg.pred (rawSmapAtomFor "b")
  ]

def forallOrAtomsCong : Proof :=
  Evidence.Proof.implyElim "_" "_"
    (Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallOrCong [
        Evidence.Arg.ty "X",
        Evidence.Arg.pred (atomSmapOriginalFor "a"),
        Evidence.Arg.pred (atomSmapCleanFor "a"),
        Evidence.Arg.pred (atomSmapOriginalFor "b"),
        Evidence.Arg.pred (atomSmapCleanFor "b")
      ])
      (forallAtomSmapCleanProofFor "a"))
    (forallAtomSmapCleanProofFor "b")

def forallOrAtomsCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred orAtomsOriginal,
    Evidence.Arg.pred orAtomsReindexed,
    Evidence.Arg.pred orAtomsClean
  ] [forallOrAtomsReindex, forallOrAtomsCong]

def iffAtomsOriginal : String :=
  "((Pred.iff (X × (X × Final)) " ++
  rawSmapAtomFor "a" ++ " " ++
  rawSmapAtomFor "b" ++ ") ∘ smap X s)"

def iffAtomsReindexed : String :=
  "(Pred.iff (X × Final) " ++
  atomSmapOriginalFor "a" ++ " " ++
  atomSmapOriginalFor "b" ++ ")"

def iffAtomsClean : String :=
  "(Pred.iff (X × Final) " ++
  atomSmapCleanFor "a" ++ " " ++
  atomSmapCleanFor "b" ++ ")"

def forallIffAtomsReindex : Proof :=
  Evidence.Proof.basis BasisName.forallIffReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.term "(smap X s)",
    Evidence.Arg.pred (rawSmapAtomFor "a"),
    Evidence.Arg.pred (rawSmapAtomFor "b")
  ]

def forallIffAtomsCong : Proof :=
  Evidence.Proof.implyElim "_" "_"
    (Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallIffCong [
        Evidence.Arg.ty "X",
        Evidence.Arg.pred (atomSmapOriginalFor "a"),
        Evidence.Arg.pred (atomSmapCleanFor "a"),
        Evidence.Arg.pred (atomSmapOriginalFor "b"),
        Evidence.Arg.pred (atomSmapCleanFor "b")
      ])
      (forallAtomSmapCleanProofFor "a"))
    (forallAtomSmapCleanProofFor "b")

def forallIffAtomsCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred iffAtomsOriginal,
    Evidence.Arg.pred iffAtomsReindexed,
    Evidence.Arg.pred iffAtomsClean
  ] [forallIffAtomsReindex, forallIffAtomsCong]

def exMemPhiMap : String :=
  "(pair (X × Final) X (X × Final) (fst X Final) ((pointAt X c) ∘ snd X Final))"

def exMemPhiRawAtom : String :=
  "(sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (v1 X X Final))"

def exMemPhiAtomOriginal : String :=
  "(" ++ exMemPhiRawAtom ++ " ∘ " ++ exMemPhiMap ++ ")"

def exMemPhiAtomReindexed : String :=
  "(sub2 (X × Final) X X R " ++
  "((v0 X (X × Final)) ∘ " ++ exMemPhiMap ++ ") " ++
  "((v1 X X Final) ∘ " ++ exMemPhiMap ++ "))"

def exMemPhiAtomFstClean : String :=
  "(sub2 (X × Final) X X R " ++
  "(v0 X Final) " ++
  "((v1 X X Final) ∘ " ++ exMemPhiMap ++ "))"

def exMemPhiAtomSndClean : String :=
  "(sub2 (X × Final) X X R " ++
  "(v0 X Final) " ++
  "((fst X Final) ∘ ((pointAt X c) ∘ snd X Final)))"

def exMemPhiAtomPointClean : String :=
  "(sub2 (X × Final) X X R " ++
  "(v0 X Final) " ++
  "((Cart.weakening X Final c) ∘ snd X Final))"

def exMemPhiAtomClean : String :=
  "(memAt X R c)"

def exMemPhiAtomSub2Reindex : Proof :=
  Evidence.Proof.basis BasisName.forallSub2ReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X (X × Final))",
    Evidence.Arg.term "(v1 X X Final)",
    Evidence.Arg.term exMemPhiMap
  ]

def exMemPhiAtomFstBeta : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairBetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "((pointAt X c) ∘ snd X Final)",
    Evidence.Arg.term ("((v1 X X Final) ∘ " ++ exMemPhiMap ++ ")")
  ]

def exMemPhiAtomSndBeta : Proof :=
  Evidence.Proof.basis BasisName.forallSndPairThenBetaRight [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "((pointAt X c) ∘ snd X Final)"
  ]

def exMemPhiAtomPointAtBeta : Proof :=
  Evidence.Proof.basis BasisName.forallPointAtFstBetaRight [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "c",
    Evidence.Arg.term "(snd X Final)"
  ]

def exMemPhiAtomConstBeta : Proof :=
  Evidence.Proof.basis BasisName.forallConstCompBetaRight [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "Final",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "c",
    Evidence.Arg.term "(snd X Final)"
  ]

def exMemPhiAtomPointTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exMemPhiAtomSndClean,
    Evidence.Arg.pred exMemPhiAtomPointClean,
    Evidence.Arg.pred exMemPhiAtomClean
  ] [exMemPhiAtomPointAtBeta, exMemPhiAtomConstBeta]

def exMemPhiAtomSndTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exMemPhiAtomFstClean,
    Evidence.Arg.pred exMemPhiAtomSndClean,
    Evidence.Arg.pred exMemPhiAtomClean
  ] [exMemPhiAtomSndBeta, exMemPhiAtomPointTail]

def exMemPhiAtomFstTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exMemPhiAtomReindexed,
    Evidence.Arg.pred exMemPhiAtomFstClean,
    Evidence.Arg.pred exMemPhiAtomClean
  ] [exMemPhiAtomFstBeta, exMemPhiAtomSndTail]

def exMemPhiAtomCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exMemPhiAtomOriginal,
    Evidence.Arg.pred exMemPhiAtomReindexed,
    Evidence.Arg.pred exMemPhiAtomClean
  ] [exMemPhiAtomSub2Reindex, exMemPhiAtomFstTail]

def exMemPhiRawPhi : String :=
  "(phi ∘ (v0 X (X × Final)))"

def exMemPhiPhiOriginal : String :=
  "(" ++ exMemPhiRawPhi ++ " ∘ " ++ exMemPhiMap ++ ")"

def exMemPhiPhiReindexed : String :=
  "(phi ∘ ((v0 X (X × Final)) ∘ " ++ exMemPhiMap ++ "))"

def exMemPhiPhiClean : String :=
  "(phi ∘ (v0 X Final))"

def exMemPhiPhiReindex : Proof :=
  Evidence.Proof.basis BasisName.forallUnaryReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "phi",
    Evidence.Arg.term "(v0 X (X × Final))",
    Evidence.Arg.term exMemPhiMap
  ]

def exMemPhiPhiFstBeta : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairUnaryBetaGrouped [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.pred "phi",
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "((pointAt X c) ∘ snd X Final)"
  ]

def exMemPhiPhiCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exMemPhiPhiOriginal,
    Evidence.Arg.pred exMemPhiPhiReindexed,
    Evidence.Arg.pred exMemPhiPhiClean
  ] [exMemPhiPhiReindex, exMemPhiPhiFstBeta]

def exMemPhiAndOriginal : String :=
  "((Pred.and (X × (X × Final)) " ++ exMemPhiRawAtom ++ " " ++
  exMemPhiRawPhi ++ ") ∘ " ++ exMemPhiMap ++ ")"

def exMemPhiAndReindexed : String :=
  "(Pred.and (X × Final) " ++ exMemPhiAtomOriginal ++ " " ++
  exMemPhiPhiOriginal ++ ")"

def exMemPhiAndClean : String :=
  "(Pred.and (X × Final) " ++ exMemPhiAtomClean ++ " " ++
  exMemPhiPhiClean ++ ")"

def exMemPhiAndReindex : Proof :=
  Evidence.Proof.basis BasisName.forallAndReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.term exMemPhiMap,
    Evidence.Arg.pred exMemPhiRawAtom,
    Evidence.Arg.pred exMemPhiRawPhi
  ]

def exMemPhiAndCong : Proof :=
  Evidence.Proof.implyElim "_" "_"
    (Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallAndCong [
        Evidence.Arg.ty "X",
        Evidence.Arg.pred exMemPhiAtomOriginal,
        Evidence.Arg.pred exMemPhiAtomClean,
        Evidence.Arg.pred exMemPhiPhiOriginal,
        Evidence.Arg.pred exMemPhiPhiClean
      ])
      exMemPhiAtomCleanProof)
    exMemPhiPhiCleanProof

def exMemPhiCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exMemPhiAndOriginal,
    Evidence.Arg.pred exMemPhiAndReindexed,
    Evidence.Arg.pred exMemPhiAndClean
  ] [exMemPhiAndReindex, exMemPhiAndCong]

def exUnionMap : String :=
  "(pair (X × Final) X (X × (X × Final)) (fst X Final) ((smap X U ∘ pointAt X z) ∘ snd X Final))"

def exUnionRawLeft : String :=
  "(sub2 (X × (X × (X × Final))) X X R " ++
  "(v0 X (X × (X × Final))) " ++
  "(Cart.weakening X (X × (X × (X × Final))) A))"

def exUnionLeftOriginal : String :=
  "(" ++ exUnionRawLeft ++ " ∘ " ++ exUnionMap ++ ")"

def exUnionLeftReindexed : String :=
  "(sub2 (X × Final) X X R " ++
  "((v0 X (X × (X × Final))) ∘ " ++ exUnionMap ++ ") " ++
  "((Cart.weakening X (X × (X × (X × Final))) A) ∘ " ++ exUnionMap ++ "))"

def exUnionLeftFstClean : String :=
  "(sub2 (X × Final) X X R " ++
  "(v0 X Final) " ++
  "((Cart.weakening X (X × (X × (X × Final))) A) ∘ " ++ exUnionMap ++ "))"

def exUnionLeftClean : String :=
  "(memAt X R A)"

def exUnionLeftSub2Reindex : Proof :=
  Evidence.Proof.basis BasisName.forallSub2ReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × (X × Final)))",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X (X × (X × Final)))",
    Evidence.Arg.term "(Cart.weakening X (X × (X × (X × Final))) A)",
    Evidence.Arg.term exUnionMap
  ]

def exUnionLeftFstBeta : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairBetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "((smap X U ∘ pointAt X z) ∘ snd X Final)",
    Evidence.Arg.term ("((Cart.weakening X (X × (X × (X × Final))) A) ∘ " ++ exUnionMap ++ ")")
  ]

def exUnionLeftConstBeta : Proof :=
  Evidence.Proof.basis BasisName.forallConstCompBetaRight [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × (X × Final)))",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "A",
    Evidence.Arg.term exUnionMap
  ]

def exUnionLeftTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionLeftReindexed,
    Evidence.Arg.pred exUnionLeftFstClean,
    Evidence.Arg.pred exUnionLeftClean
  ] [exUnionLeftFstBeta, exUnionLeftConstBeta]

def exUnionLeftCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionLeftOriginal,
    Evidence.Arg.pred exUnionLeftReindexed,
    Evidence.Arg.pred exUnionLeftClean
  ] [exUnionLeftSub2Reindex, exUnionLeftTail]

def exUnionRawRight : String :=
  "(sub2 (X × (X × (X × Final))) X X R " ++
  "(v1 X X (X × Final)) " ++
  "(v0 X (X × (X × Final))))"

def exUnionRightOriginal : String :=
  "(" ++ exUnionRawRight ++ " ∘ " ++ exUnionMap ++ ")"

def exUnionRightReindexed : String :=
  "(sub2 (X × Final) X X R " ++
  "((v1 X X (X × Final)) ∘ " ++ exUnionMap ++ ") " ++
  "((v0 X (X × (X × Final))) ∘ " ++ exUnionMap ++ "))"

def exUnionRightSlotClean : String :=
  "(sub2 (X × Final) X X R " ++
  "((v1 X X (X × Final)) ∘ " ++ exUnionMap ++ ") " ++
  "(v0 X Final))"

def exUnionRightSndClean : String :=
  "(sub2 (X × Final) X X R " ++
  "((fst X (X × Final)) ∘ ((smap X U ∘ pointAt X z) ∘ snd X Final)) " ++
  "(v0 X Final))"

def exUnionRightSmapClean : String :=
  "(sub2 (X × Final) X X R " ++
  "((v0 X Final) ∘ ((pointAt X z) ∘ snd X Final)) " ++
  "(v0 X Final))"

def exUnionRightPointClean : String :=
  "(sub2 (X × Final) X X R " ++
  "((Cart.weakening X Final z) ∘ snd X Final) " ++
  "(v0 X Final))"

def exUnionRightClean : String :=
  "(sub2 (X × Final) X X R (Cart.weakening X (X × Final) z) (v0 X Final))"

def exUnionRightSub2Reindex : Proof :=
  Evidence.Proof.basis BasisName.forallSub2ReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × (X × Final)))",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v1 X X (X × Final))",
    Evidence.Arg.term "(v0 X (X × (X × Final)))",
    Evidence.Arg.term exUnionMap
  ]

def exUnionRightFstPairRight : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairBetaRight [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term ("((v1 X X (X × Final)) ∘ " ++ exUnionMap ++ ")"),
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "((smap X U ∘ pointAt X z) ∘ snd X Final)"
  ]

def exUnionRightSndPairLeft : Proof :=
  Evidence.Proof.basis BasisName.forallSndPairThenBetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × Final))",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(fst X (X × Final))",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(fst X Final)",
    Evidence.Arg.term "((smap X U ∘ pointAt X z) ∘ snd X Final)"
  ]

def exUnionRightFstPairComp2 : Proof :=
  Evidence.Proof.basis BasisName.forallFstPairComp2BetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "Final",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × Final)",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(pair (X × Final) X Final (Cart.weakening X (X × Final) U) (snd X Final))",
    Evidence.Arg.term "(pointAt X z)",
    Evidence.Arg.term "(snd X Final)",
    Evidence.Arg.term "(v0 X Final)"
  ]

def exUnionRightPointAtFst : Proof :=
  Evidence.Proof.basis BasisName.forallPointAtFstBetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "z",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(snd X Final)"
  ]

def exUnionRightConstComp : Proof :=
  Evidence.Proof.basis BasisName.forallConstCompBetaLeft [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "Final",
    Evidence.Arg.pred "R",
    Evidence.Arg.term "z",
    Evidence.Arg.term "(v0 X Final)",
    Evidence.Arg.term "(snd X Final)"
  ]

def exUnionRightPointTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionRightSmapClean,
    Evidence.Arg.pred exUnionRightPointClean,
    Evidence.Arg.pred exUnionRightClean
  ] [exUnionRightPointAtFst, exUnionRightConstComp]

def exUnionRightSmapTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionRightSndClean,
    Evidence.Arg.pred exUnionRightSmapClean,
    Evidence.Arg.pred exUnionRightClean
  ] [exUnionRightFstPairComp2, exUnionRightPointTail]

def exUnionRightSndTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionRightSlotClean,
    Evidence.Arg.pred exUnionRightSndClean,
    Evidence.Arg.pred exUnionRightClean
  ] [exUnionRightSndPairLeft, exUnionRightSmapTail]

def exUnionRightFstTail : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionRightReindexed,
    Evidence.Arg.pred exUnionRightSlotClean,
    Evidence.Arg.pred exUnionRightClean
  ] [exUnionRightFstPairRight, exUnionRightSndTail]

def exUnionRightCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionRightOriginal,
    Evidence.Arg.pred exUnionRightReindexed,
    Evidence.Arg.pred exUnionRightClean
  ] [exUnionRightSub2Reindex, exUnionRightFstTail]

def exUnionAndOriginal : String :=
  "((Pred.and (X × (X × (X × Final))) " ++ exUnionRawLeft ++ " " ++
  exUnionRawRight ++ ") ∘ " ++ exUnionMap ++ ")"

def exUnionAndReindexed : String :=
  "(Pred.and (X × Final) " ++ exUnionLeftOriginal ++ " " ++
  exUnionRightOriginal ++ ")"

def exUnionAndClean : String :=
  "(Pred.and (X × Final) " ++ exUnionLeftClean ++ " " ++
  exUnionRightClean ++ ")"

def exUnionAndReindex : Proof :=
  Evidence.Proof.basis BasisName.forallAndReindexBeta [
    Evidence.Arg.ty "X",
    Evidence.Arg.ty "(X × (X × (X × Final)))",
    Evidence.Arg.term exUnionMap,
    Evidence.Arg.pred exUnionRawLeft,
    Evidence.Arg.pred exUnionRawRight
  ]

def exUnionAndCong : Proof :=
  Evidence.Proof.implyElim "_" "_"
    (Evidence.Proof.implyElim "_" "_"
      (Evidence.Proof.basis BasisName.forallAndCong [
        Evidence.Arg.ty "X",
        Evidence.Arg.pred exUnionLeftOriginal,
        Evidence.Arg.pred exUnionLeftClean,
        Evidence.Arg.pred exUnionRightOriginal,
        Evidence.Arg.pred exUnionRightClean
      ])
      exUnionLeftCleanProof)
    exUnionRightCleanProof

def exUnionCleanProof : Proof :=
  Evidence.Proof.call BasisName.forallIffTransApply [
    Evidence.Arg.ty "X",
    Evidence.Arg.pred exUnionAndOriginal,
    Evidence.Arg.pred exUnionAndReindexed,
    Evidence.Arg.pred exUnionAndClean
  ] [exUnionAndReindex, exUnionAndCong]

def smapAtomAFormula : Formula :=
  Formula.atom "R" (Term.var "w") (Term.const "a")

def smapAtomBFormula : Formula :=
  Formula.atom "R" (Term.var "w") (Term.const "b")

def smapPhiFormula : Formula :=
  Formula.papp "phi" (Term.var "w")

def smapOrAtomsFormula : Formula :=
  Formula.or smapAtomAFormula smapAtomBFormula

def smapIffAtomsFormula : Formula :=
  Formula.iff smapAtomAFormula smapAtomBFormula

def smapAtomPhiFormula : Formula :=
  Formula.and smapAtomAFormula smapPhiFormula

def smapForallAtomFormula : Formula :=
  Formula.all "u" (Ty.base "X") (Formula.atom "R" (Term.var "u") (Term.const "a"))

def smapExistAtomFormula : Formula :=
  Formula.ex "u" (Ty.base "X") (Formula.atom "R" (Term.var "u") (Term.const "a"))

def smapForallAtomPhiFormula : Formula :=
  Formula.all "u" (Ty.base "X")
    (Formula.and
      (Formula.atom "R" (Term.var "u") (Term.const "a"))
      (Formula.papp "phi" (Term.var "u")))

def smapForallOrAtomsFormula : Formula :=
  Formula.all "u" (Ty.base "X")
    (Formula.or
      (Formula.atom "R" (Term.var "u") (Term.const "a"))
      (Formula.atom "R" (Term.var "u") (Term.const "b")))

def smapForallImpAtomPhiFormula : Formula :=
  Formula.all "u" (Ty.base "X")
    (Formula.imp
      (Formula.atom "R" (Term.var "u") (Term.const "a"))
      (Formula.papp "phi" (Term.var "u")))

def smapForallIffAtomsFormula : Formula :=
  Formula.all "u" (Ty.base "X")
    (Formula.iff
      (Formula.atom "R" (Term.var "u") (Term.const "a"))
      (Formula.atom "R" (Term.var "u") (Term.const "b")))

def smapForallNotPhiFormula : Formula :=
  Formula.all "u" (Ty.base "X")
    (Formula.not (Formula.papp "phi" (Term.var "u")))

def formulaSmapPhiCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapPhiFormula

def formulaSmapOrAtomsCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapOrAtomsFormula

def formulaSmapIffAtomsCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapIffAtomsFormula

def formulaSmapAtomPhiCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapAtomPhiFormula

def formulaSmapForallAtomCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapForallAtomFormula

def formulaSmapExistAtomCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapExistAtomFormula

def formulaSmapForallAtomPhiCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapForallAtomPhiFormula

def formulaSmapForallOrAtomsCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapForallOrAtomsFormula

def formulaSmapForallImpAtomPhiCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapForallImpAtomPhiFormula

def formulaSmapForallIffAtomsCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapForallIffAtomsFormula

def formulaSmapForallNotPhiCleanCert? : Option ForallCert :=
  SubstEvidenceBuilder.buildSubstEvidence? smapForallNotPhiFormula

def formulaSmapPhiCert : ForallCert := requireCert formulaSmapPhiCert?
def formulaSmapOrAtomsCert : ForallCert := requireCert formulaSmapOrAtomsCert?
def formulaSmapIffAtomsCert : ForallCert := requireCert formulaSmapIffAtomsCert?
def formulaSmapAtomPhiCert : ForallCert := requireCert formulaSmapAtomPhiCert?
def formulaSmapForallAtomShellCert : ForallCert :=
  SubstEvidenceBuilder.forallShellEvidence "R" "a"
def formulaSmapExistAtomShellCert : ForallCert :=
  SubstEvidenceBuilder.existShellEvidence "R" "a"
def formulaSmapForallAtomCleanCert : ForallCert := requireCert formulaSmapForallAtomCleanCert?
def formulaSmapExistAtomCleanCert : ForallCert := requireCert formulaSmapExistAtomCleanCert?
def formulaSmapForallAtomPhiCleanCert : ForallCert :=
  requireCert formulaSmapForallAtomPhiCleanCert?
def formulaSmapForallOrAtomsCleanCert : ForallCert :=
  requireCert formulaSmapForallOrAtomsCleanCert?
def formulaSmapForallImpAtomPhiCleanCert : ForallCert :=
  requireCert formulaSmapForallImpAtomPhiCleanCert?
def formulaSmapForallIffAtomsCleanCert : ForallCert :=
  requireCert formulaSmapForallIffAtomsCleanCert?
def formulaSmapForallNotPhiCleanCert : ForallCert :=
  requireCert formulaSmapForallNotPhiCleanCert?

def renderFormulaSmapCert (declName binders : String) (cert : ForallCert) : String :=
  "noncomputable def " ++ declName ++ " " ++ binders ++ " :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    " ++ cert.original ++ "\n" ++
  "    " ++ cert.clean ++ ")) :=\n" ++
  "  " ++ cert.proof.render ++ "\n"

def renderGeneratedFormulaSmapPhiClean : String :=
  renderFormulaSmapCert "generated_formula_smap_phiClean"
    "(X : Type) (phi : Pred X) (s : X)"
    formulaSmapPhiCert

def renderGeneratedFormulaSmapOrAtomsClean : String :=
  renderFormulaSmapCert "generated_formula_smap_orAtomsClean"
    "(X : Type) (R : Pred (X × X)) (a b s : X)"
    formulaSmapOrAtomsCert

def renderGeneratedFormulaSmapIffAtomsClean : String :=
  renderFormulaSmapCert "generated_formula_smap_iffAtomsClean"
    "(X : Type) (R : Pred (X × X)) (a b s : X)"
    formulaSmapIffAtomsCert

def renderGeneratedFormulaSmapAtomPhiClean : String :=
  renderFormulaSmapCert "generated_formula_smap_atomPhiClean"
    "(X : Type) (R : Pred (X × X)) (phi : Pred X) (a s : X)"
    formulaSmapAtomPhiCert

def renderGeneratedFormulaSmapForallAtomShell : String :=
  renderFormulaSmapCert "generated_formula_smap_forallAtomShell"
    "(X : Type) (R : Pred (X × X)) (a s : X)"
    formulaSmapForallAtomShellCert

def renderGeneratedFormulaSmapExistAtomShell : String :=
  renderFormulaSmapCert "generated_formula_smap_existAtomShell"
    "(X : Type) (R : Pred (X × X)) (a s : X)"
    formulaSmapExistAtomShellCert

def renderGeneratedFormulaSmapForallAtomClean : String :=
  renderFormulaSmapCert "generated_formula_smap_forallAtomClean"
    "(X : Type) (R : Pred (X × X)) (a s : X)"
    formulaSmapForallAtomCleanCert

def renderGeneratedFormulaSmapExistAtomClean : String :=
  renderFormulaSmapCert "generated_formula_smap_existAtomClean"
    "(X : Type) (R : Pred (X × X)) (a s : X)"
    formulaSmapExistAtomCleanCert

def renderGeneratedFormulaSmapForallAtomPhiClean : String :=
  renderFormulaSmapCert "generated_formula_smap_forallAtomPhiClean"
    "(X : Type) (R : Pred (X × X)) (phi : Pred X) (a s : X)"
    formulaSmapForallAtomPhiCleanCert

def renderGeneratedFormulaSmapForallOrAtomsClean : String :=
  renderFormulaSmapCert "generated_formula_smap_forallOrAtomsClean"
    "(X : Type) (R : Pred (X × X)) (a b s : X)"
    formulaSmapForallOrAtomsCleanCert

def renderGeneratedFormulaSmapForallImpAtomPhiClean : String :=
  renderFormulaSmapCert "generated_formula_smap_forallImpAtomPhiClean"
    "(X : Type) (R : Pred (X × X)) (phi : Pred X) (a s : X)"
    formulaSmapForallImpAtomPhiCleanCert

def renderGeneratedFormulaSmapForallIffAtomsClean : String :=
  renderFormulaSmapCert "generated_formula_smap_forallIffAtomsClean"
    "(X : Type) (R : Pred (X × X)) (a b s : X)"
    formulaSmapForallIffAtomsCleanCert

def renderGeneratedFormulaSmapForallNotPhiClean : String :=
  renderFormulaSmapCert "generated_formula_smap_forallNotPhiClean"
    "(X : Type) (phi : Pred X) (s : X)"
    formulaSmapForallNotPhiCleanCert

def renderGeneratedMemBeta : String :=
  "noncomputable def generated_memBeta (X : Type) (elt : Pred (X × X)) (t s : X) :\n" ++
  "  iff (Pred.term ((memAt X elt s) ∘ pointAt X t)) (curry X X PC elt t s) :=\n" ++
  "  " ++ memBetaProof.render ++ "\n"

def renderGeneratedMemBetaRev : String :=
  "noncomputable def generated_memBetaRev (X : Type) (elt : Pred (X × X)) (z t : X) :\n" ++
  "  iff (Pred.term\n" ++
  "        ((sub2 (X × Final) X X elt (Cart.weakening X (X × Final) z) (v0 X Final)) ∘ pointAt X t))\n" ++
  "      (curry X X PC elt z t) :=\n" ++
  "  " ++ memBetaRevProof.render ++ "\n"

def renderGeneratedConstAtomBeta : String :=
  "noncomputable def generated_constAtomBeta (X : Type) (elt : Pred (X × X)) (c d t : X) :\n" ++
  "  iff (Pred.term\n" ++
  "        ((sub2 (X × Final) X X elt (Cart.weakening X (X × Final) c) (Cart.weakening X (X × Final) d))\n" ++
  "          ∘ pointAt X t))\n" ++
  "      (curry X X PC elt c d) :=\n" ++
  "  " ++ constAtomBetaProof.render ++ "\n"

def renderGeneratedSepPhiBeta : String :=
  "noncomputable def generated_sepPhiBeta (X : Type) (phi : Pred X) (s t : X) :\n" ++
  "  iff (Pred.term ((phi ∘ (v0 X (X × Final))) ∘ (smap X s ∘ pointAt X t))) (phi t) :=\n" ++
  "  " ++ sepPhiBetaProof.render ++ "\n"

def renderGeneratedAtomBeta : String :=
  "noncomputable def generated_atomBeta (X : Type) (R : Pred (X × X)) (s c t : X) :\n" ++
  "  iff (Pred.term\n" ++
  "        ((sub2 (X × (X × Final)) X X R (v0 X (X × Final))\n" ++
  "           (Cart.weakening X (X × (X × Final)) c)) ∘ (smap X s ∘ pointAt X t)))\n" ++
  "      (curry X X PC R t c) :=\n" ++
  "  " ++ atomBetaProof.render ++ "\n"

def renderGeneratedForallAtomSmapClean : String :=
  "noncomputable def generated_Forall_atomSmapClean (X : Type) (R : Pred (X × X)) (a s : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × Final)) X X R\n" ++
  "        (v0 X (X × Final))\n" ++
  "        (Cart.weakening X (X × (X × Final)) a))\n" ++
  "      ∘ smap X s)\n" ++
  "    (sub2 (X × Final) X X R\n" ++
  "      (v0 X Final)\n" ++
  "      (Cart.weakening X (X × Final) a)))) :=\n" ++
  "  " ++ forallAtomSmapCleanProof.render ++ "\n"

def renderGeneratedForallOrAtomsClean : String :=
  "noncomputable def generated_Forall_orAtomsClean (X : Type) (R : Pred (X × X)) (a b s : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.or (X × (X × Final))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) a))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) b)))\n" ++
  "     ∘ smap X s)\n" ++
  "    (Pred.or (X × Final)\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) a))\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) b))))) :=\n" ++
  "  " ++ forallOrAtomsCleanProof.render ++ "\n"

def renderGeneratedForallIffAtomsClean : String :=
  "noncomputable def generated_Forall_iffAtomsClean (X : Type) (R : Pred (X × X)) (a b s : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.iff (X × (X × Final))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) a))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) b)))\n" ++
  "     ∘ smap X s)\n" ++
  "    (Pred.iff (X × Final)\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) a))\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) b))))) :=\n" ++
  "  " ++ forallIffAtomsCleanProof.render ++ "\n"

def renderGeneratedForallExMemPhiAtomClean : String :=
  "noncomputable def generated_Forall_exMemPhi_atomClean (X : Type) (R : Pred (X × X)) (c : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (v1 X X Final))\n" ++
  "      ∘ (pair (X × Final) X (X × Final)\n" ++
  "          (fst X Final)\n" ++
  "          ((pointAt X c) ∘ snd X Final)))\n" ++
  "    (memAt X R c))) :=\n" ++
  "  " ++ exMemPhiAtomCleanProof.render ++ "\n"

def renderGeneratedForallExMemPhiPhiClean : String :=
  "noncomputable def generated_Forall_exMemPhi_phiClean (X : Type) (phi : Pred X) (c : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((phi ∘ (v0 X (X × Final)))\n" ++
  "      ∘ (pair (X × Final) X (X × Final)\n" ++
  "          (fst X Final)\n" ++
  "          ((pointAt X c) ∘ snd X Final)))\n" ++
  "    (phi ∘ (v0 X Final)))) :=\n" ++
  "  " ++ exMemPhiPhiCleanProof.render ++ "\n"

def renderGeneratedForallExMemPhiClean : String :=
  "noncomputable def generated_Forall_exMemPhiClean (X : Type) (R : Pred (X × X)) (phi : Pred X) (c : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.and (X × (X × Final))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (v1 X X Final))\n" ++
  "       (phi ∘ (v0 X (X × Final))))\n" ++
  "     ∘ (pair (X × Final) X (X × Final) (fst X Final) ((pointAt X c) ∘ snd X Final)))\n" ++
  "    (Pred.and (X × Final)\n" ++
  "      (memAt X R c)\n" ++
  "      (phi ∘ (v0 X Final))))) :=\n" ++
  "  " ++ exMemPhiCleanProof.render ++ "\n"

def renderGeneratedForallExUnionLeftClean : String :=
  "noncomputable def generated_Forall_exUnion_leftClean (X : Type) (R : Pred (X × X)) (A z U : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × (X × Final))) X X R\n" ++
  "       (v0 X (X × (X × Final))) (Cart.weakening X (X × (X × (X × Final))) A))\n" ++
  "     ∘ (pair (X × Final) X (X × (X × Final)) (fst X Final)\n" ++
  "          ((smap X U ∘ pointAt X z) ∘ snd X Final)))\n" ++
  "    (memAt X R A))) :=\n" ++
  "  " ++ exUnionLeftCleanProof.render ++ "\n"

def renderGeneratedForallExUnionRightClean : String :=
  "noncomputable def generated_Forall_exUnion_rightClean (X : Type) (R : Pred (X × X)) (A z U : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × (X × Final))) X X R\n" ++
  "       (v1 X X (X × Final)) (v0 X (X × (X × Final))))\n" ++
  "     ∘ (pair (X × Final) X (X × (X × Final)) (fst X Final)\n" ++
  "          ((smap X U ∘ pointAt X z) ∘ snd X Final)))\n" ++
  "    (sub2 (X × Final) X X R (Cart.weakening X (X × Final) z) (v0 X Final)))) :=\n" ++
  "  " ++ exUnionRightCleanProof.render ++ "\n"

def renderGeneratedForallExUnionClean : String :=
  "noncomputable def generated_Forall_exUnionClean (X : Type) (R : Pred (X × X)) (A z U : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.and (X × (X × (X × Final)))\n" ++
  "       (sub2 (X × (X × (X × Final))) X X R\n" ++
  "         (v0 X (X × (X × Final))) (Cart.weakening X (X × (X × (X × Final))) A))\n" ++
  "       (sub2 (X × (X × (X × Final))) X X R\n" ++
  "         (v1 X X (X × Final)) (v0 X (X × (X × Final)))))\n" ++
  "     ∘ (pair (X × Final) X (X × (X × Final)) (fst X Final)\n" ++
  "          ((smap X U ∘ pointAt X z) ∘ snd X Final)))\n" ++
  "    (Pred.and (X × Final)\n" ++
  "      (memAt X R A)\n" ++
  "      (sub2 (X × Final) X X R (Cart.weakening X (X × Final) z) (v0 X Final))))) :=\n" ++
  "  " ++ exUnionCleanProof.render ++ "\n"

def generatedDerivationsFile : String :=
  "-- Generated by formalization/GenerateBasisDerivations.lean.\n" ++
  "-- This file is an M2 certificate target: proofs are rendered from Evidence.Proof.\n" ++
  "import definite_description\n\n" ++
  renderGeneratedMemBeta ++ "\n" ++
  renderGeneratedMemBetaRev ++ "\n" ++
  renderGeneratedConstAtomBeta ++ "\n" ++
  renderGeneratedSepPhiBeta ++ "\n" ++
  renderGeneratedAtomBeta ++ "\n" ++
  renderGeneratedForallAtomSmapClean ++ "\n" ++
  renderGeneratedForallOrAtomsClean ++ "\n" ++
  renderGeneratedForallIffAtomsClean ++ "\n" ++
  renderGeneratedForallExMemPhiAtomClean ++ "\n" ++
  renderGeneratedForallExMemPhiPhiClean ++ "\n" ++
  renderGeneratedForallExMemPhiClean ++ "\n" ++
  renderGeneratedForallExUnionLeftClean ++ "\n" ++
  renderGeneratedForallExUnionRightClean ++ "\n" ++
  renderGeneratedForallExUnionClean ++ "\n" ++
  renderGeneratedFormulaSmapPhiClean ++ "\n" ++
  renderGeneratedFormulaSmapOrAtomsClean ++ "\n" ++
  renderGeneratedFormulaSmapIffAtomsClean ++ "\n" ++
  renderGeneratedFormulaSmapAtomPhiClean ++ "\n" ++
  renderGeneratedFormulaSmapForallAtomShell ++ "\n" ++
  renderGeneratedFormulaSmapExistAtomShell ++ "\n" ++
  renderGeneratedFormulaSmapForallAtomClean ++ "\n" ++
  renderGeneratedFormulaSmapExistAtomClean ++ "\n" ++
  renderGeneratedFormulaSmapForallAtomPhiClean ++ "\n" ++
  renderGeneratedFormulaSmapForallOrAtomsClean ++ "\n" ++
  renderGeneratedFormulaSmapForallImpAtomPhiClean ++ "\n" ++
  renderGeneratedFormulaSmapForallIffAtomsClean ++ "\n" ++
  renderGeneratedFormulaSmapForallNotPhiClean

def regenCheckFile : String :=
  "-- Generated by formalization/GenerateBasisDerivations.lean.\n" ++
  "-- Ascribes generated proofs to the handwritten Core statement shapes.\n" ++
  "import definite_description\n" ++
  "import generated_basis_derivations\n\n" ++
  "noncomputable def memBeta_generated_check (X : Type) (elt : Pred (X × X)) (t s : X) :\n" ++
  "  iff (Pred.term ((memAt X elt s) ∘ pointAt X t)) (curry X X PC elt t s) :=\n" ++
  "  generated_memBeta X elt t s\n\n" ++
  "noncomputable def memBetaRev_generated_check (X : Type) (elt : Pred (X × X)) (z t : X) :\n" ++
  "  iff (Pred.term\n" ++
  "        ((sub2 (X × Final) X X elt (Cart.weakening X (X × Final) z) (v0 X Final)) ∘ pointAt X t))\n" ++
  "      (curry X X PC elt z t) :=\n" ++
  "  generated_memBetaRev X elt z t\n\n" ++
  "noncomputable def constAtomBeta_generated_check (X : Type) (elt : Pred (X × X)) (c d t : X) :\n" ++
  "  iff (Pred.term\n" ++
  "        ((sub2 (X × Final) X X elt (Cart.weakening X (X × Final) c) (Cart.weakening X (X × Final) d))\n" ++
  "          ∘ pointAt X t))\n" ++
  "      (curry X X PC elt c d) :=\n" ++
  "  generated_constAtomBeta X elt c d t\n\n" ++
  "noncomputable def sepPhiBeta_generated_check (X : Type) (phi : Pred X) (s t : X) :\n" ++
  "  iff (Pred.term ((phi ∘ (v0 X (X × Final))) ∘ (smap X s ∘ pointAt X t))) (phi t) :=\n" ++
  "  generated_sepPhiBeta X phi s t\n\n" ++
  "noncomputable def atomBeta_generated_check (X : Type) (R : Pred (X × X)) (s c t : X) :\n" ++
  "  iff (Pred.term\n" ++
  "        ((sub2 (X × (X × Final)) X X R (v0 X (X × Final))\n" ++
  "           (Cart.weakening X (X × (X × Final)) c)) ∘ (smap X s ∘ pointAt X t)))\n" ++
  "      (curry X X PC R t c) :=\n" ++
  "  generated_atomBeta X R s c t\n\n" ++
  "noncomputable def Forall_atomSmapClean_generated_check (X : Type) (R : Pred (X × X)) (a s : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × Final)) X X R\n" ++
  "        (v0 X (X × Final))\n" ++
  "        (Cart.weakening X (X × (X × Final)) a))\n" ++
  "      ∘ smap X s)\n" ++
  "    (sub2 (X × Final) X X R\n" ++
  "      (v0 X Final)\n" ++
  "      (Cart.weakening X (X × Final) a)))) :=\n" ++
  "  generated_Forall_atomSmapClean X R a s\n\n" ++
  "noncomputable def Forall_orAtomsClean_generated_check (X : Type) (R : Pred (X × X)) (a b s : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.or (X × (X × Final))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) a))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) b)))\n" ++
  "     ∘ smap X s)\n" ++
  "    (Pred.or (X × Final)\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) a))\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) b))))) :=\n" ++
  "  generated_Forall_orAtomsClean X R a b s\n\n" ++
  "noncomputable def Forall_iffAtomsClean_generated_check (X : Type) (R : Pred (X × X)) (a b s : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.iff (X × (X × Final))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) a))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (Cart.weakening X (X × (X × Final)) b)))\n" ++
  "     ∘ smap X s)\n" ++
  "    (Pred.iff (X × Final)\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) a))\n" ++
  "      (sub2 (X × Final) X X R (v0 X Final) (Cart.weakening X (X × Final) b))))) :=\n" ++
  "  generated_Forall_iffAtomsClean X R a b s\n\n" ++
  "noncomputable def Forall_exMemPhi_atomClean_generated_check (X : Type) (R : Pred (X × X)) (c : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (v1 X X Final))\n" ++
  "      ∘ (pair (X × Final) X (X × Final)\n" ++
  "          (fst X Final)\n" ++
  "          ((pointAt X c) ∘ snd X Final)))\n" ++
  "    (memAt X R c))) :=\n" ++
  "  generated_Forall_exMemPhi_atomClean X R c\n\n" ++
  "noncomputable def Forall_exMemPhi_phiClean_generated_check (X : Type) (phi : Pred X) (c : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((phi ∘ (v0 X (X × Final)))\n" ++
  "      ∘ (pair (X × Final) X (X × Final)\n" ++
  "          (fst X Final)\n" ++
  "          ((pointAt X c) ∘ snd X Final)))\n" ++
  "    (phi ∘ (v0 X Final)))) :=\n" ++
  "  generated_Forall_exMemPhi_phiClean X phi c\n\n" ++
  "noncomputable def Forall_exMemPhiClean_generated_check (X : Type) (R : Pred (X × X)) (phi : Pred X) (c : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.and (X × (X × Final))\n" ++
  "       (sub2 (X × (X × Final)) X X R (v0 X (X × Final)) (v1 X X Final))\n" ++
  "       (phi ∘ (v0 X (X × Final))))\n" ++
  "     ∘ (pair (X × Final) X (X × Final) (fst X Final) ((pointAt X c) ∘ snd X Final)))\n" ++
  "    (Pred.and (X × Final)\n" ++
  "      (memAt X R c)\n" ++
  "      (phi ∘ (v0 X Final))))) :=\n" ++
  "  generated_Forall_exMemPhiClean X R phi c\n\n" ++
  "noncomputable def Forall_exUnion_leftClean_generated_check (X : Type) (R : Pred (X × X)) (A z U : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × (X × Final))) X X R\n" ++
  "       (v0 X (X × (X × Final))) (Cart.weakening X (X × (X × (X × Final))) A))\n" ++
  "     ∘ (pair (X × Final) X (X × (X × Final)) (fst X Final)\n" ++
  "          ((smap X U ∘ pointAt X z) ∘ snd X Final)))\n" ++
  "    (memAt X R A))) :=\n" ++
  "  generated_Forall_exUnion_leftClean X R A z U\n\n" ++
  "noncomputable def Forall_exUnion_rightClean_generated_check (X : Type) (R : Pred (X × X)) (A z U : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((sub2 (X × (X × (X × Final))) X X R\n" ++
  "       (v1 X X (X × Final)) (v0 X (X × (X × Final))))\n" ++
  "     ∘ (pair (X × Final) X (X × (X × Final)) (fst X Final)\n" ++
  "          ((smap X U ∘ pointAt X z) ∘ snd X Final)))\n" ++
  "    (sub2 (X × Final) X X R (Cart.weakening X (X × Final) z) (v0 X Final)))) :=\n" ++
  "  generated_Forall_exUnion_rightClean X R A z U\n\n" ++
  "noncomputable def Forall_exUnionClean_generated_check (X : Type) (R : Pred (X × X)) (A z U : X) :\n" ++
  "  Pred.term (Forall X Final (Pred.iff (X × Final)\n" ++
  "    ((Pred.and (X × (X × (X × Final)))\n" ++
  "       (sub2 (X × (X × (X × Final))) X X R\n" ++
  "         (v0 X (X × (X × Final))) (Cart.weakening X (X × (X × (X × Final))) A))\n" ++
  "       (sub2 (X × (X × (X × Final))) X X R\n" ++
  "         (v1 X X (X × Final)) (v0 X (X × (X × Final)))))\n" ++
  "     ∘ (pair (X × Final) X (X × (X × Final)) (fst X Final)\n" ++
  "          ((smap X U ∘ pointAt X z) ∘ snd X Final)))\n" ++
  "    (Pred.and (X × Final)\n" ++
  "      (memAt X R A)\n" ++
  "      (sub2 (X × Final) X X R (Cart.weakening X (X × Final) z) (v0 X Final))))) :=\n" ++
  "  generated_Forall_exUnionClean X R A z U\n\n" ++
  "#check @memBeta_generated_check\n" ++
  "#check @memBetaRev_generated_check\n" ++
  "#check @constAtomBeta_generated_check\n" ++
  "#check @sepPhiBeta_generated_check\n" ++
  "#check @atomBeta_generated_check\n" ++
  "#check @Forall_atomSmapClean_generated_check\n" ++
  "#check @Forall_orAtomsClean_generated_check\n" ++
  "#check @Forall_iffAtomsClean_generated_check\n" ++
  "#check @Forall_exMemPhi_atomClean_generated_check\n" ++
  "#check @Forall_exMemPhi_phiClean_generated_check\n" ++
  "#check @Forall_exMemPhiClean_generated_check\n" ++
  "#check @Forall_exUnion_leftClean_generated_check\n" ++
  "#check @Forall_exUnion_rightClean_generated_check\n" ++
  "#check @Forall_exUnionClean_generated_check\n" ++
  "#check @generated_formula_smap_phiClean\n" ++
  "#check @generated_formula_smap_orAtomsClean\n" ++
  "#check @generated_formula_smap_iffAtomsClean\n" ++
  "#check @generated_formula_smap_atomPhiClean\n" ++
  "#check @generated_formula_smap_forallAtomShell\n" ++
  "#check @generated_formula_smap_existAtomShell\n" ++
  "#check @generated_formula_smap_forallAtomClean\n" ++
  "#check @generated_formula_smap_existAtomClean\n" ++
  "#check @generated_formula_smap_forallAtomPhiClean\n" ++
  "#check @generated_formula_smap_forallOrAtomsClean\n" ++
  "#check @generated_formula_smap_forallImpAtomPhiClean\n" ++
  "#check @generated_formula_smap_forallIffAtomsClean\n" ++
  "#check @generated_formula_smap_forallNotPhiClean\n"

def ensureAllowed (proof : Proof) : IO Unit := do
  if proof.usesOnlyAllowed then
    pure ()
  else
    throw (IO.userError
      "generated proof references a raw proof term or a name outside BasisName.all")

def ensureBuilt (label : String) (result : Option ForallCert) : IO Unit := do
  match result with
  | some _ => pure ()
  | none => throw (IO.userError ("formula evidence generation failed for " ++ label))

def main (_args : List String) : IO Unit := do
  ensureAllowed memBetaProof
  ensureAllowed memBetaRevProof
  ensureAllowed constAtomBetaProof
  ensureAllowed sepPhiBetaProof
  ensureAllowed atomBetaProof
  ensureAllowed forallAtomSmapCleanProof
  ensureAllowed forallOrAtomsCleanProof
  ensureAllowed forallIffAtomsCleanProof
  ensureAllowed exMemPhiAtomCleanProof
  ensureAllowed exMemPhiPhiCleanProof
  ensureAllowed exMemPhiCleanProof
  ensureAllowed exUnionLeftCleanProof
  ensureAllowed exUnionRightCleanProof
  ensureAllowed exUnionCleanProof
  ensureBuilt "smap phi" formulaSmapPhiCert?
  ensureBuilt "smap or atoms" formulaSmapOrAtomsCert?
  ensureBuilt "smap iff atoms" formulaSmapIffAtomsCert?
  ensureBuilt "smap atom phi" formulaSmapAtomPhiCert?
  ensureBuilt "smap forall atom clean" formulaSmapForallAtomCleanCert?
  ensureBuilt "smap exist atom clean" formulaSmapExistAtomCleanCert?
  ensureBuilt "smap forall atom phi clean" formulaSmapForallAtomPhiCleanCert?
  ensureBuilt "smap forall or atoms clean" formulaSmapForallOrAtomsCleanCert?
  ensureBuilt "smap forall imp atom phi clean" formulaSmapForallImpAtomPhiCleanCert?
  ensureBuilt "smap forall iff atoms clean" formulaSmapForallIffAtomsCleanCert?
  ensureBuilt "smap forall not phi clean" formulaSmapForallNotPhiCleanCert?
  ensureAllowed formulaSmapPhiCert.proof
  ensureAllowed formulaSmapOrAtomsCert.proof
  ensureAllowed formulaSmapIffAtomsCert.proof
  ensureAllowed formulaSmapAtomPhiCert.proof
  ensureAllowed formulaSmapForallAtomShellCert.proof
  ensureAllowed formulaSmapExistAtomShellCert.proof
  ensureAllowed formulaSmapForallAtomCleanCert.proof
  ensureAllowed formulaSmapExistAtomCleanCert.proof
  ensureAllowed formulaSmapForallAtomPhiCleanCert.proof
  ensureAllowed formulaSmapForallOrAtomsCleanCert.proof
  ensureAllowed formulaSmapForallImpAtomPhiCleanCert.proof
  ensureAllowed formulaSmapForallIffAtomsCleanCert.proof
  ensureAllowed formulaSmapForallNotPhiCleanCert.proof
  IO.FS.writeFile "/home/andre/mathagent/ma1/generated_basis_derivations.cor"
    generatedDerivationsFile
  IO.FS.writeFile "/home/andre/mathagent/ma1/contextual_hol_basis_derivation_check.cor"
    regenCheckFile

end BasisDerivations
end ContextualHOL

def main (args : List String) : IO Unit :=
  ContextualHOL.BasisDerivations.main args
