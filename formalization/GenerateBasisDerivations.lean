import ContextualHOL.Evidence

open ContextualHOL

namespace ContextualHOL
namespace BasisDerivations

abbrev Arg := Evidence.Arg
abbrev Proof := Evidence.Proof

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
  renderGeneratedForallIffAtomsClean

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
  "#check @memBeta_generated_check\n" ++
  "#check @memBetaRev_generated_check\n" ++
  "#check @constAtomBeta_generated_check\n" ++
  "#check @sepPhiBeta_generated_check\n" ++
  "#check @atomBeta_generated_check\n" ++
  "#check @Forall_atomSmapClean_generated_check\n" ++
  "#check @Forall_orAtomsClean_generated_check\n" ++
  "#check @Forall_iffAtomsClean_generated_check\n"

def ensureAllowed (proof : Proof) : IO Unit := do
  if proof.usesOnlyAllowed then
    pure ()
  else
    throw (IO.userError "generated proof references a name outside BasisName.all")

def main (_args : List String) : IO Unit := do
  ensureAllowed memBetaProof
  ensureAllowed memBetaRevProof
  ensureAllowed constAtomBetaProof
  ensureAllowed sepPhiBetaProof
  ensureAllowed atomBetaProof
  ensureAllowed forallAtomSmapCleanProof
  ensureAllowed forallOrAtomsCleanProof
  ensureAllowed forallIffAtomsCleanProof
  IO.FS.writeFile "/home/andre/mathagent/ma1/generated_basis_derivations.cor"
    generatedDerivationsFile
  IO.FS.writeFile "/home/andre/mathagent/ma1/contextual_hol_basis_derivation_check.cor"
    regenCheckFile

end BasisDerivations
end ContextualHOL

def main (args : List String) : IO Unit :=
  ContextualHOL.BasisDerivations.main args
