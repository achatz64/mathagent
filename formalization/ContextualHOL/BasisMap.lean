import ContextualHOL.Core

namespace ContextualHOL

inductive BasisOrigin where
  | betaBasis
  | classicalFirstOrderLogic
  | primitiveLogic
  deriving Repr, BEq, DecidableEq

inductive BasisName where
  -- ma1/beta_basis.cor
  | betaSub2Point
  | betaV0PointArg1
  | betaV0PointArg2
  | betaV0PointUnary
  | betaFstPairPointArg1
  | betaFstPairPointUnary
  | betaWeakeningArg1
  | betaWeakeningArg2
  | forallOrReindexBeta
  | forallAndReindexBeta
  | forallImpReindexBeta
  | forallIffReindexBeta
  | forallNotReindexBeta
  | forallUnaryReindexBeta
  | forallOrCong
  | forallAndCong
  | forallImpCong
  | forallIffCong
  | forallNotCong
  | forallForallCong
  | forallExistCong
  | existReindex
  | forallSub2ReindexBeta
  | forallFstPairBetaLeft
  | forallFstPairBetaRight
  | forallFstPairCompBetaLeft
  | forallFstPairComp2BetaLeft
  | forallFstPairUnaryBeta
  | forallSndPairThenBetaRight
  | forallSndPairThenBetaLeft
  | forallPointAtFstBetaLeft
  | forallPointAtFstBetaRight
  | forallConstCompBetaRight
  | forallConstCompBetaLeft
  | forallIffSymApply
  | forallIffTransApply
  | forallFstPairUnaryBetaGrouped
  | forallCtxSub2ReindexBeta
  | forallCtxUnaryReindexBeta
  | forallCtxAndReindexBeta
  | forallCtxOrReindexBeta
  | forallCtxImpReindexBeta
  | forallCtxIffReindexBeta
  | forallCtxNotReindexBeta
  | forallCtxAndCong
  | forallCtxOrCong
  | forallCtxImpCong
  | forallCtxIffCong
  | forallCtxNotCong
  | forallCtxFstPairBetaLeft
  | forallCtxConstCompBetaRight
  | forallCtxFstPairUnaryBetaGrouped
  | forallCtxIffTransApply
  -- ma1/beta_basis.cor: M3 additions (lifted-map cleanup + closure/fusion)
  | forallSndPairLiftBetaLeft
  | forallSndPairLiftBetaRight
  | forallSndPairLiftUnaryBeta
  | forallSndPairIdBetaLeft
  | forallSndPairIdBetaRight
  | forallSndPairIdUnaryBeta
  | forallSndAssocBetaLeft
  | forallSndAssocBetaRight
  | forallSndAssocUnaryBeta
  | forallFstPairCompBetaRight
  | forallFstPairCompUnaryBeta
  | forallConstCompUnaryBeta
  | forallClosureBeta
  | existClosureBeta
  | forallLiftFuse
  -- ma1/classical_first_order_logic_new.cor
  | forallReindex
  | curryUncurry
  | relEqExt
  | forallElim
  | existIntro
  | termImply
  | termAnd
  | termOr
  | termNot
  | termExist
  | forallMono
  | forallAnd
  | existMono
  | forallMonoCtx
  | forallAndCtx
  | forallIffTransCtx
  | forallAndElimL
  | forallIffMp
  | forallIffRefl
  | forallIffSym
  | forallIffTrans
  | forallAndMono
  | forallAndOrDistrib
  | forallAndProjL
  -- primitive logical proof constants
  | implyElim
  | iffTrans
  | iffSym
  | iffMp
  | iffMpr
  deriving Repr, BEq, DecidableEq

namespace BasisName

def coreName : BasisName -> String
  | betaSub2Point => "beta_sub2_point"
  | betaV0PointArg1 => "beta_v0_point_arg1"
  | betaV0PointArg2 => "beta_v0_point_arg2"
  | betaV0PointUnary => "beta_v0_point_unary"
  | betaFstPairPointArg1 => "beta_fst_pair_point_arg1"
  | betaFstPairPointUnary => "beta_fst_pair_point_unary"
  | betaWeakeningArg1 => "beta_weakening_arg1"
  | betaWeakeningArg2 => "beta_weakening_arg2"
  | forallOrReindexBeta => "Forall_or_reindex_beta"
  | forallAndReindexBeta => "Forall_and_reindex_beta"
  | forallImpReindexBeta => "Forall_imp_reindex_beta"
  | forallIffReindexBeta => "Forall_iff_reindex_beta"
  | forallNotReindexBeta => "Forall_not_reindex_beta"
  | forallUnaryReindexBeta => "Forall_unary_reindex_beta"
  | forallOrCong => "Forall_orCong"
  | forallAndCong => "Forall_andCong"
  | forallImpCong => "Forall_impCong"
  | forallIffCong => "Forall_iffCong"
  | forallNotCong => "Forall_notCong"
  | forallForallCong => "Forall_ForallCong"
  | forallExistCong => "Forall_ExistCong"
  | existReindex => "Exist_reindex"
  | forallSub2ReindexBeta => "Forall_sub2_reindex_beta"
  | forallFstPairBetaLeft => "Forall_fst_pair_beta_left"
  | forallFstPairBetaRight => "Forall_fst_pair_beta_right"
  | forallFstPairCompBetaLeft => "Forall_fst_pair_comp_beta_left"
  | forallFstPairComp2BetaLeft => "Forall_fst_pair_comp2_beta_left"
  | forallFstPairUnaryBeta => "Forall_fst_pair_unary_beta"
  | forallSndPairThenBetaRight => "Forall_snd_pair_then_beta_right"
  | forallSndPairThenBetaLeft => "Forall_snd_pair_then_beta_left"
  | forallPointAtFstBetaLeft => "Forall_pointAt_fst_beta_left"
  | forallPointAtFstBetaRight => "Forall_pointAt_fst_beta_right"
  | forallConstCompBetaRight => "Forall_const_comp_beta_right"
  | forallConstCompBetaLeft => "Forall_const_comp_beta_left"
  | forallIffSymApply => "Forall_iffSym_apply"
  | forallIffTransApply => "Forall_iffTrans_apply"
  | forallFstPairUnaryBetaGrouped => "Forall_fst_pair_unary_beta_grouped"
  | forallCtxSub2ReindexBeta => "Forall_ctx_sub2_reindex_beta"
  | forallCtxUnaryReindexBeta => "Forall_ctx_unary_reindex_beta"
  | forallCtxAndReindexBeta => "Forall_ctx_and_reindex_beta"
  | forallCtxOrReindexBeta => "Forall_ctx_or_reindex_beta"
  | forallCtxImpReindexBeta => "Forall_ctx_imp_reindex_beta"
  | forallCtxIffReindexBeta => "Forall_ctx_iff_reindex_beta"
  | forallCtxNotReindexBeta => "Forall_ctx_not_reindex_beta"
  | forallCtxAndCong => "Forall_ctx_andCong"
  | forallCtxOrCong => "Forall_ctx_orCong"
  | forallCtxImpCong => "Forall_ctx_impCong"
  | forallCtxIffCong => "Forall_ctx_iffCong"
  | forallCtxNotCong => "Forall_ctx_notCong"
  | forallCtxFstPairBetaLeft => "Forall_ctx_fst_pair_beta_left"
  | forallCtxConstCompBetaRight => "Forall_ctx_const_comp_beta_right"
  | forallCtxFstPairUnaryBetaGrouped => "Forall_ctx_fst_pair_unary_beta_grouped"
  | forallCtxIffTransApply => "Forall_ctx_iffTrans_apply"
  | forallSndPairLiftBetaLeft => "Forall_snd_pair_lift_beta_left"
  | forallSndPairLiftBetaRight => "Forall_snd_pair_lift_beta_right"
  | forallSndPairLiftUnaryBeta => "Forall_snd_pair_lift_unary_beta"
  | forallSndPairIdBetaLeft => "Forall_snd_pair_id_beta_left"
  | forallSndPairIdBetaRight => "Forall_snd_pair_id_beta_right"
  | forallSndPairIdUnaryBeta => "Forall_snd_pair_id_unary_beta"
  | forallSndAssocBetaLeft => "Forall_snd_assoc_beta_left"
  | forallSndAssocBetaRight => "Forall_snd_assoc_beta_right"
  | forallSndAssocUnaryBeta => "Forall_snd_assoc_unary_beta"
  | forallFstPairCompBetaRight => "Forall_fst_pair_comp_beta_right"
  | forallFstPairCompUnaryBeta => "Forall_fst_pair_comp_unary_beta"
  | forallConstCompUnaryBeta => "Forall_const_comp_unary_beta"
  | forallClosureBeta => "Forall_closure_beta"
  | existClosureBeta => "Exist_closure_beta"
  | forallLiftFuse => "Forall_lift_fuse"
  | forallReindex => "Forall_reindex"
  | curryUncurry => "curry_uncurry"
  | relEqExt => "RelEqExt"
  | forallElim => "Forall_elim"
  | existIntro => "Exist_intro"
  | termImply => "term_imply"
  | termAnd => "term_and"
  | termOr => "term_or"
  | termNot => "term_not"
  | termExist => "term_exist"
  | forallMono => "Forall_mono"
  | forallAnd => "Forall_and"
  | existMono => "Exist_mono"
  | forallMonoCtx => "Forall_mono_ctx"
  | forallAndCtx => "Forall_and_ctx"
  | forallIffTransCtx => "Forall_iffTrans_ctx"
  | forallAndElimL => "Forall_andElimL"
  | forallIffMp => "Forall_iffMp"
  | forallIffRefl => "Forall_iffRefl"
  | forallIffSym => "Forall_iffSym"
  | forallIffTrans => "Forall_iffTrans"
  | forallAndMono => "Forall_andMono"
  | forallAndOrDistrib => "Forall_andOrDistrib"
  | forallAndProjL => "Forall_andProjL"
  | implyElim => "imply_elim"
  | iffTrans => "iff_trans"
  | iffSym => "iff_sym"
  | iffMp => "iff_mp"
  | iffMpr => "iff_mpr"

def origin : BasisName -> BasisOrigin
  | betaSub2Point
  | betaV0PointArg1
  | betaV0PointArg2
  | betaV0PointUnary
  | betaFstPairPointArg1
  | betaFstPairPointUnary
  | betaWeakeningArg1
  | betaWeakeningArg2
  | forallOrReindexBeta
  | forallAndReindexBeta
  | forallImpReindexBeta
  | forallIffReindexBeta
  | forallNotReindexBeta
  | forallUnaryReindexBeta
  | forallOrCong
  | forallAndCong
  | forallImpCong
  | forallIffCong
  | forallNotCong
  | forallForallCong
  | forallExistCong
  | existReindex
  | forallSub2ReindexBeta
  | forallFstPairBetaLeft
  | forallFstPairBetaRight
  | forallFstPairCompBetaLeft
  | forallFstPairComp2BetaLeft
  | forallFstPairUnaryBeta
  | forallSndPairThenBetaRight
  | forallSndPairThenBetaLeft
  | forallPointAtFstBetaLeft
  | forallPointAtFstBetaRight
  | forallConstCompBetaRight
  | forallConstCompBetaLeft
  | forallIffSymApply
  | forallIffTransApply
  | forallFstPairUnaryBetaGrouped
  | forallCtxSub2ReindexBeta
  | forallCtxUnaryReindexBeta
  | forallCtxAndReindexBeta
  | forallCtxOrReindexBeta
  | forallCtxImpReindexBeta
  | forallCtxIffReindexBeta
  | forallCtxNotReindexBeta
  | forallCtxAndCong
  | forallCtxOrCong
  | forallCtxImpCong
  | forallCtxIffCong
  | forallCtxNotCong
  | forallCtxFstPairBetaLeft
  | forallCtxConstCompBetaRight
  | forallCtxFstPairUnaryBetaGrouped
  | forallCtxIffTransApply
  | forallSndPairLiftBetaLeft
  | forallSndPairLiftBetaRight
  | forallSndPairLiftUnaryBeta
  | forallSndPairIdBetaLeft
  | forallSndPairIdBetaRight
  | forallSndPairIdUnaryBeta
  | forallSndAssocBetaLeft
  | forallSndAssocBetaRight
  | forallSndAssocUnaryBeta
  | forallFstPairCompBetaRight
  | forallFstPairCompUnaryBeta
  | forallConstCompUnaryBeta
  | forallClosureBeta
  | existClosureBeta
  | forallLiftFuse => BasisOrigin.betaBasis
  | forallReindex
  | curryUncurry
  | relEqExt
  | forallElim
  | existIntro
  | termImply
  | termAnd
  | termOr
  | termNot
  | termExist
  | forallMono
  | forallAnd
  | existMono
  | forallMonoCtx
  | forallAndCtx
  | forallIffTransCtx
  | forallAndElimL
  | forallIffMp
  | forallIffRefl
  | forallIffSym
  | forallIffTrans
  | forallAndMono
  | forallAndOrDistrib
  | forallAndProjL => BasisOrigin.classicalFirstOrderLogic
  | implyElim
  | iffTrans
  | iffSym
  | iffMp
  | iffMpr => BasisOrigin.primitiveLogic

def all : List BasisName := [
  betaSub2Point,
  betaV0PointArg1,
  betaV0PointArg2,
  betaV0PointUnary,
  betaFstPairPointArg1,
  betaFstPairPointUnary,
  betaWeakeningArg1,
  betaWeakeningArg2,
  forallOrReindexBeta,
  forallAndReindexBeta,
  forallImpReindexBeta,
  forallIffReindexBeta,
  forallNotReindexBeta,
  forallUnaryReindexBeta,
  forallOrCong,
  forallAndCong,
  forallImpCong,
  forallIffCong,
  forallNotCong,
  forallForallCong,
  forallExistCong,
  existReindex,
  forallSub2ReindexBeta,
  forallFstPairBetaLeft,
  forallFstPairBetaRight,
  forallFstPairCompBetaLeft,
  forallFstPairComp2BetaLeft,
  forallFstPairUnaryBeta,
  forallSndPairThenBetaRight,
  forallSndPairThenBetaLeft,
  forallPointAtFstBetaLeft,
  forallPointAtFstBetaRight,
  forallConstCompBetaRight,
  forallConstCompBetaLeft,
  forallIffSymApply,
  forallIffTransApply,
  forallFstPairUnaryBetaGrouped,
  forallCtxSub2ReindexBeta,
  forallCtxUnaryReindexBeta,
  forallCtxAndReindexBeta,
  forallCtxOrReindexBeta,
  forallCtxImpReindexBeta,
  forallCtxIffReindexBeta,
  forallCtxNotReindexBeta,
  forallCtxAndCong,
  forallCtxOrCong,
  forallCtxImpCong,
  forallCtxIffCong,
  forallCtxNotCong,
  forallCtxFstPairBetaLeft,
  forallCtxConstCompBetaRight,
  forallCtxFstPairUnaryBetaGrouped,
  forallCtxIffTransApply,
  forallSndPairLiftBetaLeft,
  forallSndPairLiftBetaRight,
  forallSndPairLiftUnaryBeta,
  forallSndPairIdBetaLeft,
  forallSndPairIdBetaRight,
  forallSndPairIdUnaryBeta,
  forallSndAssocBetaLeft,
  forallSndAssocBetaRight,
  forallSndAssocUnaryBeta,
  forallFstPairCompBetaRight,
  forallFstPairCompUnaryBeta,
  forallConstCompUnaryBeta,
  forallClosureBeta,
  existClosureBeta,
  forallLiftFuse,
  forallReindex,
  curryUncurry,
  relEqExt,
  forallElim,
  existIntro,
  termImply,
  termAnd,
  termOr,
  termNot,
  termExist,
  forallMono,
  forallAnd,
  existMono,
  forallMonoCtx,
  forallAndCtx,
  forallIffTransCtx,
  forallAndElimL,
  forallIffMp,
  forallIffRefl,
  forallIffSym,
  forallIffTrans,
  forallAndMono,
  forallAndOrDistrib,
  forallAndProjL,
  implyElim,
  iffTrans,
  iffSym,
  iffMp,
  iffMpr
]

def allowedCoreNames : List String :=
  all.map coreName

end BasisName

end ContextualHOL
