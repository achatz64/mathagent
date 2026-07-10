import ContextualHOL.CoreThm

/-!
# SubstEquiv soundness (M3.2): the certificate is redeemable as CoreThm evidence

For every `SubstEquiv tc k newCtx P Q` derivation, the reindexing of (the
embedding of) `P` along the k-fold binder lift of `⟨tc, id⟩` is CoreThm-
provably observationally equal to (the embedding of) `Q`, observed through
ONE binder over the flattened context — `substSoundGoal`.

Structure:
* embedding RELATIONS (`ProjMapIs`, `TermEmbedIs`, `PredEmbedIs`) — the
  relational form of `embedTerm?`/`embedPred?`, avoiding Option/Sigma casts;
* `SlotObs` — an abstract "observation slot" bundling the five β-facts each
  slot position provides; instantiated three times (left/right atom slot,
  unary predicate slot), so every map-cleanup lemma is proved once;
* the spine-cleanup lemmas: `projNorm` (normalize a projection against an
  opaque tail), `peelInside`/`peelBoundary`/`peelBeyond` (clean a projection
  through the k-fold lifted substitution map, by cases on the projection
  index against the telescope);
* `termClean` — the full Core-term cleanup (the atom/papp workhorse);
* `substEquiv_sound` — the main induction.

Terms `Core.Term.raw` are NOT embeddable (`TermEmbedIs` has no raw case):
raw is the escape hatch, with no reindexing behaviour to certify.
-/

namespace ContextualHOL

open CoreThm

-- ===== embedding relations =====

-- `m` is the fst/snd spine reading projection `n` out of context type `D`.
inductive ProjMapIs : (D : Ty) -> Nat -> (A : Ty) -> CMap D A -> Prop where
  | zero (A B : Ty) : ProjMapIs (A ×' B) 0 A (CMap.fst A B)
  | succ (T B A : Ty) (n : Nat) (m : CMap B A) :
      ProjMapIs B n A m ->
      ProjMapIs (T ×' B) (n + 1) A (CMap.comp m (CMap.snd T B))

-- canonical right-nested reading of projection `n` continued by tail `w`:
-- fst ∘ (snd ∘ (snd ∘ (... ∘ w))).
inductive ProjCanonIs {Z : Ty} : (D : Ty) -> Nat -> CMap Z D -> (A : Ty) ->
    CMap Z A -> Prop where
  | zero (A B : Ty) (w : CMap Z (A ×' B)) :
      ProjCanonIs (A ×' B) 0 w A (CMap.comp (CMap.fst A B) w)
  | succ (T B A : Ty) (n : Nat) (w : CMap Z (T ×' B)) (c : CMap Z A) :
      ProjCanonIs B n (CMap.comp (CMap.snd T B) w) A c ->
      ProjCanonIs (T ×' B) (n + 1) w A c

-- w' is w with the whole telescope peeled by a right-nested snd spine.
inductive SndSpineIs {Z : Ty} (base : Ty) : (tele : List Ty) ->
    CMap Z (tele.foldr Ty.prod base) -> CMap Z base -> Prop where
  | nil (w : CMap Z base) : SndSpineIs base [] w w
  | cons (T : Ty) (tele : List Ty) (w : CMap Z (T ×' tele.foldr Ty.prod base))
      (w' : CMap Z base) :
      SndSpineIs base tele
        (CMap.comp (CMap.snd T (tele.foldr Ty.prod base)) w) w' ->
      SndSpineIs base (T :: tele) w w'

inductive TermEmbedIs (ctx : Ty) : Core.Term -> (A : Ty) -> CMap ctx A -> Prop where
  | proj (n : Nat) (A : Ty) (m : CMap ctx A) :
      ProjMapIs ctx n A m -> TermEmbedIs ctx (Core.Term.proj n) A m
  | weaken (ty ctx0 : Ty) (c : Name) :
      TermEmbedIs ctx (Core.Term.weakening ty ctx0 c) ty (CMap.weaken ty ctx c)

inductive PredEmbedIs : (ctx : Ty) -> Core.Pred -> CPred ctx -> Prop where
  | atom (ctx A B : Ty) (rel : Name) (l r : Core.Term)
      (fl : CMap ctx A) (fr : CMap ctx B) :
      TermEmbedIs ctx l A fl -> TermEmbedIs ctx r B fr ->
      PredEmbedIs ctx (Core.Pred.atom ctx A B rel l r)
        (CPred.sub2 (CPred.raw rel (A ×' B)) fl fr)
  | papp (ctx A : Ty) (p : Name) (arg : Core.Term) (u : CMap ctx A) :
      TermEmbedIs ctx arg A u ->
      PredEmbedIs ctx (Core.Pred.papp ctx A p arg)
        (CPred.comp (CPred.raw p A) u)
  | and (ctx : Ty) (p q : Core.Pred) (cp cq : CPred ctx) :
      PredEmbedIs ctx p cp -> PredEmbedIs ctx q cq ->
      PredEmbedIs ctx (Core.Pred.and ctx p q) (CPred.and cp cq)
  | or (ctx : Ty) (p q : Core.Pred) (cp cq : CPred ctx) :
      PredEmbedIs ctx p cp -> PredEmbedIs ctx q cq ->
      PredEmbedIs ctx (Core.Pred.or ctx p q) (CPred.or cp cq)
  | imp (ctx : Ty) (p q : Core.Pred) (cp cq : CPred ctx) :
      PredEmbedIs ctx p cp -> PredEmbedIs ctx q cq ->
      PredEmbedIs ctx (Core.Pred.imp ctx p q) (CPred.imp cp cq)
  | iff (ctx : Ty) (p q : Core.Pred) (cp cq : CPred ctx) :
      PredEmbedIs ctx p cp -> PredEmbedIs ctx q cq ->
      PredEmbedIs ctx (Core.Pred.iff ctx p q) (CPred.iff cp cq)
  | not (ctx : Ty) (p : Core.Pred) (cp : CPred ctx) :
      PredEmbedIs ctx p cp ->
      PredEmbedIs ctx (Core.Pred.not ctx p) (CPred.not cp)
  | all (bound ctx : Ty) (p : Core.Pred) (cp : CPred (bound ×' ctx)) :
      PredEmbedIs (bound ×' ctx) p cp ->
      PredEmbedIs ctx (Core.Pred.all bound ctx p) (CPred.all bound cp)
  | ex (bound ctx : Ty) (p : Core.Pred) (cp : CPred (bound ×' ctx)) :
      PredEmbedIs (bound ×' ctx) p cp ->
      PredEmbedIs ctx (Core.Pred.ex bound ctx p) (CPred.ex bound cp)

-- ===== spine bookkeeping lemmas =====

theorem projCanonIs_exists {D : Ty} {n : Nat} {A : Ty} {m : CMap D A}
    (hm : ProjMapIs D n A m) :
    forall {Z : Ty} (w : CMap Z D), exists c, ProjCanonIs D n w A c := by
  induction hm with
  | zero A B =>
      intro Z w
      exact ⟨CMap.comp (CMap.fst A B) w, ProjCanonIs.zero A B w⟩
  | succ T B A n m _ ih =>
      intro Z w
      obtain ⟨c, hc⟩ := ih (CMap.comp (CMap.snd T B) w)
      exact ⟨c, ProjCanonIs.succ T B A n w c hc⟩

theorem sndSpineIs_exists (base : Ty) :
    forall (tele : List Ty) {Z : Ty} (w : CMap Z (tele.foldr Ty.prod base)),
      exists w', SndSpineIs base tele w w' := by
  intro tele
  induction tele with
  | nil => intro Z w; exact ⟨w, SndSpineIs.nil w⟩
  | cons T rest ih =>
      intro Z w
      obtain ⟨w', hw'⟩ := ih (CMap.comp (CMap.snd T (rest.foldr Ty.prod base)) w)
      exact ⟨w', SndSpineIs.cons T rest w w' hw'⟩

-- extend a canonical projection over the base through the telescope spine.
theorem projCanonIs_extend (base : Ty) {Z : Ty} :
    forall (tele : List Ty) (i : Nat)
      (w : CMap Z (tele.foldr Ty.prod base)) (w' : CMap Z base)
      (A : Ty) (c : CMap Z A),
      SndSpineIs base tele w w' -> ProjCanonIs base i w' A c ->
      ProjCanonIs (tele.foldr Ty.prod base) (i + tele.length) w A c := by
  intro tele
  induction tele with
  | nil =>
      intro i w w' A c hspine hc
      cases hspine
      simpa using hc
  | cons T rest ih =>
      intro i w w' A c hspine hc
      cases hspine with
      | cons _ _ _ _ hrest =>
          have hlen : i + (T :: rest).length = (i + rest.length) + 1 := by
            simp only [List.length_cons]
            omega
          rw [hlen]
          exact ProjCanonIs.succ T (rest.foldr Ty.prod base) A (i + rest.length)
            w c (ih i _ w' A c hrest hc)

-- a projection landing exactly on the telescope boundary reads the X slot.
theorem projMapIs_boundary (X Γctx : Ty) :
    forall (tele : List Ty) (A : Ty)
      (m : CMap (tele.foldr Ty.prod (X ×' Γctx)) A),
      ProjMapIs (tele.foldr Ty.prod (X ×' Γctx)) tele.length A m -> A = X := by
  intro tele
  induction tele with
  | nil =>
      intro A m hm
      cases hm
      rfl
  | cons T rest ih =>
      intro A m hm
      cases hm with
      | succ _ _ _ _ m' hm' => exact ih A m' hm'

-- a projection strictly beyond the boundary reads out of the base context.
theorem projMapIs_beyond (X Γctx : Ty) :
    forall (tele : List Ty) (i : Nat) (A : Ty)
      (m : CMap (tele.foldr Ty.prod (X ×' Γctx)) A),
      ProjMapIs (tele.foldr Ty.prod (X ×' Γctx)) (tele.length + i + 1) A m ->
      exists m', ProjMapIs Γctx i A m' := by
  intro tele
  induction tele with
  | nil =>
      intro i A m hm
      simp only [List.length_nil, Nat.zero_add] at hm
      cases hm with
      | succ _ _ _ _ m' hm' => exact ⟨m', hm'⟩
  | cons T rest ih =>
      intro i A m hm
      have hlen : (T :: rest).length + i + 1 = (rest.length + i + 1) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hlen] at hm
      cases hm with
      | succ _ _ _ _ m' hm' => exact ih i A m' hm'

-- ===== the abstract observation slot =====

-- One "slot" through which map equations are observed at PC under one ∀.
-- Fields are exactly the five M3 β-facts, instantiated per slot position.
structure SlotObs (I A0 : Ty) where
  view : CMap (I ×' Ty.final) A0 -> CPred (I ×' Ty.final)
  sndAssoc : forall (A B : Ty) (m : CMap B A0)
      (w : CMap (I ×' Ty.final) (A ×' B)),
    CoreThm (Vy I (CPred.iff
      (view (CMap.comp (CMap.comp m (CMap.snd A B)) w))
      (view (CMap.comp m (CMap.comp (CMap.snd A B) w)))))
  sndPairLift : forall (W A B B0 : Ty) (m : CMap B A0) (f : CMap W A)
      (g : CMap B0 B) (h : CMap W B0) (w : CMap (I ×' Ty.final) W),
    CoreThm (Vy I (CPred.iff
      (view (CMap.comp (CMap.comp m (CMap.snd A B))
        (CMap.comp (CMap.pair f (CMap.comp g h)) w)))
      (view (CMap.comp m (CMap.comp g (CMap.comp h w))))))
  sndPairId : forall (A B : Ty) (m : CMap B A0) (f : CMap B A)
      (w : CMap (I ×' Ty.final) B),
    CoreThm (Vy I (CPred.iff
      (view (CMap.comp (CMap.comp m (CMap.snd A B))
        (CMap.comp (CMap.pair f (CMap.id B)) w)))
      (view (CMap.comp m w))))
  fstPairComp : forall (Z B : Ty) (f : CMap Z A0) (g : CMap Z B)
      (s : CMap (I ×' Ty.final) Z),
    CoreThm (Vy I (CPred.iff
      (view (CMap.comp (CMap.fst A0 B) (CMap.comp (CMap.pair f g) s)))
      (view (CMap.comp f s))))
  constComp : forall (Z : Ty) (c : Name) (s : CMap (I ×' Ty.final) Z),
    CoreThm (Vy I (CPred.iff
      (view (CMap.comp (CMap.weaken A0 Z c) s))
      (view (CMap.weaken A0 (I ×' Ty.final) c))))

def leftObs (I C A0 : Ty) (Q : CPred (A0 ×' C)) (h : CMap (I ×' Ty.final) C) :
    SlotObs I A0 where
  view m := CPred.sub2 Q m h
  sndAssoc A B m w := CoreThm.forallSndAssocBetaLeft I A B C A0 Q m w h
  sndPairLift W A B B0 m f g hh w :=
    CoreThm.forallSndPairLiftBetaLeft I W A B B0 C A0 Q m f g hh w h
  sndPairId A B m f w := CoreThm.forallSndPairIdBetaLeft I A B C A0 Q m f w h
  fstPairComp Z B f g s := CoreThm.forallFstPairCompBetaLeft I Z A0 B C Q f g s h
  constComp Z c s := CoreThm.forallConstCompBetaLeft I A0 C Z Q c h s

def rightObs (I C A0 : Ty) (Q : CPred (C ×' A0)) (h : CMap (I ×' Ty.final) C) :
    SlotObs I A0 where
  view m := CPred.sub2 Q h m
  sndAssoc A B m w := CoreThm.forallSndAssocBetaRight I A B C A0 Q h m w
  sndPairLift W A B B0 m f g hh w :=
    CoreThm.forallSndPairLiftBetaRight I W A B B0 C A0 Q h m f g hh w
  sndPairId A B m f w := CoreThm.forallSndPairIdBetaRight I A B C A0 Q h m f w
  fstPairComp Z B f g s := CoreThm.forallFstPairCompBetaRight I Z A0 B C Q h f g s
  constComp Z c s := CoreThm.forallConstCompBetaRight I C A0 Z Q h c s

def unaryObs (I A0 : Ty) (P : CPred A0) : SlotObs I A0 where
  view m := CPred.comp P m
  sndAssoc A B m w := CoreThm.forallSndAssocUnaryBeta I A B A0 P m w
  sndPairLift W A B B0 m f g hh w :=
    CoreThm.forallSndPairLiftUnaryBeta I W A B B0 A0 P m f g hh w
  sndPairId A B m f w := CoreThm.forallSndPairIdUnaryBeta I A B A0 P m f w
  fstPairComp Z B f g s := CoreThm.forallFstPairCompUnaryBeta I Z A0 B P f g s
  constComp Z c s := CoreThm.forallConstCompUnaryBeta I A0 Z P c s

namespace SlotObs

-- T1: normalize a projection spine against an opaque tail.
theorem projNorm {I A0 : Ty} (o : SlotObs I A0) :
    forall {n : Nat} {D : Ty} {m : CMap D A0}
      (w : CMap (I ×' Ty.final) D) (c : CMap (I ×' Ty.final) A0),
      ProjMapIs D n A0 m -> ProjCanonIs D n w A0 c ->
      CoreThm (Vy I (CPred.iff (o.view (CMap.comp m w)) (o.view c))) := by
  intro n
  induction n with
  | zero =>
      intro D m w c hm hc
      cases hm
      cases hc
      exact CoreThm.forallIffRefl I (o.view _)
  | succ n ih =>
      intro D m w c hm hc
      cases hm with
      | succ _ _ _ _ m' hm' =>
          cases hc with
          | succ _ _ _ _ _ _ hc' =>
              exact CoreThm.forallIffTransApply I _ _ _
                (o.sndAssoc _ _ m' w)
                (ih _ c hm' hc')

-- T2a: the projection lands strictly inside the telescope.  Generic in the
-- base map σ0 (only the LIFT layers are peeled), so it serves both the
-- substitution generator (σ0 = ⟨t, id⟩) and the weakening generator
-- (σ0 = snd).
theorem peelInside {I A0 : Ty} (o : SlotObs I A0) (B0 B1 : Ty)
    (σ0 : CMap B1 B0) :
    forall (tele : List Ty) (n : Nat)
      (m : CMap (tele.foldr Ty.prod B0) A0)
      (w : CMap (I ×' Ty.final) (tele.foldr Ty.prod B1))
      (c : CMap (I ×' Ty.final) A0),
      n < tele.length ->
      ProjMapIs (tele.foldr Ty.prod B0) n A0 m ->
      ProjCanonIs (tele.foldr Ty.prod B1) n w A0 c ->
      CoreThm (Vy I (CPred.iff
        (o.view (CMap.comp m
          (CMap.comp (liftMapAlong tele σ0) w)))
        (o.view c))) := by
  intro tele
  induction tele with
  | nil =>
      intro n m w c hlt
      exact absurd hlt (Nat.not_lt_zero n)
  | cons T rest ih =>
      intro n m w c hlt hm hc
      cases n with
      | zero =>
          cases hm
          cases hc
          exact o.fstPairComp _ _ _ _ _
      | succ n =>
          cases hm with
          | succ _ _ _ _ m' hm' =>
              cases hc with
              | succ _ _ _ _ _ _ hc' =>
                  exact CoreThm.forallIffTransApply I _ _ _
                    (o.sndPairLift _ _ _ _ m' _
                      (liftMapAlong rest σ0) _ w)
                    (ih n m' _ c (Nat.lt_of_succ_lt_succ hlt) hm' hc')

-- T2b: the projection lands exactly on the substituted slot.
theorem peelBoundary {I X : Ty} (o : SlotObs I X) (Γctx : Ty)
    (tcm : CMap Γctx X) :
    forall (tele : List Ty)
      (m : CMap (tele.foldr Ty.prod (X ×' Γctx)) X)
      (w : CMap (I ×' Ty.final) (tele.foldr Ty.prod Γctx))
      (w' : CMap (I ×' Ty.final) Γctx),
      ProjMapIs (tele.foldr Ty.prod (X ×' Γctx)) tele.length X m ->
      SndSpineIs Γctx tele w w' ->
      CoreThm (Vy I (CPred.iff
        (o.view (CMap.comp m
          (CMap.comp (liftMapAlong tele (substMap X Γctx tcm)) w)))
        (o.view (CMap.comp tcm w')))) := by
  intro tele
  induction tele with
  | nil =>
      intro m w w' hm hspine
      cases hspine
      cases hm
      exact o.fstPairComp _ _ _ _ _
  | cons T rest ih =>
      intro m w w' hm hspine
      cases hm with
      | succ _ _ _ _ m' hm' =>
          cases hspine with
          | cons _ _ _ _ hrest =>
              exact CoreThm.forallIffTransApply I _ _ _
                (o.sndPairLift _ _ _ _ m' _
                  (liftMapAlong rest (substMap X Γctx tcm)) _ w)
                (ih m' _ w' hm' hrest)

-- T2c: the projection lands strictly beyond the substituted slot.
theorem peelBeyond {I A0 : Ty} (o : SlotObs I A0) (X Γctx : Ty)
    (tcm : CMap Γctx X) :
    forall (tele : List Ty) (i : Nat)
      (m : CMap (tele.foldr Ty.prod (X ×' Γctx)) A0)
      (w : CMap (I ×' Ty.final) (tele.foldr Ty.prod Γctx))
      (w' : CMap (I ×' Ty.final) Γctx)
      (c : CMap (I ×' Ty.final) A0),
      ProjMapIs (tele.foldr Ty.prod (X ×' Γctx)) (tele.length + i + 1) A0 m ->
      SndSpineIs Γctx tele w w' ->
      ProjCanonIs Γctx i w' A0 c ->
      CoreThm (Vy I (CPred.iff
        (o.view (CMap.comp m
          (CMap.comp (liftMapAlong tele (substMap X Γctx tcm)) w)))
        (o.view c))) := by
  intro tele
  induction tele with
  | nil =>
      intro i m w w' c hm hspine hc
      cases hspine
      simp only [List.length_nil, Nat.zero_add] at hm
      cases hm with
      | succ _ _ _ _ m' hm' =>
          exact CoreThm.forallIffTransApply I _ _ _
            (o.sndPairId _ _ m' tcm w)
            (o.projNorm w c hm' hc)
  | cons T rest ih =>
      intro i m w w' c hm hspine hc
      have hlen : (T :: rest).length + i + 1 = (rest.length + i + 1) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hlen] at hm
      cases hm with
      | succ _ _ _ _ m' hm' =>
          cases hspine with
          | cons _ _ _ _ hrest =>
              exact CoreThm.forallIffTransApply I _ _ _
                (o.sndPairLift _ _ _ _ m' _
                  (liftMapAlong rest (substMap X Γctx tcm)) _ w)
                (ih i m' _ w' c hm' hrest hc)

-- the full Core-term cleanup: (embed u) ∘ (σk ∘ w) is observationally the
-- embedding of `substCoreTerm k tc u` continued by w.
theorem termClean {I A0 : Ty} (o : SlotObs I A0) (X Γctx : Ty)
    (tc : Core.Term) (tcm : CMap Γctx X)
    (htc : TermEmbedIs Γctx tc X tcm) :
    forall (tele : List Ty) (u : Core.Term)
      (fl : CMap (tele.foldr Ty.prod (X ×' Γctx)) A0)
      (fl' : CMap (tele.foldr Ty.prod Γctx) A0)
      (w : CMap (I ×' Ty.final) (tele.foldr Ty.prod Γctx)),
      TermEmbedIs (tele.foldr Ty.prod (X ×' Γctx)) u A0 fl ->
      TermEmbedIs (tele.foldr Ty.prod Γctx)
        (substCoreTerm tele.length (tele.foldr Ty.prod Γctx) tc u) A0 fl' ->
      CoreThm (Vy I (CPred.iff
        (o.view (CMap.comp fl
          (CMap.comp (liftMapAlong tele (substMap X Γctx tcm)) w)))
        (o.view (CMap.comp fl' w)))) := by
  intro tele u fl fl' w hfl hfl'
  cases u with
  | raw name ty => cases hfl
  | weakening ty ctx0 c0 =>
      simp only [substCoreTerm] at hfl'
      cases hfl
      cases hfl'
      exact CoreThm.forallIffTransApply I _ _ _
        (o.constComp (tele.foldr Ty.prod (X ×' Γctx)) c0
          (CMap.comp (liftMapAlong tele (substMap X Γctx tcm)) w))
        (CoreThm.forallIffSymApply I _ _
          (o.constComp (tele.foldr Ty.prod Γctx) c0 w))
  | proj n =>
      cases hfl with
      | proj _ _ _ hm =>
      rcases Nat.lt_trichotomy n tele.length with hlt | heq | hgt
      · -- inside the telescope: substCoreTerm keeps proj n
        simp only [substCoreTerm] at hfl'
        rw [if_pos hlt] at hfl'
        cases hfl' with
        | proj _ _ _ hm' =>
            obtain ⟨c, hc⟩ := projCanonIs_exists hm' w
            exact CoreThm.forallIffTransApply I _ _ _
              (o.peelInside (X ×' Γctx) Γctx (substMap X Γctx tcm)
                tele n _ w c hlt hm hc)
              (CoreThm.forallIffSymApply I _ _ (o.projNorm w c hm' hc))
      · -- the boundary: substCoreTerm inserts (the shift of) tc
        subst heq
        have hA : A0 = X := projMapIs_boundary X Γctx tele A0 _ hm
        subst hA
        simp [substCoreTerm, Nat.lt_irrefl] at hfl'
        obtain ⟨w', hspine⟩ := sndSpineIs_exists Γctx tele w
        cases htc with
        | proj i _ _ htcm =>
            simp only [shiftCoreTerm] at hfl'
            cases hfl' with
            | proj _ _ _ hm' =>
                obtain ⟨c, hc⟩ := projCanonIs_exists htcm w'
                exact CoreThm.forallIffTransApply I _ _ _
                  (CoreThm.forallIffTransApply I _ _ _
                    (o.peelBoundary Γctx tcm tele _ w w' hm hspine)
                    (o.projNorm w' c htcm hc))
                  (CoreThm.forallIffSymApply I _ _
                    (o.projNorm w c hm'
                      (projCanonIs_extend Γctx tele i w w' A0 c hspine hc)))
        | weaken ty ctx0 c0 =>
            simp only [shiftCoreTerm] at hfl'
            cases hfl'
            exact CoreThm.forallIffTransApply I _ _ _
              (CoreThm.forallIffTransApply I _ _ _
                (o.peelBoundary Γctx _ tele _ w w' hm hspine)
                (o.constComp Γctx c0 w'))
              (CoreThm.forallIffSymApply I _ _
                (o.constComp (tele.foldr Ty.prod Γctx) c0 w))
      · -- beyond the boundary: substCoreTerm shifts down by one
        have hne : ¬ (n < tele.length) := by omega
        have hne' : ¬ (n = tele.length) := by omega
        simp only [substCoreTerm] at hfl'
        rw [if_neg hne, if_neg hne'] at hfl'
        cases hfl' with
        | proj _ _ _ hm' =>
            obtain ⟨w', hspine⟩ := sndSpineIs_exists Γctx tele w
            have hn : n = tele.length + (n - tele.length - 1) + 1 := by omega
            rw [hn] at hm
            obtain ⟨mΓ, hmΓ⟩ :=
              projMapIs_beyond X Γctx tele (n - tele.length - 1) A0 _ hm
            obtain ⟨c, hc⟩ := projCanonIs_exists hmΓ w'
            have hn' : n - 1 = (n - tele.length - 1) + tele.length := by omega
            rw [hn'] at hm'
            exact CoreThm.forallIffTransApply I _ _ _
              (o.peelBeyond X Γctx tcm tele (n - tele.length - 1) _ w w' c
                hm hspine hc)
              (CoreThm.forallIffSymApply I _ _
                (o.projNorm w c hm'
                  (projCanonIs_extend Γctx tele (n - tele.length - 1)
                    w w' A0 c hspine hc)))

end SlotObs

-- ===== the main soundness theorem =====

theorem substEquiv_sound (X Γctx : Ty) (tc : Core.Term) (tcm : CMap Γctx X)
    (htc : TermEmbedIs Γctx tc X tcm) :
    forall (P : Core.Pred) (tele : List Ty) (Q : Core.Pred)
      (cP : CPred (tele.foldr Ty.prod (X ×' Γctx)))
      (cQ : CPred (tele.foldr Ty.prod Γctx)),
      SubstEquiv tc tele.length (tele.foldr Ty.prod Γctx) P Q ->
      PredEmbedIs (tele.foldr Ty.prod (X ×' Γctx)) P cP ->
      PredEmbedIs (tele.foldr Ty.prod Γctx) Q cQ ->
      CoreThm (substSoundGoal X Γctx tcm tele cP cQ) := by
  intro P
  induction P with
  | atom ctxP A B rel l r =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE
      cases hcP with
      | atom _ _ _ _ _ _ fl fr hl hr =>
      cases hcQ with
      | atom _ _ _ _ _ _ fl' fr' hl' hr' =>
      -- reindex both sides into the slots, clean each slot, meet in the middle
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallSub2ReindexBeta _ _ _ _ (CPred.raw rel (A ×' B)) fl fr
          (CMap.comp (liftMapAlong tele (substMap X Γctx tcm))
            (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final)))
        (CoreThm.forallIffTransApply _ _ _ _
          ((leftObs _ _ _ (CPred.raw rel (A ×' B))
              (CMap.comp fr (CMap.comp (liftMapAlong tele (substMap X Γctx tcm))
                (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final)))).termClean
            X Γctx tc tcm htc tele l fl fl'
            (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final) hl hl')
          (CoreThm.forallIffTransApply _ _ _ _
            ((rightObs _ _ _ (CPred.raw rel (A ×' B))
                (CMap.comp fl' (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final))).termClean
              X Γctx tc tcm htc tele r fr fr'
              (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final) hr hr')
            (CoreThm.forallIffSymApply _ _ _
              (CoreThm.forallSub2ReindexBeta _ _ _ _ (CPred.raw rel (A ×' B))
                fl' fr' (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final)))))
  | papp ctxP A p arg =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE
      cases hcP with
      | papp _ _ _ _ u hu =>
      cases hcQ with
      | papp _ _ _ _ u' hu' =>
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallUnaryReindexBeta _ _ _ (CPred.raw p A) u
          (CMap.comp (liftMapAlong tele (substMap X Γctx tcm))
            (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final)))
        (CoreThm.forallIffTransApply _ _ _ _
          ((unaryObs _ _ (CPred.raw p A)).termClean X Γctx tc tcm htc tele
            arg u u' (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final) hu hu')
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.forallUnaryReindexBeta _ _ _ (CPred.raw p A) u'
              (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final))))
  | and ctxP p q ihp ihq =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | and _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | and _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | and _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compAndStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | or ctxP p q ihp ihq =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | or _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | or _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | or _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compOrStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | imp ctxP p q ihp ihq =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | imp _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | imp _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | imp _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compImpStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | iff ctxP p q ihp ihq =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | iff _ _ _ _ p' _ q' hp hq =>
      cases hcP with
      | iff _ _ _ cp cq' hcp hcq =>
      cases hcQ with
      | iff _ _ _ cp' cq'' hcp' hcq' =>
      exact CoreThm.compIffStep _ _ _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
        (ihq tele q' cq' cq'' hq hcq hcq')
  | not ctxP p ihp =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | not _ _ _ _ p' hp =>
      cases hcP with
      | not _ _ cp hcp =>
      cases hcQ with
      | not _ _ cp' hcp' =>
      exact CoreThm.compNotStep _ _ _ _ _ _ _
        (ihp tele p' cp cp' hp hcp hcp')
  | all bound ctxP p ihp =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | all _ _ _ _ _ p' hp =>
      cases hcP with
      | all _ _ _ cp hcp =>
      cases hcQ with
      | all _ _ _ cq hcq =>
      have ihFused :=
        CoreThm.forallLiftFuse bound (tele.foldr Ty.prod Γctx)
          (tele.foldr Ty.prod (X ×' Γctx))
          (liftMapAlong tele (substMap X Γctx tcm)) cp cq
          (ihp (bound :: tele) p' cp cq hp hcp hcq)
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallReindex bound (tele.foldr Ty.prod (X ×' Γctx))
          (tele.foldr Ty.prod Γctx) cp
          (liftMapAlong tele (substMap X Γctx tcm)))
        (CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.mp
            (CoreThm.forallForallCong bound (tele.foldr Ty.prod Γctx) _ _)
            ihFused)
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.forallClosureBeta bound (tele.foldr Ty.prod Γctx) cq)))
  | ex bound ctxP p ihp =>
      intro tele Q cP cQ hSE hcP hcQ
      cases hSE with
      | ex _ _ _ _ _ p' hp =>
      cases hcP with
      | ex _ _ _ cp hcp =>
      cases hcQ with
      | ex _ _ _ cq hcq =>
      have ihFused :=
        CoreThm.forallLiftFuse bound (tele.foldr Ty.prod Γctx)
          (tele.foldr Ty.prod (X ×' Γctx))
          (liftMapAlong tele (substMap X Γctx tcm)) cp cq
          (ihp (bound :: tele) p' cp cq hp hcp hcq)
      exact CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.existReindex bound (tele.foldr Ty.prod (X ×' Γctx))
          (tele.foldr Ty.prod Γctx) cp
          (liftMapAlong tele (substMap X Γctx tcm)))
        (CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.mp
            (CoreThm.forallExistCong bound (tele.foldr Ty.prod Γctx) _ _)
            ihFused)
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.existClosureBeta bound (tele.foldr Ty.prod Γctx) cq)))

-- the closed (top-level) instance, matching translate_substFormula_closed.
theorem substEquiv_sound_closed (X Γctx : Ty) (tc : Core.Term)
    (tcm : CMap Γctx X) (htc : TermEmbedIs Γctx tc X tcm)
    (P Q : Core.Pred) (cP : CPred (X ×' Γctx)) (cQ : CPred Γctx)
    (hSE : SubstEquiv tc 0 Γctx P Q)
    (hcP : PredEmbedIs (X ×' Γctx) P cP)
    (hcQ : PredEmbedIs Γctx Q cQ) :
    CoreThm (Vy Γctx (CPred.iff
      (CPred.comp cP (CMap.comp (substMap X Γctx tcm)
        (CMap.fst Γctx Ty.final)))
      (CPred.comp cQ (CMap.fst Γctx Ty.final)))) :=
  substEquiv_sound X Γctx tc tcm htc P [] Q cP cQ hSE hcP hcQ

end ContextualHOL
