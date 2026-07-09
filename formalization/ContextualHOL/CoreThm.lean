import ContextualHOL.Substitution

/-!
# Deep-embedded Core statements and provability (M3.2)

`Core.Pred` (the translation target) cannot express reindexed predicates
`P ∘ σ`, so it cannot state the β-basis facts.  This file adds a typed
syntax for the Core fragment the lifting works in:

* `CMap A B` — point-free maps `A → B` (`fst`/`snd`/`pair`/`Cart.weakening`/
  `Cart.i_comb`/named constants);
* `CPred ctx` — predicates `Pred ctx`, with a `comp` node for reindexing and
  `raw` for named predicate constants (schema parameters);
* `CProp` — PC-level statements (`Pred.term`, `iff`, `imply`, `and`);
* `CoreThm : CProp → Prop` — provability from the NAMED Core theorems.

Discipline (see `ma1/m3.md`): every `CoreThm` constructor is a transcription
of one named, checked `.cor` declaration, EXACTLY as schematic as its source
— pinned observation contexts and all.  Two systematic deviations, both in
the sound (restrictive) direction:

* `.cor` definitions are unfolded where the Lean checker would unfold them:
  `sub2 T A B Q f g` is written `Q ∘ ⟨f, g⟩` (`CPred.sub2` below), `Pred.iff`
  stays primitive (it is used opaquely by every axiom).
* element-generic parameters (`b : B` under `Cart.weakening`) become
  name-generic (`CMap.weaken` carries a constant Name) — every name instance
  is an element instance.

Rule-shaped `.cor` items (taking proof arguments at the Lean level, e.g.
`imply_elim`, `Forall_ctx_iffTrans_apply`) become premise-taking
constructors; statement-shaped axioms become axiom constructors.

Derived `.cor` glue (`Forall_iffSym_apply`, `Forall_iffTrans_apply`,
`Forall_fst_pair_unary_beta_grouped`) is re-DERIVED here from the
transcribed constructors, mirroring the `.cor` proof terms — a first
mechanical check that the transcriptions compose the way the originals do.
-/

namespace ContextualHOL

scoped infixr:35 " ×' " => Ty.prod

-- ===== point-free map syntax =====

inductive CMap : Ty -> Ty -> Type where
  | id (A : Ty) : CMap A A                                    -- Cart.i_comb A
  | comp {A B C : Ty} : CMap B C -> CMap A B -> CMap A C      -- g ∘ f
  | fst (A B : Ty) : CMap (A ×' B) A
  | snd (A B : Ty) : CMap (A ×' B) B
  | pair {C A B : Ty} : CMap C A -> CMap C B -> CMap C (A ×' B)
  | weaken (A C : Ty) (c : Name) : CMap C A                   -- Cart.weakening A C c
  | raw (n : Name) (A B : Ty) : CMap A B

-- ===== predicate syntax (Pred ctx, with reindexing) =====

inductive CPred : Ty -> Type where
  | raw (p : Name) (ctx : Ty) : CPred ctx                     -- named Pred constant
  | and {ctx : Ty} : CPred ctx -> CPred ctx -> CPred ctx      -- Pred.and
  | or {ctx : Ty} : CPred ctx -> CPred ctx -> CPred ctx       -- Pred.or
  | imp {ctx : Ty} : CPred ctx -> CPred ctx -> CPred ctx      -- Pred.imply
  | iff {ctx : Ty} : CPred ctx -> CPred ctx -> CPred ctx      -- Pred.iff
  | not {ctx : Ty} : CPred ctx -> CPred ctx                   -- Pred.not
  | all (X : Ty) {ctx : Ty} : CPred (X ×' ctx) -> CPred ctx   -- Forall X ctx
  | ex (X : Ty) {ctx : Ty} : CPred (X ×' ctx) -> CPred ctx    -- Exist X ctx
  | comp {A B : Ty} : CPred A -> CMap B A -> CPred B          -- P ∘ s

-- `sub2 T A B Q f g` unfolds (definitionally, in the Lean checker) to
-- `Q ∘ pair f g`; transcriptions use this spelling.
def CPred.sub2 {T A B : Ty} (Q : CPred (A ×' B)) (f : CMap T A) (g : CMap T B) :
    CPred T :=
  CPred.comp Q (CMap.pair f g)

-- ===== PC-level statement syntax =====

inductive CProp where
  | term : CPred Ty.final -> CProp                            -- Pred.term P
  | iff : CProp -> CProp -> CProp
  | imply : CProp -> CProp -> CProp
  | and : CProp -> CProp -> CProp

-- `Vy Y m` from classical_first_order_logic_new.cor.
def Vy (Y : Ty) (m : CPred (Y ×' Ty.final)) : CProp :=
  CProp.term (CPred.all Y m)

-- ===== embedding the translation target =====

-- read the n-th projection out of a right-nested context type.
def projMap? : (ctx : Ty) -> Nat -> Option ((A : Ty) × CMap ctx A)
  | Ty.prod A B, 0 => some ⟨A, CMap.fst A B⟩
  | Ty.prod A B, Nat.succ n =>
      match projMap? B n with
      | none => none
      | some ⟨C, m⟩ => some ⟨C, CMap.comp m (CMap.snd A B)⟩
  | _, _ => none

def embedTerm? (ctx : Ty) : Core.Term -> Option ((A : Ty) × CMap ctx A)
  | Core.Term.proj n => projMap? ctx n
  | Core.Term.weakening ty _ c => some ⟨ty, CMap.weaken ty ctx c⟩
  | Core.Term.raw n ty => some ⟨ty, CMap.raw n ctx ty⟩

def embedPred? : (ctx : Ty) -> Core.Pred -> Option (CPred ctx)
  | ctx, Core.Pred.atom ctx' A B rel l r =>
      if ctx' = ctx then
        match embedTerm? ctx l, embedTerm? ctx r with
        | some ⟨A', f⟩, some ⟨B', g⟩ =>
            if hA : A' = A then
              if hB : B' = B then
                some (CPred.sub2 (CPred.raw rel (A ×' B)) (hA ▸ f) (hB ▸ g))
              else none
            else none
        | _, _ => none
      else none
  | ctx, Core.Pred.papp ctx' A p arg =>
      if ctx' = ctx then
        match embedTerm? ctx arg with
        | some ⟨A', u⟩ =>
            if hA : A' = A then
              some (CPred.comp (CPred.raw p A) (hA ▸ u))
            else none
        | none => none
      else none
  | ctx, Core.Pred.and ctx' p q =>
      if ctx' = ctx then
        match embedPred? ctx p, embedPred? ctx q with
        | some cp, some cq => some (CPred.and cp cq)
        | _, _ => none
      else none
  | ctx, Core.Pred.or ctx' p q =>
      if ctx' = ctx then
        match embedPred? ctx p, embedPred? ctx q with
        | some cp, some cq => some (CPred.or cp cq)
        | _, _ => none
      else none
  | ctx, Core.Pred.imp ctx' p q =>
      if ctx' = ctx then
        match embedPred? ctx p, embedPred? ctx q with
        | some cp, some cq => some (CPred.imp cp cq)
        | _, _ => none
      else none
  | ctx, Core.Pred.iff ctx' p q =>
      if ctx' = ctx then
        match embedPred? ctx p, embedPred? ctx q with
        | some cp, some cq => some (CPred.iff cp cq)
        | _, _ => none
      else none
  | ctx, Core.Pred.not ctx' p =>
      if ctx' = ctx then
        match embedPred? ctx p with
        | some cp => some (CPred.not cp)
        | none => none
      else none
  | ctx, Core.Pred.all bound ctx' p =>
      if ctx' = ctx then
        match embedPred? (bound ×' ctx) p with
        | some cp => some (CPred.all bound cp)
        | none => none
      else none
  | ctx, Core.Pred.ex bound ctx' p =>
      if ctx' = ctx then
        match embedPred? (bound ×' ctx) p with
        | some cp => some (CPred.ex bound cp)
        | none => none
      else none

-- ===== the substitution/weakening maps and the sequent closure =====

-- ⟨t, id⟩ : ctx → X × ctx  (the substitution generator's map)
def substMap (X ctx : Ty) (t : CMap ctx X) : CMap ctx (X ×' ctx) :=
  CMap.pair t (CMap.id ctx)

-- one-binder lift of a context map
def liftMap (X : Ty) {A B : Ty} (s : CMap B A) : CMap (X ×' B) (X ×' A) :=
  CMap.pair (CMap.fst X B) (CMap.comp s (CMap.snd X B))

-- k-fold lift along a telescope of bound types (innermost first)
def liftMapAlong : (tele : List Ty) -> {A B : Ty} -> CMap B A ->
    CMap (tele.foldr Ty.prod B) (tele.foldr Ty.prod A)
  | [], _, _, s => s
  | X :: rest, _, _, s => liftMap X (liftMapAlong rest s)

-- head-newest assumption chain (see Calculus.lean)
def chain (ctx : Ty) : List (CPred ctx) -> CPred ctx -> CPred ctx
  | [], concl => concl
  | a :: rest, concl => chain ctx rest (CPred.imp a concl)

-- the single-closure reading of Γ | Δ ⊢ φ over the context object ctx = C[Γ]
def seqClosure (ctx : Ty) (assumptions : List (CPred ctx)) (concl : CPred ctx) :
    CProp :=
  Vy ctx (CPred.comp (chain ctx assumptions concl) (CMap.fst ctx Ty.final))

-- ===== provability from the named Core theorems =====

inductive CoreThm : CProp -> Prop where
  -- ---- primitive logical glue (classical_propositional_logic_new.cor) ----
  -- imply_elim (A B : PC) : imply A B -> A -> B
  | mp {a b : CProp} :
      CoreThm (CProp.imply a b) -> CoreThm a -> CoreThm b
  -- iff_mp (A B : PC) : iff A B -> A -> B
  | iffMp {a b : CProp} :
      CoreThm (CProp.iff a b) -> CoreThm a -> CoreThm b
  -- iff_mpr (A B : PC) : iff A B -> B -> A
  | iffMpr {a b : CProp} :
      CoreThm (CProp.iff a b) -> CoreThm b -> CoreThm a
  -- iff_sym (A B : PC) : iff A B -> iff B A
  | iffSym {a b : CProp} :
      CoreThm (CProp.iff a b) -> CoreThm (CProp.iff b a)
  -- iff_trans (A B C : PC) : iff A B -> iff B C -> iff A C
  | iffTrans {a b c : CProp} :
      CoreThm (CProp.iff a b) -> CoreThm (CProp.iff b c) ->
      CoreThm (CProp.iff a c)
  -- ---- classical_first_order_logic_new.cor ----
  -- Forall_mono
  | forallMono (X : Ty) (P Q : CPred (X ×' Ty.final)) :
      CoreThm (CProp.imply (Vy X (CPred.imp P Q))
        (CProp.imply (Vy X P) (Vy X Q)))
  -- Forall_gen
  | forallGen (X : Ty) (psi : CPred Ty.final) (P : CPred (X ×' Ty.final)) :
      CoreThm (CProp.imply
        (Vy X (CPred.imp (CPred.comp psi (CMap.snd X Ty.final)) P))
        (CProp.imply (CProp.term psi) (CProp.term (CPred.all X P))))
  -- Exist_gen
  | existGen (X : Ty) (psi : CPred Ty.final) (P : CPred (X ×' Ty.final)) :
      CoreThm (CProp.imply
        (Vy X (CPred.imp P (CPred.comp psi (CMap.snd X Ty.final))))
        (CProp.imply (CProp.term (CPred.ex X P)) (CProp.term psi)))
  -- Forall_iffRefl / Forall_iffSym / Forall_iffTrans (∀-lifted tautologies)
  | forallIffRefl (X : Ty) (A : CPred (X ×' Ty.final)) :
      CoreThm (Vy X (CPred.iff A A))
  | forallIffSym (X : Ty) (A B : CPred (X ×' Ty.final)) :
      CoreThm (Vy X (CPred.imp (CPred.iff A B) (CPred.iff B A)))
  | forallIffTrans (X : Ty) (A B C : CPred (X ×' Ty.final)) :
      CoreThm (Vy X (CPred.imp (CPred.iff A B)
        (CPred.imp (CPred.iff B C) (CPred.iff A C))))
  -- Forall_reindex (Beck–Chevalley for ∀)
  | forallReindex (X Y0 Y : Ty) (R : CPred (X ×' Y0)) (f : CMap Y Y0) :
      CoreThm (Vy Y (CPred.iff
        (CPred.comp (CPred.all X R) (CMap.comp f (CMap.fst Y Ty.final)))
        (CPred.all X (CPred.comp R (CMap.pair
          (CMap.fst X (Y ×' Ty.final))
          (CMap.comp f (CMap.comp (CMap.fst Y Ty.final)
            (CMap.snd X (Y ×' Ty.final)))))))))
  -- ---- beta_basis.cor: one-binder reindexing homomorphisms ----
  -- Exist_reindex (Beck–Chevalley for ∃)
  | existReindex (X Y0 Y : Ty) (R : CPred (X ×' Y0)) (f : CMap Y Y0) :
      CoreThm (Vy Y (CPred.iff
        (CPred.comp (CPred.ex X R) (CMap.comp f (CMap.fst Y Ty.final)))
        (CPred.ex X (CPred.comp R (CMap.pair
          (CMap.fst X (Y ×' Ty.final))
          (CMap.comp f (CMap.comp (CMap.fst Y Ty.final)
            (CMap.snd X (Y ×' Ty.final)))))))))
  -- Forall_sub2_reindex_beta
  | forallSub2ReindexBeta (I Z A B : Ty) (Q : CPred (A ×' B))
      (f : CMap Z A) (g : CMap Z B) (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.sub2 Q f g) s)
        (CPred.sub2 Q (CMap.comp f s) (CMap.comp g s))))
  -- Forall_unary_reindex_beta
  | forallUnaryReindexBeta (I Z A : Ty) (P : CPred A)
      (u : CMap Z A) (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.comp P u) s)
        (CPred.comp P (CMap.comp u s))))
  -- Forall_and/or/imp/iff/not_reindex_beta
  | forallAndReindexBeta (I Y : Ty) (s : CMap (I ×' Ty.final) Y)
      (P Q : CPred Y) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.and P Q) s)
        (CPred.and (CPred.comp P s) (CPred.comp Q s))))
  | forallOrReindexBeta (I Y : Ty) (s : CMap (I ×' Ty.final) Y)
      (P Q : CPred Y) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.or P Q) s)
        (CPred.or (CPred.comp P s) (CPred.comp Q s))))
  | forallImpReindexBeta (I Y : Ty) (s : CMap (I ×' Ty.final) Y)
      (P Q : CPred Y) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.imp P Q) s)
        (CPred.imp (CPred.comp P s) (CPred.comp Q s))))
  | forallIffReindexBeta (I Y : Ty) (s : CMap (I ×' Ty.final) Y)
      (P Q : CPred Y) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.iff P Q) s)
        (CPred.iff (CPred.comp P s) (CPred.comp Q s))))
  | forallNotReindexBeta (I Y : Ty) (s : CMap (I ×' Ty.final) Y)
      (P : CPred Y) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.not P) s)
        (CPred.not (CPred.comp P s))))
  -- ---- beta_basis.cor: one-binder congruences ----
  | forallAndCong (I : Ty) (A A' B B' : CPred (I ×' Ty.final)) :
      CoreThm (CProp.imply (Vy I (CPred.iff A A'))
        (CProp.imply (Vy I (CPred.iff B B'))
          (Vy I (CPred.iff (CPred.and A B) (CPred.and A' B')))))
  | forallOrCong (I : Ty) (A A' B B' : CPred (I ×' Ty.final)) :
      CoreThm (CProp.imply (Vy I (CPred.iff A A'))
        (CProp.imply (Vy I (CPred.iff B B'))
          (Vy I (CPred.iff (CPred.or A B) (CPred.or A' B')))))
  | forallImpCong (I : Ty) (A A' B B' : CPred (I ×' Ty.final)) :
      CoreThm (CProp.imply (Vy I (CPred.iff A A'))
        (CProp.imply (Vy I (CPred.iff B B'))
          (Vy I (CPred.iff (CPred.imp A B) (CPred.imp A' B')))))
  | forallIffCong (I : Ty) (A A' B B' : CPred (I ×' Ty.final)) :
      CoreThm (CProp.imply (Vy I (CPred.iff A A'))
        (CProp.imply (Vy I (CPred.iff B B'))
          (Vy I (CPred.iff (CPred.iff A B) (CPred.iff A' B')))))
  | forallNotCong (I : Ty) (A A' : CPred (I ×' Ty.final)) :
      CoreThm (CProp.imply (Vy I (CPred.iff A A'))
        (Vy I (CPred.iff (CPred.not A) (CPred.not A'))))
  -- Forall_ForallCong / Forall_ExistCong (two-binder observation, as in .cor)
  | forallForallCong (X I : Ty) (P Q : CPred (X ×' (I ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all I (CPred.all X (CPred.iff P Q))))
        (Vy I (CPred.iff (CPred.all X P) (CPred.all X Q))))
  | forallExistCong (X I : Ty) (P Q : CPred (X ×' (I ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all I (CPred.all X (CPred.iff P Q))))
        (Vy I (CPred.iff (CPred.ex X P) (CPred.ex X Q))))
  -- ---- beta_basis.cor: one-binder atom-slot product/terminal β ----
  | forallFstPairBetaLeft (I A B C : Ty) (Q : CPred (A ×' C))
      (f : CMap (I ×' Ty.final) A) (g : CMap (I ×' Ty.final) B)
      (h : CMap (I ×' Ty.final) C) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.fst A B) (CMap.pair f g)) h)
        (CPred.sub2 Q f h)))
  | forallFstPairBetaRight (I A B C : Ty) (Q : CPred (C ×' A))
      (h : CMap (I ×' Ty.final) C) (f : CMap (I ×' Ty.final) A)
      (g : CMap (I ×' Ty.final) B) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q h (CMap.comp (CMap.fst A B) (CMap.pair f g)))
        (CPred.sub2 Q h f)))
  | forallFstPairCompBetaLeft (I Z A B C : Ty) (Q : CPred (A ×' C))
      (f : CMap Z A) (g : CMap Z B) (s : CMap (I ×' Ty.final) Z)
      (h : CMap (I ×' Ty.final) C) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.fst A B) (CMap.comp (CMap.pair f g) s)) h)
        (CPred.sub2 Q (CMap.comp f s) h)))
  | forallFstPairComp2BetaLeft (I W Z A B C : Ty) (Q : CPred (A ×' C))
      (f : CMap Z A) (g : CMap Z B) (s : CMap W Z) (r : CMap (I ×' Ty.final) W)
      (h : CMap (I ×' Ty.final) C) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q
          (CMap.comp (CMap.fst A B) (CMap.comp (CMap.comp (CMap.pair f g) s) r)) h)
        (CPred.sub2 Q (CMap.comp f (CMap.comp s r)) h)))
  | forallFstPairUnaryBeta (I A B : Ty) (P : CPred A)
      (f : CMap (I ×' Ty.final) A) (g : CMap (I ×' Ty.final) B) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp (CPred.comp P (CMap.fst A B)) (CMap.pair f g))
        (CPred.comp P f)))
  | forallSndPairThenBetaRight (I A B C D : Ty) (Q : CPred (C ×' D))
      (h : CMap (I ×' Ty.final) C) (k : CMap B D)
      (f : CMap (I ×' Ty.final) A) (g : CMap (I ×' Ty.final) B) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q h (CMap.comp (CMap.comp k (CMap.snd A B)) (CMap.pair f g)))
        (CPred.sub2 Q h (CMap.comp k g))))
  | forallSndPairThenBetaLeft (I A B C D : Ty) (Q : CPred (D ×' C))
      (k : CMap B D) (h : CMap (I ×' Ty.final) C)
      (f : CMap (I ×' Ty.final) A) (g : CMap (I ×' Ty.final) B) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.comp k (CMap.snd A B)) (CMap.pair f g)) h)
        (CPred.sub2 Q (CMap.comp k g) h)))
  -- Forall_const_comp_beta_right / _left (name-generic where .cor is
  -- element-generic; sound restriction)
  | forallConstCompBetaRight (I A B Z : Ty) (Q : CPred (A ×' B))
      (f : CMap (I ×' Ty.final) A) (c : Name) (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q f (CMap.comp (CMap.weaken B Z c) s))
        (CPred.sub2 Q f (CMap.weaken B (I ×' Ty.final) c))))
  | forallConstCompBetaLeft (I A B Z : Ty) (Q : CPred (A ×' B))
      (c : Name) (h : CMap (I ×' Ty.final) B) (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.weaken A Z c) s) h)
        (CPred.sub2 Q (CMap.weaken A (I ×' Ty.final) c) h)))
  -- ---- beta_basis.cor: the two-binder (ctx) slice, exactly as pinned ----
  | forallCtxSub2ReindexBeta (I J Z A B : Ty) (Q : CPred (A ×' B))
      (f : CMap Z A) (g : CMap Z B) (s : CMap (I ×' (J ×' Ty.final)) Z) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.sub2 Q f g) s)
        (CPred.sub2 Q (CMap.comp f s) (CMap.comp g s))))))
  | forallCtxUnaryReindexBeta (I J Z A : Ty) (P : CPred A)
      (u : CMap Z A) (s : CMap (I ×' (J ×' Ty.final)) Z) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.comp P u) s)
        (CPred.comp P (CMap.comp u s))))))
  | forallCtxAndReindexBeta (I J Y : Ty) (s : CMap (I ×' (J ×' Ty.final)) Y)
      (P Q : CPred Y) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.and P Q) s)
        (CPred.and (CPred.comp P s) (CPred.comp Q s))))))
  | forallCtxOrReindexBeta (I J Y : Ty) (s : CMap (I ×' (J ×' Ty.final)) Y)
      (P Q : CPred Y) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.or P Q) s)
        (CPred.or (CPred.comp P s) (CPred.comp Q s))))))
  | forallCtxImpReindexBeta (I J Y : Ty) (s : CMap (I ×' (J ×' Ty.final)) Y)
      (P Q : CPred Y) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.imp P Q) s)
        (CPred.imp (CPred.comp P s) (CPred.comp Q s))))))
  | forallCtxIffReindexBeta (I J Y : Ty) (s : CMap (I ×' (J ×' Ty.final)) Y)
      (P Q : CPred Y) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.iff P Q) s)
        (CPred.iff (CPred.comp P s) (CPred.comp Q s))))))
  | forallCtxNotReindexBeta (I J Y : Ty) (s : CMap (I ×' (J ×' Ty.final)) Y)
      (P : CPred Y) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp (CPred.not P) s)
        (CPred.not (CPred.comp P s))))))
  | forallCtxAndCong (I J : Ty) (A A' B B' : CPred (I ×' (J ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all J (CPred.all I (CPred.iff A A'))))
        (CProp.imply
          (CProp.term (CPred.all J (CPred.all I (CPred.iff B B'))))
          (CProp.term (CPred.all J (CPred.all I (CPred.iff
            (CPred.and A B) (CPred.and A' B')))))))
  | forallCtxOrCong (I J : Ty) (A A' B B' : CPred (I ×' (J ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all J (CPred.all I (CPred.iff A A'))))
        (CProp.imply
          (CProp.term (CPred.all J (CPred.all I (CPred.iff B B'))))
          (CProp.term (CPred.all J (CPred.all I (CPred.iff
            (CPred.or A B) (CPred.or A' B')))))))
  | forallCtxImpCong (I J : Ty) (A A' B B' : CPred (I ×' (J ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all J (CPred.all I (CPred.iff A A'))))
        (CProp.imply
          (CProp.term (CPred.all J (CPred.all I (CPred.iff B B'))))
          (CProp.term (CPred.all J (CPred.all I (CPred.iff
            (CPred.imp A B) (CPred.imp A' B')))))))
  | forallCtxIffCong (I J : Ty) (A A' B B' : CPred (I ×' (J ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all J (CPred.all I (CPred.iff A A'))))
        (CProp.imply
          (CProp.term (CPred.all J (CPred.all I (CPred.iff B B'))))
          (CProp.term (CPred.all J (CPred.all I (CPred.iff
            (CPred.iff A B) (CPred.iff A' B')))))))
  | forallCtxNotCong (I J : Ty) (A A' : CPred (I ×' (J ×' Ty.final))) :
      CoreThm (CProp.imply
        (CProp.term (CPred.all J (CPred.all I (CPred.iff A A'))))
        (CProp.term (CPred.all J (CPred.all I (CPred.iff
          (CPred.not A) (CPred.not A'))))))
  | forallCtxFstPairBetaLeft (I J A B C : Ty) (Q : CPred (A ×' C))
      (f : CMap (I ×' (J ×' Ty.final)) A) (g : CMap (I ×' (J ×' Ty.final)) B)
      (h : CMap (I ×' (J ×' Ty.final)) C) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.fst A B) (CMap.pair f g)) h)
        (CPred.sub2 Q f h)))))
  | forallCtxConstCompBetaRight (I J A B Z : Ty) (Q : CPred (A ×' B))
      (f : CMap (I ×' (J ×' Ty.final)) A) (c : Name)
      (s : CMap (I ×' (J ×' Ty.final)) Z) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.sub2 Q f (CMap.comp (CMap.weaken B Z c) s))
        (CPred.sub2 Q f (CMap.weaken B (I ×' (J ×' Ty.final)) c))))))
  | forallCtxFstPairUnaryBetaGrouped (I J A B : Ty) (P : CPred A)
      (f : CMap (I ×' (J ×' Ty.final)) A) (g : CMap (I ×' (J ×' Ty.final)) B) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff
        (CPred.comp P (CMap.comp (CMap.fst A B) (CMap.pair f g)))
        (CPred.comp P f)))))
  -- Forall_ctx_iffTrans_apply (rule-shaped in .cor)
  | forallCtxIffTransApply (I J : Ty) (A B C : CPred (I ×' (J ×' Ty.final))) :
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff A B)))) ->
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff B C)))) ->
      CoreThm (CProp.term (CPred.all J (CPred.all I (CPred.iff A C))))
  -- ---- beta_basis.cor: M3 additions (lifted-map cleanup, canonical spine) ----
  -- Forall_snd_pair_lift_beta_left / _right / _unary
  | forallSndPairLiftBetaLeft (I W A B B0 C D : Ty) (Q : CPred (D ×' C))
      (m : CMap B D) (f : CMap W A) (g : CMap B0 B) (h : CMap W B0)
      (w : CMap (I ×' Ty.final) W) (h' : CMap (I ×' Ty.final) C) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.comp m (CMap.snd A B))
          (CMap.comp (CMap.pair f (CMap.comp g h)) w)) h')
        (CPred.sub2 Q (CMap.comp m (CMap.comp g (CMap.comp h w))) h')))
  | forallSndPairLiftBetaRight (I W A B B0 C D : Ty) (Q : CPred (C ×' D))
      (h' : CMap (I ×' Ty.final) C) (m : CMap B D) (f : CMap W A)
      (g : CMap B0 B) (h : CMap W B0) (w : CMap (I ×' Ty.final) W) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q h' (CMap.comp (CMap.comp m (CMap.snd A B))
          (CMap.comp (CMap.pair f (CMap.comp g h)) w)))
        (CPred.sub2 Q h' (CMap.comp m (CMap.comp g (CMap.comp h w))))))
  | forallSndPairLiftUnaryBeta (I W A B B0 D : Ty) (P : CPred D)
      (m : CMap B D) (f : CMap W A) (g : CMap B0 B) (h : CMap W B0)
      (w : CMap (I ×' Ty.final) W) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp P (CMap.comp (CMap.comp m (CMap.snd A B))
          (CMap.comp (CMap.pair f (CMap.comp g h)) w)))
        (CPred.comp P (CMap.comp m (CMap.comp g (CMap.comp h w))))))
  -- Forall_snd_pair_id_beta_left / _right / _unary (i_comb absorption)
  | forallSndPairIdBetaLeft (I A B C D : Ty) (Q : CPred (D ×' C))
      (m : CMap B D) (f : CMap B A) (w : CMap (I ×' Ty.final) B)
      (h' : CMap (I ×' Ty.final) C) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.comp m (CMap.snd A B))
          (CMap.comp (CMap.pair f (CMap.id B)) w)) h')
        (CPred.sub2 Q (CMap.comp m w) h')))
  | forallSndPairIdBetaRight (I A B C D : Ty) (Q : CPred (C ×' D))
      (h' : CMap (I ×' Ty.final) C) (m : CMap B D) (f : CMap B A)
      (w : CMap (I ×' Ty.final) B) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q h' (CMap.comp (CMap.comp m (CMap.snd A B))
          (CMap.comp (CMap.pair f (CMap.id B)) w)))
        (CPred.sub2 Q h' (CMap.comp m w))))
  | forallSndPairIdUnaryBeta (I A B D : Ty) (P : CPred D)
      (m : CMap B D) (f : CMap B A) (w : CMap (I ×' Ty.final) B) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp P (CMap.comp (CMap.comp m (CMap.snd A B))
          (CMap.comp (CMap.pair f (CMap.id B)) w)))
        (CPred.comp P (CMap.comp m w))))
  -- Forall_snd_assoc_beta_left / _right / _unary (spine regrouping)
  | forallSndAssocBetaLeft (I A B C D : Ty) (Q : CPred (D ×' C))
      (m : CMap B D) (w : CMap (I ×' Ty.final) (A ×' B))
      (h' : CMap (I ×' Ty.final) C) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q (CMap.comp (CMap.comp m (CMap.snd A B)) w) h')
        (CPred.sub2 Q (CMap.comp m (CMap.comp (CMap.snd A B) w)) h')))
  | forallSndAssocBetaRight (I A B C D : Ty) (Q : CPred (C ×' D))
      (h' : CMap (I ×' Ty.final) C) (m : CMap B D)
      (w : CMap (I ×' Ty.final) (A ×' B)) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q h' (CMap.comp (CMap.comp m (CMap.snd A B)) w))
        (CPred.sub2 Q h' (CMap.comp m (CMap.comp (CMap.snd A B) w)))))
  | forallSndAssocUnaryBeta (I A B D : Ty) (P : CPred D)
      (m : CMap B D) (w : CMap (I ×' Ty.final) (A ×' B)) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp P (CMap.comp (CMap.comp m (CMap.snd A B)) w))
        (CPred.comp P (CMap.comp m (CMap.comp (CMap.snd A B) w)))))
  -- Forall_fst_pair_comp_beta_right / _unary
  | forallFstPairCompBetaRight (I Z A B C : Ty) (Q : CPred (C ×' A))
      (h : CMap (I ×' Ty.final) C) (f : CMap Z A) (g : CMap Z B)
      (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.sub2 Q h (CMap.comp (CMap.fst A B) (CMap.comp (CMap.pair f g) s)))
        (CPred.sub2 Q h (CMap.comp f s))))
  | forallFstPairCompUnaryBeta (I Z A B : Ty) (P : CPred A)
      (f : CMap Z A) (g : CMap Z B) (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp P (CMap.comp (CMap.fst A B) (CMap.comp (CMap.pair f g) s)))
        (CPred.comp P (CMap.comp f s))))
  -- Forall_const_comp_unary_beta (name-generic weakening, as elsewhere)
  | forallConstCompUnaryBeta (I A Z : Ty) (P : CPred A)
      (c : Name) (s : CMap (I ×' Ty.final) Z) :
      CoreThm (Vy I (CPred.iff
        (CPred.comp P (CMap.comp (CMap.weaken A Z c) s))
        (CPred.comp P (CMap.weaken A (I ×' Ty.final) c))))
  -- ---- beta_basis.cor: M3 additions (closure/fusion, quantifier cases) ----
  -- Forall_closure_beta / Exist_closure_beta
  | forallClosureBeta (X Y : Ty) (R : CPred (X ×' Y)) :
      CoreThm (Vy Y (CPred.iff
        (CPred.comp (CPred.all X R) (CMap.fst Y Ty.final))
        (CPred.all X (CPred.comp R (CMap.pair
          (CMap.fst X (Y ×' Ty.final))
          (CMap.comp (CMap.fst Y Ty.final) (CMap.snd X (Y ×' Ty.final))))))))
  | existClosureBeta (X Y : Ty) (R : CPred (X ×' Y)) :
      CoreThm (Vy Y (CPred.iff
        (CPred.comp (CPred.ex X R) (CMap.fst Y Ty.final))
        (CPred.ex X (CPred.comp R (CMap.pair
          (CMap.fst X (Y ×' Ty.final))
          (CMap.comp (CMap.fst Y Ty.final) (CMap.snd X (Y ×' Ty.final))))))))
  -- Forall_lift_fuse (rule-shaped: the generic-depth Beck–Chevalley seam)
  | forallLiftFuse (X Y Y0 : Ty) (s : CMap Y Y0)
      (A : CPred (X ×' Y0)) (B : CPred (X ×' Y)) :
      CoreThm (Vy (X ×' Y) (CPred.iff
        (CPred.comp A (CMap.comp
          (CMap.pair (CMap.fst X Y) (CMap.comp s (CMap.snd X Y)))
          (CMap.fst (X ×' Y) Ty.final)))
        (CPred.comp B (CMap.fst (X ×' Y) Ty.final)))) ->
      CoreThm (CProp.term (CPred.all Y (CPred.all X (CPred.iff
        (CPred.comp A (CMap.pair
          (CMap.fst X (Y ×' Ty.final))
          (CMap.comp s (CMap.comp (CMap.fst Y Ty.final)
            (CMap.snd X (Y ×' Ty.final))))))
        (CPred.comp B (CMap.pair
          (CMap.fst X (Y ×' Ty.final))
          (CMap.comp (CMap.fst Y Ty.final) (CMap.snd X (Y ×' Ty.final)))))))))

namespace CoreThm

-- ===== derived glue, mirroring the .cor noncomputable defs =====

-- Forall_iffSym_apply (derived in beta_basis.cor from Forall_mono + Forall_iffSym)
theorem forallIffSymApply (X : Ty) (A B : CPred (X ×' Ty.final))
    (h : CoreThm (Vy X (CPred.iff A B))) :
    CoreThm (Vy X (CPred.iff B A)) :=
  mp (mp (forallMono X (CPred.iff A B) (CPred.iff B A)) (forallIffSym X A B)) h

-- Forall_iffTrans_apply (derived in beta_basis.cor)
theorem forallIffTransApply (X : Ty) (A B C : CPred (X ×' Ty.final))
    (h1 : CoreThm (Vy X (CPred.iff A B)))
    (h2 : CoreThm (Vy X (CPred.iff B C))) :
    CoreThm (Vy X (CPred.iff A C)) :=
  mp
    (mp (forallMono X (CPred.iff B C) (CPred.iff A C))
      (mp
        (mp (forallMono X (CPred.iff A B)
          (CPred.imp (CPred.iff B C) (CPred.iff A C)))
          (forallIffTrans X A B C))
        h1))
    h2

-- Forall_fst_pair_unary_beta_grouped (derived in beta_basis.cor)
theorem forallFstPairUnaryBetaGrouped (I A B : Ty) (P : CPred A)
    (f : CMap (I ×' Ty.final) A) (g : CMap (I ×' Ty.final) B) :
    CoreThm (Vy I (CPred.iff
      (CPred.comp P (CMap.comp (CMap.fst A B) (CMap.pair f g)))
      (CPred.comp P f))) :=
  forallIffTransApply I
    (CPred.comp P (CMap.comp (CMap.fst A B) (CMap.pair f g)))
    (CPred.comp (CPred.comp P (CMap.fst A B)) (CMap.pair f g))
    (CPred.comp P f)
    (forallIffSymApply I
      (CPred.comp (CPred.comp P (CMap.fst A B)) (CMap.pair f g))
      (CPred.comp P (CMap.comp (CMap.fst A B) (CMap.pair f g)))
      (forallUnaryReindexBeta I (A ×' B) A P (CMap.fst A B) (CMap.pair f g)))
    (forallFstPairUnaryBeta I A B P f g)

-- ===== the connective engine for the soundness induction =====
--
-- Each step: given that the children's reindexed forms are observationally
-- interchangeable, so are the connective nodes' — via reindex-beta on both
-- sides plus the congruence.  These are exactly the composition patterns the
-- `SubstEquiv`-soundness induction will use, one per connective; proving
-- them now smoke-tests the transcriptions.

theorem compAndStep (I Y Y' : Ty) (s : CMap (I ×' Ty.final) Y)
    (t : CMap (I ×' Ty.final) Y') (p q : CPred Y) (p' q' : CPred Y')
    (hp : CoreThm (Vy I (CPred.iff (CPred.comp p s) (CPred.comp p' t))))
    (hq : CoreThm (Vy I (CPred.iff (CPred.comp q s) (CPred.comp q' t)))) :
    CoreThm (Vy I (CPred.iff
      (CPred.comp (CPred.and p q) s) (CPred.comp (CPred.and p' q') t))) :=
  forallIffTransApply I _ _ _
    (forallAndReindexBeta I Y s p q)
    (forallIffTransApply I _ _ _
      (mp (mp (forallAndCong I _ _ _ _) hp) hq)
      (forallIffSymApply I _ _ (forallAndReindexBeta I Y' t p' q')))

theorem compOrStep (I Y Y' : Ty) (s : CMap (I ×' Ty.final) Y)
    (t : CMap (I ×' Ty.final) Y') (p q : CPred Y) (p' q' : CPred Y')
    (hp : CoreThm (Vy I (CPred.iff (CPred.comp p s) (CPred.comp p' t))))
    (hq : CoreThm (Vy I (CPred.iff (CPred.comp q s) (CPred.comp q' t)))) :
    CoreThm (Vy I (CPred.iff
      (CPred.comp (CPred.or p q) s) (CPred.comp (CPred.or p' q') t))) :=
  forallIffTransApply I _ _ _
    (forallOrReindexBeta I Y s p q)
    (forallIffTransApply I _ _ _
      (mp (mp (forallOrCong I _ _ _ _) hp) hq)
      (forallIffSymApply I _ _ (forallOrReindexBeta I Y' t p' q')))

theorem compImpStep (I Y Y' : Ty) (s : CMap (I ×' Ty.final) Y)
    (t : CMap (I ×' Ty.final) Y') (p q : CPred Y) (p' q' : CPred Y')
    (hp : CoreThm (Vy I (CPred.iff (CPred.comp p s) (CPred.comp p' t))))
    (hq : CoreThm (Vy I (CPred.iff (CPred.comp q s) (CPred.comp q' t)))) :
    CoreThm (Vy I (CPred.iff
      (CPred.comp (CPred.imp p q) s) (CPred.comp (CPred.imp p' q') t))) :=
  forallIffTransApply I _ _ _
    (forallImpReindexBeta I Y s p q)
    (forallIffTransApply I _ _ _
      (mp (mp (forallImpCong I _ _ _ _) hp) hq)
      (forallIffSymApply I _ _ (forallImpReindexBeta I Y' t p' q')))

theorem compIffStep (I Y Y' : Ty) (s : CMap (I ×' Ty.final) Y)
    (t : CMap (I ×' Ty.final) Y') (p q : CPred Y) (p' q' : CPred Y')
    (hp : CoreThm (Vy I (CPred.iff (CPred.comp p s) (CPred.comp p' t))))
    (hq : CoreThm (Vy I (CPred.iff (CPred.comp q s) (CPred.comp q' t)))) :
    CoreThm (Vy I (CPred.iff
      (CPred.comp (CPred.iff p q) s) (CPred.comp (CPred.iff p' q') t))) :=
  forallIffTransApply I _ _ _
    (forallIffReindexBeta I Y s p q)
    (forallIffTransApply I _ _ _
      (mp (mp (forallIffCong I _ _ _ _) hp) hq)
      (forallIffSymApply I _ _ (forallIffReindexBeta I Y' t p' q')))

theorem compNotStep (I Y Y' : Ty) (s : CMap (I ×' Ty.final) Y)
    (t : CMap (I ×' Ty.final) Y') (p : CPred Y) (p' : CPred Y')
    (hp : CoreThm (Vy I (CPred.iff (CPred.comp p s) (CPred.comp p' t)))) :
    CoreThm (Vy I (CPred.iff
      (CPred.comp (CPred.not p) s) (CPred.comp (CPred.not p') t))) :=
  forallIffTransApply I _ _ _
    (forallNotReindexBeta I Y s p)
    (forallIffTransApply I _ _ _
      (mp (forallNotCong I _ _) hp)
      (forallIffSymApply I _ _ (forallNotReindexBeta I Y' t p')))

end CoreThm

-- ===== the M3.2 soundness target (statement only; proof is the next stage) =====

-- observation of "P reindexed along the k-fold lift of ⟨t, id⟩ equals Q" over
-- the flattened new context, through one binder.
def substSoundGoal (X Γctx : Ty) (tcm : CMap Γctx X) (tele : List Ty)
    (cP : CPred (tele.foldr Ty.prod (X ×' Γctx)))
    (cQ : CPred (tele.foldr Ty.prod Γctx)) : CProp :=
  Vy (tele.foldr Ty.prod Γctx) (CPred.iff
    (CPred.comp cP (CMap.comp
      (liftMapAlong tele (substMap X Γctx tcm))
      (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final)))
    (CPred.comp cQ (CMap.fst (tele.foldr Ty.prod Γctx) Ty.final)))

-- The `SubstEquiv`-soundness statement itself is proved (relationally, via
-- `PredEmbedIs`) as `substEquiv_sound` in `ContextualHOL/SubstSound.lean`:
-- the telescope `tele` lists the Ψ bound types innermost-first, so
-- `tele.length = k` and `tele.foldr Ty.prod Γctx = C[Ψ ++ Γ]`.

end ContextualHOL
