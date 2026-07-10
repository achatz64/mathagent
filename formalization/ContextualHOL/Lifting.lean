import ContextualHOL.SubstSound
import ContextualHOL.Calculus

/-!
# Sequent lifting, propositional layer (M3.3, slice 1)

The Core reading of a contextual sequent `Γ | Δ ⊢ φ` is the single-closure
form

  `SeqLift G Δ' φ'  =  Vy G (chainF Δ' φ')`

over the context object `G = C[Γ]`, where `Δ'`/`φ'` are the (embedded)
translations composed with the closure projection `fst G Final`, and
`chainF` is the HEAD-NEWEST implication chain — so discharging the newest
assumption (`Proves.impIntro`) is definitional at this level.

This file provides the propositional engine for the lifting induction:

* `vy*` — reasoning under the single closure (modus ponens via
  `Forall_mono` at `X := G`, weakening via `Forall_impK`, the transports);
* `chain*` — the same lifted through an arbitrary assumption chain
  (`chainMP` iterates the Y-generic S; `chainOfVy` iterates K; `chainHyp`
  is the assumption rule);
* `dist*` — one-step distribution of the closure map through each
  connective (the `Forall_*_reindex_beta` facts at `s := fst G Final`),
  composable into a distribution tree for any schema shape;
* `seq*` — one lemma per propositional rule of `Proves`, stated over the
  UNDISTRIBUTED conclusion shapes the translation produces.

Everything is generic in `G`: no per-depth facts anywhere.
-/

namespace ContextualHOL

open CoreThm

-- head-newest assumption chain at the observation context
def chainF (G : Ty) : List (CPred (G ×' Ty.final)) -> CPred (G ×' Ty.final) ->
    CPred (G ×' Ty.final)
  | [], c => c
  | a :: rest, c => chainF G rest (CPred.imp a c)

-- the single-closure sequent reading
def SeqLift (G : Ty) (Δ : List (CPred (G ×' Ty.final)))
    (c : CPred (G ×' Ty.final)) : CProp :=
  Vy G (chainF G Δ c)

-- ===== reasoning under the single closure =====

theorem vyMP {G : Ty} {a b : CPred (G ×' Ty.final)}
    (h1 : CoreThm (Vy G (CPred.imp a b))) (h2 : CoreThm (Vy G a)) :
    CoreThm (Vy G b) :=
  CoreThm.mp (CoreThm.mp (CoreThm.forallMono G a b) h1) h2

theorem vyWeaken {G : Ty} {m : CPred (G ×' Ty.final)}
    (a : CPred (G ×' Ty.final)) (h : CoreThm (Vy G m)) :
    CoreThm (Vy G (CPred.imp a m)) :=
  vyMP (CoreThm.forallImpK G m a) h

theorem vyI {G : Ty} (a : CPred (G ×' Ty.final)) :
    CoreThm (Vy G (CPred.imp a a)) :=
  vyMP
    (vyMP (CoreThm.forallImpS G a (CPred.imp a a) a)
      (CoreThm.forallImpK G a (CPred.imp a a)))
    (CoreThm.forallImpK G a a)

theorem vyIffMp {G : Ty} {a b : CPred (G ×' Ty.final)}
    (h : CoreThm (Vy G (CPred.iff a b))) : CoreThm (Vy G (CPred.imp a b)) :=
  vyMP (CoreThm.forallIffProjL G a b) h

theorem vyIffMpr {G : Ty} {a b : CPred (G ×' Ty.final)}
    (h : CoreThm (Vy G (CPred.iff a b))) : CoreThm (Vy G (CPred.imp b a)) :=
  vyMP (CoreThm.forallIffProjR G a b) h

theorem vyImpCong {G : Ty} {a a' b b' : CPred (G ×' Ty.final)}
    (h1 : CoreThm (Vy G (CPred.iff a a')))
    (h2 : CoreThm (Vy G (CPred.iff b b'))) :
    CoreThm (Vy G (CPred.iff (CPred.imp a b) (CPred.imp a' b'))) :=
  CoreThm.mp (CoreThm.mp (CoreThm.forallImpCong G a a' b b') h1) h2

theorem vyAndCong {G : Ty} {a a' b b' : CPred (G ×' Ty.final)}
    (h1 : CoreThm (Vy G (CPred.iff a a')))
    (h2 : CoreThm (Vy G (CPred.iff b b'))) :
    CoreThm (Vy G (CPred.iff (CPred.and a b) (CPred.and a' b'))) :=
  CoreThm.mp (CoreThm.mp (CoreThm.forallAndCong G a a' b b') h1) h2

theorem vyOrCong {G : Ty} {a a' b b' : CPred (G ×' Ty.final)}
    (h1 : CoreThm (Vy G (CPred.iff a a')))
    (h2 : CoreThm (Vy G (CPred.iff b b'))) :
    CoreThm (Vy G (CPred.iff (CPred.or a b) (CPred.or a' b'))) :=
  CoreThm.mp (CoreThm.mp (CoreThm.forallOrCong G a a' b b') h1) h2

theorem vyIffCong {G : Ty} {a a' b b' : CPred (G ×' Ty.final)}
    (h1 : CoreThm (Vy G (CPred.iff a a')))
    (h2 : CoreThm (Vy G (CPred.iff b b'))) :
    CoreThm (Vy G (CPred.iff (CPred.iff a b) (CPred.iff a' b'))) :=
  CoreThm.mp (CoreThm.mp (CoreThm.forallIffCong G a a' b b') h1) h2

theorem vyNotCong {G : Ty} {a a' : CPred (G ×' Ty.final)}
    (h : CoreThm (Vy G (CPred.iff a a'))) :
    CoreThm (Vy G (CPred.iff (CPred.not a) (CPred.not a'))) :=
  CoreThm.mp (CoreThm.forallNotCong G a a') h

-- ===== the chain layer =====

theorem chainOfVy {G : Ty} (Δ : List (CPred (G ×' Ty.final)))
    {m : CPred (G ×' Ty.final)} (h : CoreThm (Vy G m)) :
    CoreThm (SeqLift G Δ m) := by
  induction Δ generalizing m with
  | nil => exact h
  | cons a rest ih => exact ih (vyWeaken a h)

theorem chainMP {G : Ty} (Δ : List (CPred (G ×' Ty.final)))
    {a b : CPred (G ×' Ty.final)}
    (h1 : CoreThm (SeqLift G Δ (CPred.imp a b)))
    (h2 : CoreThm (SeqLift G Δ a)) :
    CoreThm (SeqLift G Δ b) := by
  induction Δ generalizing a b with
  | nil => exact vyMP h1 h2
  | cons x rest ih =>
      exact ih (ih (chainOfVy rest (CoreThm.forallImpS G x a b)) h1) h2

theorem chainMono {G : Ty} (Δ : List (CPred (G ×' Ty.final)))
    {a b : CPred (G ×' Ty.final)}
    (h : CoreThm (Vy G (CPred.imp a b))) (h2 : CoreThm (SeqLift G Δ a)) :
    CoreThm (SeqLift G Δ b) :=
  chainMP Δ (chainOfVy Δ h) h2

theorem chainIffMp {G : Ty} (Δ : List (CPred (G ×' Ty.final)))
    {a b : CPred (G ×' Ty.final)}
    (h : CoreThm (Vy G (CPred.iff a b))) :
    CoreThm (SeqLift G Δ a) -> CoreThm (SeqLift G Δ b) :=
  chainMono Δ (vyIffMp h)

theorem chainIffMpr {G : Ty} (Δ : List (CPred (G ×' Ty.final)))
    {a b : CPred (G ×' Ty.final)}
    (h : CoreThm (Vy G (CPred.iff a b))) :
    CoreThm (SeqLift G Δ b) -> CoreThm (SeqLift G Δ a) :=
  chainMono Δ (vyIffMpr h)

theorem chainHyp {G : Ty} (Δ : List (CPred (G ×' Ty.final)))
    {a : CPred (G ×' Ty.final)} (h : a ∈ Δ) :
    CoreThm (SeqLift G Δ a) := by
  induction Δ with
  | nil => exact absurd h (by simp)
  | cons x rest ih =>
      cases h with
      | head => exact chainOfVy rest (vyI a)
      | tail _ h' => exact chainMono rest (CoreThm.forallImpK G a x) (ih h')

-- ===== distribution of the closure map through connectives =====
--
-- Each `dist*` step: given that the children distribute, so does the node.
-- Leaves are `CoreThm.forallIffRefl`.  Generic in the map `f`, so the same
-- trees serve any reindexing, not only the closure projection.

theorem distImp {G : Ty} {f : CMap (G ×' Ty.final) G} {u v : CPred G}
    {U V : CPred (G ×' Ty.final)}
    (hU : CoreThm (Vy G (CPred.iff (CPred.comp u f) U)))
    (hV : CoreThm (Vy G (CPred.iff (CPred.comp v f) V))) :
    CoreThm (Vy G (CPred.iff (CPred.comp (CPred.imp u v) f) (CPred.imp U V))) :=
  CoreThm.forallIffTransApply G _ _ _
    (CoreThm.forallImpReindexBeta G G f u v)
    (vyImpCong hU hV)

theorem distAnd {G : Ty} {f : CMap (G ×' Ty.final) G} {u v : CPred G}
    {U V : CPred (G ×' Ty.final)}
    (hU : CoreThm (Vy G (CPred.iff (CPred.comp u f) U)))
    (hV : CoreThm (Vy G (CPred.iff (CPred.comp v f) V))) :
    CoreThm (Vy G (CPred.iff (CPred.comp (CPred.and u v) f) (CPred.and U V))) :=
  CoreThm.forallIffTransApply G _ _ _
    (CoreThm.forallAndReindexBeta G G f u v)
    (vyAndCong hU hV)

theorem distOr {G : Ty} {f : CMap (G ×' Ty.final) G} {u v : CPred G}
    {U V : CPred (G ×' Ty.final)}
    (hU : CoreThm (Vy G (CPred.iff (CPred.comp u f) U)))
    (hV : CoreThm (Vy G (CPred.iff (CPred.comp v f) V))) :
    CoreThm (Vy G (CPred.iff (CPred.comp (CPred.or u v) f) (CPred.or U V))) :=
  CoreThm.forallIffTransApply G _ _ _
    (CoreThm.forallOrReindexBeta G G f u v)
    (vyOrCong hU hV)

theorem distIff {G : Ty} {f : CMap (G ×' Ty.final) G} {u v : CPred G}
    {U V : CPred (G ×' Ty.final)}
    (hU : CoreThm (Vy G (CPred.iff (CPred.comp u f) U)))
    (hV : CoreThm (Vy G (CPred.iff (CPred.comp v f) V))) :
    CoreThm (Vy G (CPred.iff (CPred.comp (CPred.iff u v) f) (CPred.iff U V))) :=
  CoreThm.forallIffTransApply G _ _ _
    (CoreThm.forallIffReindexBeta G G f u v)
    (vyIffCong hU hV)

theorem distNot {G : Ty} {f : CMap (G ×' Ty.final) G} {u : CPred G}
    {U : CPred (G ×' Ty.final)}
    (hU : CoreThm (Vy G (CPred.iff (CPred.comp u f) U))) :
    CoreThm (Vy G (CPred.iff (CPred.comp (CPred.not u) f) (CPred.not U))) :=
  CoreThm.forallIffTransApply G _ _ _
    (CoreThm.forallNotReindexBeta G G f u)
    (vyNotCong hU)

theorem distLeaf {G : Ty} (f : CMap (G ×' Ty.final) G) (u : CPred G) :
    CoreThm (Vy G (CPred.iff (CPred.comp u f) (CPred.comp u f))) :=
  CoreThm.forallIffRefl G (CPred.comp u f)

-- ===== per-rule case lemmas (propositional layer of `Proves`) =====

section Rules

variable {G : Ty} (Δ : List (CPred (G ×' Ty.final)))

-- notation-free shorthand for "translated formula, closed": u ∘ fst G Final
private def cl {G : Ty} (u : CPred G) : CPred (G ×' Ty.final) :=
  CPred.comp u (CMap.fst G Ty.final)

theorem seqMp (x y : CPred G)
    (h1 : CoreThm (SeqLift G Δ (cl (CPred.imp x y))))
    (h2 : CoreThm (SeqLift G Δ (cl x))) :
    CoreThm (SeqLift G Δ (cl y)) :=
  chainMP Δ (chainIffMp Δ (distImp (distLeaf _ x) (distLeaf _ y)) h1) h2

theorem seqImpIntro (x y : CPred G)
    (h : CoreThm (SeqLift G (cl x :: Δ) (cl y))) :
    CoreThm (SeqLift G Δ (cl (CPred.imp x y))) :=
  chainIffMpr Δ (distImp (distLeaf _ x) (distLeaf _ y)) h

theorem seqK (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp x (CPred.imp y x)))) :=
  chainIffMpr Δ (distImp (distLeaf _ x) (distImp (distLeaf _ y) (distLeaf _ x)))
    (chainOfVy Δ (CoreThm.forallImpK G (cl x) (cl y)))

theorem seqS (x y z : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp
      (CPred.imp x (CPred.imp y z))
      (CPred.imp (CPred.imp x y) (CPred.imp x z))))) :=
  chainIffMpr Δ
    (distImp
      (distImp (distLeaf _ x) (distImp (distLeaf _ y) (distLeaf _ z)))
      (distImp (distImp (distLeaf _ x) (distLeaf _ y))
        (distImp (distLeaf _ x) (distLeaf _ z))))
    (chainOfVy Δ (CoreThm.forallImpS G (cl x) (cl y) (cl z)))

theorem seqCP (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp
      (CPred.imp (CPred.not y) (CPred.not x))
      (CPred.imp x y)))) :=
  chainIffMpr Δ
    (distImp
      (distImp (distNot (distLeaf _ y)) (distNot (distLeaf _ x)))
      (distImp (distLeaf _ x) (distLeaf _ y)))
    (chainOfVy Δ (CoreThm.forallContrapose G (cl x) (cl y)))

theorem seqAndL (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp (CPred.and x y) x))) :=
  chainIffMpr Δ (distImp (distAnd (distLeaf _ x) (distLeaf _ y)) (distLeaf _ x))
    (chainOfVy Δ (CoreThm.forallAndProjL G (cl x) (cl y)))

theorem seqAndR (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp (CPred.and x y) y))) :=
  chainIffMpr Δ (distImp (distAnd (distLeaf _ x) (distLeaf _ y)) (distLeaf _ y))
    (chainOfVy Δ (CoreThm.forallAndProjR G (cl x) (cl y)))

theorem seqAndI (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp x
      (CPred.imp y (CPred.and x y))))) :=
  chainIffMpr Δ
    (distImp (distLeaf _ x)
      (distImp (distLeaf _ y) (distAnd (distLeaf _ x) (distLeaf _ y))))
    (chainOfVy Δ (CoreThm.forallAndIntro G (cl x) (cl y)))

theorem seqOrL (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp x (CPred.or x y)))) :=
  chainIffMpr Δ (distImp (distLeaf _ x) (distOr (distLeaf _ x) (distLeaf _ y)))
    (chainOfVy Δ (CoreThm.forallOrInL G (cl x) (cl y)))

theorem seqOrR (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp y (CPred.or x y)))) :=
  chainIffMpr Δ (distImp (distLeaf _ y) (distOr (distLeaf _ x) (distLeaf _ y)))
    (chainOfVy Δ (CoreThm.forallOrInR G (cl x) (cl y)))

theorem seqOrE (x y z : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp (CPred.imp x z)
      (CPred.imp (CPred.imp y z)
        (CPred.imp (CPred.or x y) z))))) :=
  chainIffMpr Δ
    (distImp (distImp (distLeaf _ x) (distLeaf _ z))
      (distImp (distImp (distLeaf _ y) (distLeaf _ z))
        (distImp (distOr (distLeaf _ x) (distLeaf _ y)) (distLeaf _ z))))
    (chainOfVy Δ (CoreThm.forallOrElim G (cl x) (cl y) (cl z)))

theorem seqIffI (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp (CPred.imp x y)
      (CPred.imp (CPred.imp y x) (CPred.iff x y))))) :=
  chainIffMpr Δ
    (distImp (distImp (distLeaf _ x) (distLeaf _ y))
      (distImp (distImp (distLeaf _ y) (distLeaf _ x))
        (distIff (distLeaf _ x) (distLeaf _ y))))
    (chainOfVy Δ (CoreThm.forallIffIntro G (cl x) (cl y)))

theorem seqIffL (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp (CPred.iff x y) (CPred.imp x y)))) :=
  chainIffMpr Δ
    (distImp (distIff (distLeaf _ x) (distLeaf _ y))
      (distImp (distLeaf _ x) (distLeaf _ y)))
    (chainOfVy Δ (CoreThm.forallIffProjL G (cl x) (cl y)))

theorem seqIffR (x y : CPred G) :
    CoreThm (SeqLift G Δ (cl (CPred.imp (CPred.iff x y) (CPred.imp y x)))) :=
  chainIffMpr Δ
    (distImp (distIff (distLeaf _ x) (distLeaf _ y))
      (distImp (distLeaf _ y) (distLeaf _ x)))
    (chainOfVy Δ (CoreThm.forallIffProjR G (cl x) (cl y)))

end Rules

end ContextualHOL
