import ContextualHOL.Lifting
import ContextualHOL.Weakening

/-!
# The proof-lifting theorem (M3.3): `Proves` → `CoreThm`

Every derivation of the contextual calculus `Γ | Δ ⊢ φ` lifts to CoreThm
evidence for the single-closure sequent reading

  `SeqLift C[Γ] (Δ-lifts ∘ fst) (φ-lift ∘ fst)`.

The propositional layer is `Lifting.lean`'s chain machinery; the two
structurality generators are `substEquiv_sound` / `weakenEquiv_sound`; the
quantifier moves are the closure-form rules of `beta_basis.cor`
(`Forall_gen_closure`, `Exist_gen_closure`, `Forall_closure_fuse`,
`Forall_elim_closure`, `Exist_intro_closure`, `Forall_inst_closure`,
`Forall_weaken_closure`, plus the three map collapses).

`genChainAll` is the heart of the ∀/∃ context moves: it walks the assumption
chain once, applying `Forall_gen_closure` per assumption and
`Forall_closure_fuse` at the base — proof size grows with the chain, the
axiom set does not.
-/

namespace ContextualHOL

open CoreThm

-- ===== list plumbing =====

-- pointwise relation between two lists (Forall₂ is not in core Lean)
inductive ListRel {α : Type _} {β : Type _} (R : α -> β -> Prop) :
    List α -> List β -> Prop where
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b -> ListRel R as bs -> ListRel R (a :: as) (b :: bs)

def LiftsAll (env : Env) (Γ : Ctx) (Δ : List Formula)
    (cΔ : List (CPred (Ctx.obj Γ))) : Prop :=
  ListRel (fun psi c => liftFormula? env Γ psi = some c) Δ cΔ

theorem liftsAll_of_isSome (env : Env) (Γ : Ctx) :
    forall (Δ : List Formula),
      (forall psi, psi ∈ Δ -> (liftFormula? env Γ psi).isSome = true) ->
      exists cΔ, LiftsAll env Γ Δ cΔ := by
  intro Δ
  induction Δ with
  | nil => intro _; exact ⟨[], ListRel.nil⟩
  | cons psi rest ih =>
      intro h
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (h psi (List.Mem.head _))
      obtain ⟨cs, hcs⟩ := ih (fun q hq => h q (List.Mem.tail _ hq))
      exact ⟨c :: cs, ListRel.cons hc hcs⟩

theorem liftsAll_mem {env : Env} {Γ : Ctx} :
    forall {Δ : List Formula} {cΔ : List (CPred (Ctx.obj Γ))},
      LiftsAll env Γ Δ cΔ ->
      forall {phi : Formula} {c : CPred (Ctx.obj Γ)},
        phi ∈ Δ -> liftFormula? env Γ phi = some c -> c ∈ cΔ := by
  intro Δ cΔ h
  induction h with
  | nil => intro phi c hm; cases hm
  | cons ha _ ih =>
      intro phi c hm hc
      cases hm with
      | head =>
          rw [ha] at hc
          cases hc
          exact List.Mem.head _
      | tail _ hm' => exact List.Mem.tail _ (ih hm' hc)

theorem forall₂_map_right {α β γ : Type _} {R : α -> β -> Prop} (f : β -> γ) :
    forall {l : List α} {l' : List β}, ListRel R l l' ->
      ListRel (fun a c => exists b, R a b ∧ c = f b) l (l'.map f) := by
  intro l l' h
  induction h with
  | nil => exact ListRel.nil
  | cons ha _ ih => exact ListRel.cons ⟨_, ha, rfl⟩ ih

theorem forall₂_with_mem {α β : Type _} {R : α -> β -> Prop} {P : α -> Prop} :
    forall {l : List α} {l' : List β}, ListRel R l l' ->
      (forall a, a ∈ l -> P a) ->
      ListRel (fun a b => P a ∧ R a b) l l' := by
  intro l l' h
  induction h with
  | nil => intro _; exact ListRel.nil
  | cons ha _ ih =>
      intro hp
      exact ListRel.cons ⟨hp _ (List.Mem.head _), ha⟩
        (ih (fun a hb => hp a (List.Mem.tail _ hb)))

-- ===== some-composition builders for liftFormula? =====

theorem liftImp_some {env : Env} {Γ : Ctx} {a b : Formula}
    {ca cb : CPred (Ctx.obj Γ)}
    (ha : liftFormula? env Γ a = some ca) (hb : liftFormula? env Γ b = some cb) :
    liftFormula? env Γ (Formula.imp a b) = some (CPred.imp ca cb) := by
  rw [liftFormula?_imp, ha, hb]

theorem liftAnd_some {env : Env} {Γ : Ctx} {a b : Formula}
    {ca cb : CPred (Ctx.obj Γ)}
    (ha : liftFormula? env Γ a = some ca) (hb : liftFormula? env Γ b = some cb) :
    liftFormula? env Γ (Formula.and a b) = some (CPred.and ca cb) := by
  rw [liftFormula?_and, ha, hb]

theorem liftOr_some {env : Env} {Γ : Ctx} {a b : Formula}
    {ca cb : CPred (Ctx.obj Γ)}
    (ha : liftFormula? env Γ a = some ca) (hb : liftFormula? env Γ b = some cb) :
    liftFormula? env Γ (Formula.or a b) = some (CPred.or ca cb) := by
  rw [liftFormula?_or, ha, hb]

theorem liftIff_some {env : Env} {Γ : Ctx} {a b : Formula}
    {ca cb : CPred (Ctx.obj Γ)}
    (ha : liftFormula? env Γ a = some ca) (hb : liftFormula? env Γ b = some cb) :
    liftFormula? env Γ (Formula.iff a b) = some (CPred.iff ca cb) := by
  rw [liftFormula?_iff, ha, hb]

theorem liftNot_some {env : Env} {Γ : Ctx} {a : Formula}
    {ca : CPred (Ctx.obj Γ)}
    (ha : liftFormula? env Γ a = some ca) :
    liftFormula? env Γ (Formula.not a) = some (CPred.not ca) := by
  rw [liftFormula?_not, ha]
  rfl

theorem liftEx_some {env : Env} {Γ : Ctx} {x : Name} {X : Ty} {b : Formula}
    {cb : CPred (Ctx.obj ({ name := x, ty := X } :: Γ))}
    (hb : liftFormula? env ({ name := x, ty := X } :: Γ) b = some cb) :
    liftFormula? env Γ (Formula.ex x X b) = some (CPred.ex X cb) := by
  rw [liftFormula?_ex, hb]
  rfl

theorem liftAll_some {env : Env} {Γ : Ctx} {x : Name} {X : Ty} {b : Formula}
    {cb : CPred (Ctx.obj ({ name := x, ty := X } :: Γ))}
    (hb : liftFormula? env ({ name := x, ty := X } :: Γ) b = some cb) :
    liftFormula? env Γ (Formula.all x X b) = some (CPred.all X cb) := by
  rw [liftFormula?_all, hb]
  rfl

-- implication composition under the closure
theorem vyComp {G : Ty} {a b c : CPred (G ×' Ty.final)}
    (h1 : CoreThm (Vy G (CPred.imp a b)))
    (h2 : CoreThm (Vy G (CPred.imp b c))) :
    CoreThm (Vy G (CPred.imp a c)) :=
  vyMP (vyMP (CoreThm.forallImpS G a b c) (vyWeaken a h2)) h1

-- ===== chain transports =====

theorem chainIffCong {G : Ty} (Δ : List (CPred (G ×' Ty.final))) :
    forall {c c' : CPred (G ×' Ty.final)},
      CoreThm (Vy G (CPred.iff c c')) ->
      CoreThm (Vy G (CPred.iff (chainF G Δ c) (chainF G Δ c'))) := by
  induction Δ with
  | nil => intro c c' h; exact h
  | cons a Δ ih =>
      intro c c' h
      exact ih (vyImpCong (CoreThm.forallIffRefl G a) h)

-- congruence at every chain position, indexed by an abstract carrier list.
theorem chainCongVia {G : Ty} {α : Type _}
    {F F' : α -> CPred (G ×' Ty.final) -> Prop}
    (hIff : forall a e e', F a e -> F' a e' ->
      CoreThm (Vy G (CPred.iff e e'))) :
    forall {l : List α} {Δ Δ' : List (CPred (G ×' Ty.final))}
      {c c' : CPred (G ×' Ty.final)},
      ListRel F l Δ -> ListRel F' l Δ' ->
      CoreThm (Vy G (CPred.iff c c')) ->
      CoreThm (SeqLift G Δ c) -> CoreThm (SeqLift G Δ' c') := by
  intro l
  induction l with
  | nil =>
      intro Δ Δ' c c' h1 h2 hc h
      cases h1
      cases h2
      exact vyMP (vyIffMp hc) h
  | cons a as ih =>
      intro Δ Δ' c c' h1 h2 hc h
      cases h1 with
      | @cons _ b1 _ bs1 ha1 has1 =>
      cases h2 with
      | @cons _ b2 _ bs2 ha2 has2 =>
      exact ih (c := CPred.imp b1 c) (c' := CPred.imp b2 c') has1 has2
        (vyImpCong (hIff a _ _ ha1 ha2) hc) h

-- distribute a chain over composition with a point map.
theorem chainDist {G H : Ty} (ι : CMap (G ×' Ty.final) (H ×' Ty.final)) :
    forall (Δ : List (CPred (H ×' Ty.final))) (b : CPred (H ×' Ty.final)),
      CoreThm (Vy G (CPred.iff
        (CPred.comp (chainF H Δ b) ι)
        (chainF G (Δ.map (fun a => CPred.comp a ι)) (CPred.comp b ι)))) := by
  intro Δ
  induction Δ with
  | nil => intro b; exact CoreThm.forallIffRefl G (CPred.comp b ι)
  | cons a Δ ih =>
      intro b
      exact CoreThm.forallIffTransApply _ _ _ _
        (ih (CPred.imp a b))
        (chainIffCong (Δ.map (fun a => CPred.comp a ι))
          (CoreThm.forallImpReindexBeta G (H ×' Ty.final) ι a b))

-- ===== the ∀/∃ context move through the whole chain =====

theorem genChainAll {G X : Ty} :
    forall (Δg : List (CPred G)) (cb : CPred (X ×' G)),
      CoreThm (SeqLift (X ×' G)
        (Δg.map (fun a => CPred.comp a
          (CMap.comp (CMap.snd X G) (CMap.fst (X ×' G) Ty.final))))
        (CPred.comp cb (CMap.fst (X ×' G) Ty.final))) ->
      CoreThm (SeqLift G
        (Δg.map (fun a => CPred.comp a (CMap.fst G Ty.final)))
        (CPred.comp (CPred.all X cb) (CMap.fst G Ty.final))) := by
  intro Δg
  induction Δg with
  | nil =>
      intro cb h
      exact vyMP (vyIffMpr (CoreThm.forallClosureBeta X G cb))
        (CoreThm.forallClosureFuse X G cb h)
  | cons a Δg ih =>
      intro cb h
      have hbody : CoreThm (Vy (X ×' G) (CPred.iff
          (CPred.comp (CPred.imp (CPred.comp a (CMap.snd X G)) cb)
            (CMap.fst (X ×' G) Ty.final))
          (CPred.imp
            (CPred.comp a (CMap.comp (CMap.snd X G)
              (CMap.fst (X ×' G) Ty.final)))
            (CPred.comp cb (CMap.fst (X ×' G) Ty.final))))) :=
        distImp
          (CoreThm.forallUnaryReindexBeta (X ×' G) (X ×' G) G a
            (CMap.snd X G) (CMap.fst (X ×' G) Ty.final))
          (CoreThm.forallIffRefl _ _)
      have h' := chainIffMpr
        (Δg.map (fun a => CPred.comp a
          (CMap.comp (CMap.snd X G) (CMap.fst (X ×' G) Ty.final))))
        hbody h
      have h'' := ih (CPred.imp (CPred.comp a (CMap.snd X G)) cb) h'
      exact chainMono (Δg.map (fun a => CPred.comp a (CMap.fst G Ty.final)))
        (CoreThm.forallGenClosure X G a cb) h''

-- ===== per-generator helper facts =====

-- the weakening generator's per-formula transport
theorem weakenIff (env : Env) (x : Binding) (Γ : Ctx) (psi : Formula)
    {c0 : CPred (Ctx.obj Γ)} {c1 : CPred (Ctx.obj (x :: Γ))}
    (hfree : occursFree x.name psi = false)
    (h0 : liftFormula? env Γ psi = some c0)
    (h1 : liftFormula? env (x :: Γ) psi = some c1) :
    CoreThm (Vy (x.ty ×' Ctx.obj Γ) (CPred.iff
      (CPred.comp c0 (CMap.comp (CMap.snd x.ty (Ctx.obj Γ))
        (CMap.fst (x.ty ×' Ctx.obj Γ) Ty.final)))
      (CPred.comp c1 (CMap.fst (x.ty ×' Ctx.obj Γ) Ty.final)))) := by
  obtain ⟨P, htP, heP⟩ := liftFormula?_is env Γ psi c0 h0
  obtain ⟨P', htP', heP'⟩ := liftFormula?_is env (x :: Γ) psi c1 h1
  exact weakenEquiv_sound_closed x.ty (Ctx.obj Γ) P P' c0 c1
    (translate_weakenFormula env x psi [] Γ P P' (Or.inr hfree) htP htP')
    heP heP'

-- the shared element-iff for the weaken-transport of assumption chains
theorem weakenElemIff (env : Env) (x : Name) (X : Ty) (Γ : Ctx)
    (psi : Formula) (e e' : CPred ((X ×' Ctx.obj Γ) ×' Ty.final))
    (he : exists c1, (occursFree x psi = false ∧
      liftFormula? env ({ name := x, ty := X } :: Γ) psi = some c1) ∧
      e = cl c1)
    (he' : exists c0, liftFormula? env Γ psi = some c0 ∧
      e' = CPred.comp c0 (CMap.comp (CMap.snd X (Ctx.obj Γ))
        (CMap.fst (X ×' Ctx.obj Γ) Ty.final))) :
    CoreThm (Vy (X ×' Ctx.obj Γ) (CPred.iff e e')) := by
  obtain ⟨c1, ⟨hfr, hc1⟩, rfl⟩ := he
  obtain ⟨c0, hc0, rfl⟩ := he'
  exact CoreThm.forallIffSymApply _ _ _
    (weakenIff env { name := x, ty := X } Γ psi hfr hc0 hc1)

-- the substitution generator's per-formula transport
theorem substIffLift (env : Env) (x : Binding) (Γ : Ctx) (phi : Formula)
    (t : Term) (tc : Core.Term) (tcm : CMap (Ctx.obj Γ) x.ty)
    (htc : translateTerm? env Γ t = some tc)
    (htcm : TermEmbedIs (Ctx.obj Γ) tc x.ty tcm)
    (havoid : avoids x.name phi = true)
    (htavoid : forall w, t = Term.var w -> avoids w phi = true)
    {cP : CPred (Ctx.obj (x :: Γ))} {cQ : CPred (Ctx.obj Γ)}
    (hP : liftFormula? env (x :: Γ) phi = some cP)
    (hQ : liftFormula? env Γ (substFormula x.name t phi) = some cQ) :
    CoreThm (Vy (Ctx.obj Γ) (CPred.iff
      (CPred.comp cP (CMap.comp (substMap x.ty (Ctx.obj Γ) tcm)
        (CMap.fst (Ctx.obj Γ) Ty.final)))
      (CPred.comp cQ (CMap.fst (Ctx.obj Γ) Ty.final)))) := by
  obtain ⟨P, htP, heP⟩ := liftFormula?_is env (x :: Γ) phi cP hP
  obtain ⟨Q, htQ, heQ⟩ := liftFormula?_is env Γ (substFormula x.name t phi) cQ hQ
  exact substEquiv_sound_closed x.ty (Ctx.obj Γ) tc tcm htcm P Q cP cQ
    (translate_substFormula_closed env x t tc Γ phi P Q htc havoid htavoid
      htP htQ)
    heP heQ

-- embed the translation of a non-raw, well-typed witness term
theorem lookupVar_projMapIs :
    forall (Γ : Ctx) (y : Name) (n : Nat) (ty : Ty),
      lookupVar? y Γ = some (n, ty) ->
      exists m, ProjMapIs (Ctx.obj Γ) n ty m := by
  intro Γ
  induction Γ with
  | nil => intro y n ty h; simp [lookupVar?] at h
  | cons b rest ih =>
      intro y n ty h
      simp only [lookupVar?] at h
      by_cases hb : b.name = y
      · rw [if_pos hb] at h
        simp at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        subst h2
        exact ⟨CMap.fst b.ty (Ctx.obj rest), ProjMapIs.zero b.ty (Ctx.obj rest)⟩
      · rw [if_neg hb] at h
        cases hr : lookupVar? y rest with
        | none => rw [hr] at h; simp at h
        | some p =>
            obtain ⟨i, ty'⟩ := p
            rw [hr] at h
            simp at h
            obtain ⟨h1, h2⟩ := h
            subst h1
            subst h2
            obtain ⟨m, hm⟩ := ih y i ty' hr
            exact ⟨CMap.comp m (CMap.snd b.ty (Ctx.obj rest)),
              ProjMapIs.succ b.ty (Ctx.obj rest) ty' i m hm⟩

theorem translateTerm_embed (env : Env) (Γ : Ctx) (t : Term) (X : Ty)
    (ht : inferTerm? env Γ t = some X)
    (htraw : forall n ty, t ≠ Term.raw n ty) :
    exists tc tcm, translateTerm? env Γ t = some tc ∧
      TermEmbedIs (Ctx.obj Γ) tc X tcm := by
  cases t with
  | var y =>
      simp only [inferTerm?] at ht
      cases hl : lookupVar? y Γ with
      | none => rw [hl] at ht; simp at ht
      | some p =>
          obtain ⟨n, ty⟩ := p
          rw [hl] at ht
          simp at ht
          subst ht
          obtain ⟨m, hm⟩ := lookupVar_projMapIs Γ y n _ hl
          exact ⟨Core.Term.proj n, m, by simp [translateTerm?, hl],
            TermEmbedIs.proj n _ m hm⟩
  | const c =>
      simp only [inferTerm?] at ht
      exact ⟨Core.Term.weakening X (Ctx.obj Γ) c, CMap.weaken X (Ctx.obj Γ) c,
        by simp [translateTerm?, ht], TermEmbedIs.weaken X (Ctx.obj Γ) c⟩
  | raw n ty => exact absurd rfl (htraw n ty)

-- substituting a variable for itself is the identity
theorem substTerm_var_self (x : Name) :
    forall (u : Term), substTerm x (Term.var x) u = u := by
  intro u
  cases u with
  | var y =>
      simp only [substTerm]
      split
      next h => rw [h]
      next => rfl
  | const c => rfl
  | raw n ty => rfl

theorem substFormula_var_self (x : Name) :
    forall (phi : Formula), substFormula x (Term.var x) phi = phi := by
  intro phi
  induction phi with
  | atom rel l r => simp [substFormula, substTerm_var_self]
  | papp p a => simp [substFormula, substTerm_var_self]
  | and p q ihp ihq => simp [substFormula, ihp, ihq]
  | or p q ihp ihq => simp [substFormula, ihp, ihq]
  | imp p q ihp ihq => simp [substFormula, ihp, ihq]
  | iff p q ihp ihq => simp [substFormula, ihp, ihq]
  | not p ihp => simp [substFormula, ihp]
  | all n ty b ihb => simp [substFormula, ihb]
  | ex n ty b ihb => simp [substFormula, ihb]

-- the counit's closed body, as a Vy fact
theorem counitVy (env : Env) (x : Name) (X : Ty) (Γ : Ctx) (phi : Formula)
    (havoid : avoids x phi = true)
    {cbb : CPred (Ctx.obj ({ name := x, ty := X } ::
      { name := x, ty := X } :: Γ))}
    {cb : CPred (Ctx.obj ({ name := x, ty := X } :: Γ))}
    (hbb : liftFormula? env
      ({ name := x, ty := X } :: { name := x, ty := X } :: Γ) phi = some cbb)
    (hb : liftFormula? env ({ name := x, ty := X } :: Γ) phi = some cb) :
    CoreThm (Vy (Ctx.obj ({ name := x, ty := X } :: Γ)) (CPred.comp
      (CPred.imp (CPred.all X cbb) cb)
      (CMap.fst (Ctx.obj ({ name := x, ty := X } :: Γ)) Ty.final))) := by
  obtain ⟨P, htP, heP⟩ := liftFormula?_is _ _ _ _ hbb
  obtain ⟨Q, htQ, heQ⟩ := liftFormula?_is _ _ _ _ hb
  have ht : translateTerm? env ({ name := x, ty := X } :: Γ) (Term.var x) =
      some (Core.Term.proj 0) := by
    simp [translateTerm?, lookupVar?]
  have hQ' : translateFormula? env ({ name := x, ty := X } :: Γ)
      (substFormula x (Term.var x) phi) = some Q := by
    rw [substFormula_var_self]
    exact htQ
  have hSE := translate_substFormula_closed env { name := x, ty := X }
    (Term.var x) (Core.Term.proj 0) ({ name := x, ty := X } :: Γ) phi P Q
    ht havoid (fun w hw => by cases hw; exact havoid) htP hQ'
  have htcm : TermEmbedIs (Ctx.obj ({ name := x, ty := X } :: Γ))
      (Core.Term.proj 0) X (CMap.fst X (Ctx.obj Γ)) :=
    TermEmbedIs.proj 0 X _ (ProjMapIs.zero X (Ctx.obj Γ))
  have hsound := substEquiv_sound_closed X
    (Ctx.obj ({ name := x, ty := X } :: Γ)) (Core.Term.proj 0)
    (CMap.fst X (Ctx.obj Γ)) htcm P Q cbb cb hSE heP heQ
  have helim := CoreThm.forallElimClosure X
    (Ctx.obj ({ name := x, ty := X } :: Γ)) (CMap.fst X (Ctx.obj Γ)) cbb
  have hregroup := CoreThm.forallUnaryReindexBeta
    (Ctx.obj ({ name := x, ty := X } :: Γ))
    (Ctx.obj ({ name := x, ty := X } :: Γ))
    (X ×' Ctx.obj ({ name := x, ty := X } :: Γ)) cbb
    (substMap X (Ctx.obj ({ name := x, ty := X } :: Γ))
      (CMap.fst X (Ctx.obj Γ)))
    (CMap.fst (Ctx.obj ({ name := x, ty := X } :: Γ)) Ty.final)
  have himpl := vyComp helim
    (vyIffMp (CoreThm.forallIffTransApply _ _ _ _ hregroup hsound))
  exact vyMP
    (vyIffMpr (distImp (distLeaf _ (CPred.all X cbb)) (distLeaf _ cb)))
    himpl

-- ===== the main theorem =====

theorem proves_lift (env : Env) {Γ : Ctx} {Δ : List Formula} {phi : Formula}
    (h : Proves env Γ Δ phi) :
    forall (cΔ : List (CPred (Ctx.obj Γ))) (cphi : CPred (Ctx.obj Γ)),
      LiftsAll env Γ Δ cΔ ->
      liftFormula? env Γ phi = some cphi ->
      CoreThm (SeqLift (Ctx.obj Γ) (cΔ.map cl) (cl cphi)) := by
  induction h with
  | @hyp Γ Δ phi hmem =>
      intro cΔ cphi hΔ hcphi
      exact chainHyp _ (List.mem_map.mpr ⟨_, liftsAll_mem hΔ hmem hcphi, rfl⟩)
  | @impIntro Γ Δ phi psi hlift hprem ih =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hlift
      cases hcb : liftFormula? env Γ psi with
      | none => rw [liftFormula?_imp, hca, hcb] at hcphi; simp at hcphi
      | some cb =>
          rw [liftImp_some hca hcb] at hcphi
          cases hcphi
          exact seqImpIntro _ ca cb
            (ih (ca :: cΔ) cb (ListRel.cons hca hΔ) hcb)
  | @mp Γ Δ phi psi hcut hprem1 hprem2 ih1 ih2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hcut
      exact seqMp _ ca cphi (ih1 cΔ _ hΔ (liftImp_some hca hcphi))
        (ih2 cΔ ca hΔ hca)
  | @axK Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some hca (liftImp_some hcb hca)] at hcphi
      cases hcphi
      exact seqK _ ca cb
  | @axS Γ Δ phi psi chi h1 h2 h3 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp h3
      rw [liftImp_some (liftImp_some hca (liftImp_some hcb hcc))
        (liftImp_some (liftImp_some hca hcb) (liftImp_some hca hcc))] at hcphi
      cases hcphi
      exact seqS _ ca cb cc
  | @axCP Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some (liftImp_some (liftNot_some hcb) (liftNot_some hca))
        (liftImp_some hca hcb)] at hcphi
      cases hcphi
      exact seqCP _ ca cb
  | @axAndL Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some (liftAnd_some hca hcb) hca] at hcphi
      cases hcphi
      exact seqAndL _ ca cb
  | @axAndR Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some (liftAnd_some hca hcb) hcb] at hcphi
      cases hcphi
      exact seqAndR _ ca cb
  | @axAndI Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some hca (liftImp_some hcb (liftAnd_some hca hcb))] at hcphi
      cases hcphi
      exact seqAndI _ ca cb
  | @axOrL Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some hca (liftOr_some hca hcb)] at hcphi
      cases hcphi
      exact seqOrL _ ca cb
  | @axOrR Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some hcb (liftOr_some hca hcb)] at hcphi
      cases hcphi
      exact seqOrR _ ca cb
  | @axOrE Γ Δ phi psi chi h1 h2 h3 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp h3
      rw [liftImp_some (liftImp_some hca hcc)
        (liftImp_some (liftImp_some hcb hcc)
          (liftImp_some (liftOr_some hca hcb) hcc))] at hcphi
      cases hcphi
      exact seqOrE _ ca cb cc
  | @axIffI Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some (liftImp_some hca hcb)
        (liftImp_some (liftImp_some hcb hca) (liftIff_some hca hcb))] at hcphi
      cases hcphi
      exact seqIffI _ ca cb
  | @axIffL Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some (liftIff_some hca hcb) (liftImp_some hca hcb)] at hcphi
      cases hcphi
      exact seqIffL _ ca cb
  | @axIffR Γ Δ phi psi h1 h2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h2
      rw [liftImp_some (liftIff_some hca hcb) (liftImp_some hcb hca)] at hcphi
      cases hcphi
      exact seqIffR _ ca cb
  | @allIntro Γ Δ x X phi hfresh hΔxs hprem ih =>
      intro cΔ cphi hΔ hcphi
      cases hb : liftFormula? env ({ name := x, ty := X } :: Γ) phi with
      | none => rw [liftFormula?_all, hb] at hcphi; simp at hcphi
      | some cb =>
          rw [liftAll_some hb] at hcphi
          cases hcphi
          obtain ⟨cΔx, hΔx⟩ := liftsAll_of_isSome env _ Δ hΔxs
          have htrans := chainCongVia (weakenElemIff env x X Γ)
            (forall₂_map_right cl (forall₂_with_mem hΔx hfresh))
            (forall₂_map_right
              (fun c => CPred.comp c (CMap.comp (CMap.snd X (Ctx.obj Γ))
                (CMap.fst (X ×' Ctx.obj Γ) Ty.final))) hΔ)
            (CoreThm.forallIffRefl _ _)
            (ih cΔx cb hΔx hb)
          exact genChainAll cΔ cb htrans
  | @allCounit Γ Δ x X phi havoid =>
      intro cΔ cphi hΔ hcphi
      cases hbb : liftFormula? env
          ({ name := x, ty := X } :: { name := x, ty := X } :: Γ) phi with
      | none =>
          rw [liftFormula?_imp, liftFormula?_all, hbb] at hcphi
          simp at hcphi
      | some cbb =>
          cases hb : liftFormula? env ({ name := x, ty := X } :: Γ) phi with
          | none =>
              rw [liftFormula?_imp, liftAll_some hbb, hb] at hcphi
              simp at hcphi
          | some cb =>
              rw [liftImp_some (liftAll_some hbb) hb] at hcphi
              cases hcphi
              exact chainOfVy _ (counitVy env x X Γ phi havoid hbb hb)
  | @exElim Γ Δ x X phi psi hfresh hfreshψ hφxs hΔxs hψxs hprem1 hprem2
      ih1 ih2 =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨cφb, hφx⟩ := Option.isSome_iff_exists.mp hφxs
      obtain ⟨cψx, hψx⟩ := Option.isSome_iff_exists.mp hψxs
      obtain ⟨cΔx, hΔx⟩ := liftsAll_of_isSome env _ Δ hΔxs
      have ihres1 := ih1 cΔ (CPred.ex X cφb) hΔ (liftEx_some hφx)
      have ihres2 := ih2 (cφb :: cΔx) cψx (ListRel.cons hφx hΔx) hψx
      have hconc : CoreThm (Vy (X ×' Ctx.obj Γ) (CPred.iff
          (CPred.imp (cl cφb) (cl cψx))
          (CPred.comp
            (CPred.imp cφb (CPred.comp cphi (CMap.snd X (Ctx.obj Γ))))
            (CMap.fst (X ×' Ctx.obj Γ) Ty.final)))) := by
        have h1 := CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.forallIffSymApply _ _ _
            (weakenIff env { name := x, ty := X } Γ psi hfreshψ hcphi hψx))
          (CoreThm.forallIffSymApply _ _ _
            (CoreThm.forallUnaryReindexBeta (X ×' Ctx.obj Γ)
              (X ×' Ctx.obj Γ) (Ctx.obj Γ) cphi (CMap.snd X (Ctx.obj Γ))
              (CMap.fst (X ×' Ctx.obj Γ) Ty.final)))
        exact CoreThm.forallIffTransApply _ _ _ _
          (vyImpCong (CoreThm.forallIffRefl _ (cl cφb)) h1)
          (CoreThm.forallIffSymApply _ _ _
            (distImp (distLeaf _ cφb)
              (distLeaf _ (CPred.comp cphi (CMap.snd X (Ctx.obj Γ))))))
      have htrans := chainCongVia (weakenElemIff env x X Γ)
        (forall₂_map_right cl (forall₂_with_mem hΔx hfresh))
        (forall₂_map_right
          (fun c => CPred.comp c (CMap.comp (CMap.snd X (Ctx.obj Γ))
            (CMap.fst (X ×' Ctx.obj Γ) Ty.final))) hΔ)
        hconc ihres2
      have hgen := genChainAll cΔ
        (CPred.imp cφb (CPred.comp cphi (CMap.snd X (Ctx.obj Γ)))) htrans
      have hmono := chainMono (cΔ.map cl)
        (CoreThm.existGenClosure X (Ctx.obj Γ) cphi cφb) hgen
      exact chainMP _ hmono ihres1
  | @exIntro Γ Δ x X phi t ht htraw havoid htavoid hφxs hsubs hprem ih =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨cφb, hφx⟩ := Option.isSome_iff_exists.mp hφxs
      obtain ⟨cq, hq⟩ := Option.isSome_iff_exists.mp hsubs
      rw [liftEx_some hφx] at hcphi
      cases hcphi
      obtain ⟨tc, tcm, htc, htcm⟩ := translateTerm_embed env Γ t X ht htraw
      have hsub := substIffLift env { name := x, ty := X } Γ phi t tc tcm
        htc htcm havoid htavoid hφx hq
      have hregroup := CoreThm.forallUnaryReindexBeta (Ctx.obj Γ) (Ctx.obj Γ)
        (X ×' Ctx.obj Γ) cφb (substMap X (Ctx.obj Γ) tcm)
        (CMap.fst (Ctx.obj Γ) Ty.final)
      have himpl := vyComp
        (vyIffMp (CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.forallIffSymApply _ _ _ hsub)
          (CoreThm.forallIffSymApply _ _ _ hregroup)))
        (CoreThm.existIntroClosure X (Ctx.obj Γ) tcm cφb)
      exact chainMono _ himpl (ih cΔ cq hΔ hq)
  | @ctxWeaken Γ Δ x X phi hfree hfreshΔ hφ0s hΔ0s hprem ih =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨cφ0, hφ0⟩ := Option.isSome_iff_exists.mp hφ0s
      obtain ⟨cΔ0, hΔ0⟩ := liftsAll_of_isSome env _ Δ hΔ0s
      have ihres := ih cΔ0 cφ0 hΔ0 hφ0
      have hweak := CoreThm.forallWeakenClosure X (Ctx.obj Γ) _ ihres
      have h2 := vyMP
        (vyIffMp (chainDist
          (CMap.pair (CMap.comp (CMap.snd X (Ctx.obj Γ))
            (CMap.fst (X ×' Ctx.obj Γ) Ty.final))
            (CMap.snd (X ×' Ctx.obj Γ) Ty.final))
          (cΔ0.map cl) (cl cφ0)))
        hweak
      rw [List.map_map] at h2
      have helem : forall (psi : Formula)
          (e e' : CPred ((X ×' Ctx.obj Γ) ×' Ty.final)),
          (exists b, (liftFormula? env Γ psi = some b) ∧
            e = CPred.comp (cl b)
              (CMap.pair (CMap.comp (CMap.snd X (Ctx.obj Γ))
                (CMap.fst (X ×' Ctx.obj Γ) Ty.final))
                (CMap.snd (X ×' Ctx.obj Γ) Ty.final))) ->
          (exists c1, (occursFree x psi = false ∧
            liftFormula? env ({ name := x, ty := X } :: Γ) psi = some c1) ∧
            e' = cl c1) ->
          CoreThm (Vy (X ×' Ctx.obj Γ) (CPred.iff e e')) := by
        intro psi e e' he he'
        obtain ⟨b, hb, rfl⟩ := he
        obtain ⟨c1, ⟨hfr, hc1⟩, rfl⟩ := he'
        exact CoreThm.forallIffTransApply _ _ _ _
          (CoreThm.forallWeakenAsmCollapse X (Ctx.obj Γ) b)
          (weakenIff env { name := x, ty := X } Γ psi hfr hb hc1)
      have hbody := CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallWeakenAsmCollapse X (Ctx.obj Γ) cφ0)
        (weakenIff env { name := x, ty := X } Γ phi hfree hφ0 hcphi)
      exact chainCongVia helem
        (forall₂_map_right
          (fun b => CPred.comp (cl b)
            (CMap.pair (CMap.comp (CMap.snd X (Ctx.obj Γ))
              (CMap.fst (X ×' Ctx.obj Γ) Ty.final))
              (CMap.snd (X ×' Ctx.obj Γ) Ty.final))) hΔ0)
        (forall₂_map_right cl (forall₂_with_mem hΔ hfreshΔ))
        hbody h2
  | @ctxSubst Γ Δ x X phi t ht htraw havoid htavoid hfreshΔ hφxs hΔxs
      hprem ih =>
      intro cΔ cphi hΔ hcphi
      obtain ⟨cφx, hφx⟩ := Option.isSome_iff_exists.mp hφxs
      obtain ⟨cΔx, hΔx⟩ := liftsAll_of_isSome env _ Δ hΔxs
      have ihres := ih cΔx cφx hΔx hφx
      obtain ⟨tc, tcm, htc, htcm⟩ := translateTerm_embed env Γ t X ht htraw
      have hinst := CoreThm.forallInstClosure X (Ctx.obj Γ) tcm _ ihres
      have h2 := vyMP
        (vyIffMp (chainDist
          (CMap.pair (CMap.comp (CMap.pair tcm (CMap.id (Ctx.obj Γ)))
            (CMap.fst (Ctx.obj Γ) Ty.final))
            (CMap.snd (Ctx.obj Γ) Ty.final))
          (cΔx.map cl) (cl cφx)))
        hinst
      rw [List.map_map] at h2
      have helem : forall (psi : Formula)
          (e e' : CPred (Ctx.obj Γ ×' Ty.final)),
          (exists c1, (occursFree x psi = false ∧
            liftFormula? env ({ name := x, ty := X } :: Γ) psi = some c1) ∧
            e = CPred.comp (cl c1)
              (CMap.pair (CMap.comp (CMap.pair tcm (CMap.id (Ctx.obj Γ)))
                (CMap.fst (Ctx.obj Γ) Ty.final))
                (CMap.snd (Ctx.obj Γ) Ty.final))) ->
          (exists c0, liftFormula? env Γ psi = some c0 ∧ e' = cl c0) ->
          CoreThm (Vy (Ctx.obj Γ) (CPred.iff e e')) := by
        intro psi e e' he he'
        obtain ⟨c1, ⟨hfr, hc1⟩, rfl⟩ := he
        obtain ⟨c0, hc0, rfl⟩ := he'
        have hstep1 :=
          vyMP
            (vyIffMp (CoreThm.forallIffReindexBeta (Ctx.obj Γ)
              ((X ×' Ctx.obj Γ) ×' Ty.final) _ _ _))
            (CoreThm.forallInstClosure X (Ctx.obj Γ) tcm _
              (CoreThm.forallIffSymApply _ _ _
                (weakenIff env { name := x, ty := X } Γ psi hfr hc0 hc1)))
        exact CoreThm.forallIffTransApply _ _ _ _ hstep1
          (CoreThm.forallInstAsmCollapse X (Ctx.obj Γ) tcm c0)
      have hbody := CoreThm.forallIffTransApply _ _ _ _
        (CoreThm.forallInstBodyCollapse X (Ctx.obj Γ) tcm cφx)
        (substIffLift env { name := x, ty := X } Γ phi t tc tcm
          htc htcm havoid htavoid hφx hcphi)
      exact chainCongVia helem
        (forall₂_map_right
          (fun c1 => CPred.comp (cl c1)
            (CMap.pair (CMap.comp (CMap.pair tcm (CMap.id (Ctx.obj Γ)))
              (CMap.fst (Ctx.obj Γ) Ty.final))
              (CMap.snd (Ctx.obj Γ) Ty.final)))
          (forall₂_with_mem hΔx hfreshΔ))
        (forall₂_map_right cl hΔ)
        hbody h2

end ContextualHOL
