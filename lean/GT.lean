import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# A Mathlib-facing formalization of the referenceable results in `test/GT/GT.tex`

The stable TeX labels are recorded in comments.  Declaration names follow
Mathlib conventions and deliberately state the Mathlib formulation, which is
occasionally more general than the finite formulation in the text.

The computational tables, algorithms, exercises, solutions, examination, and
informal historical assertions are outside the present scope.  Constructions
already supplied by Mathlib are used directly instead of being duplicated.
-/

namespace GT

open scoped Pointwise

section BasicDefinitions

variable {G G' : Type*} [Group G] [Group G']

/-- GT `bd4`: a nonempty subset closed under multiplication and inversion is a subgroup. -/
def Subgroup.ofNonemptyMulInvClosed (S : Set G) (hne : S.Nonempty)
    (hmul : ∀ {a b : G}, a ∈ S → b ∈ S → a * b ∈ S)
    (hinv : ∀ {a : G}, a ∈ S → a⁻¹ ∈ S) : Subgroup G where
  carrier := S
  one_mem' := by
    obtain ⟨a, ha⟩ := hne
    simpa using hmul (hinv ha) ha
  mul_mem' := hmul
  inv_mem' := hinv

/-- GT `bd5`: membership in an arbitrary intersection of subgroups. -/
theorem Subgroup.mem_sInf_iff {S : Set (Subgroup G)} {x : G} :
    x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H := by
  simp

/-- GT `bd7`: the generated subgroup is the least subgroup containing the set. -/
theorem Subgroup.closure_le_iff {S : Set G} {H : Subgroup G} :
    Subgroup.closure S ≤ H ↔ S ⊆ H :=
  Subgroup.closure_le H

/-- GT `bd11` (Cayley) and finite corollary `bd12`: every group is
isomorphic to a subgroup of its permutation group. -/
noncomputable def Equiv.Perm.cayley (G : Type*) [Group G] :
    G ≃* (MulAction.toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

/-- GT `bd14`, part (c): equality of left cosets. -/
theorem Subgroup.leftCoset_eq_leftCoset_iff (H : Subgroup G) (a b : G) :
    a • (H : Set G) = b • H ↔ a⁻¹ * b ∈ H :=
  leftCoset_eq_iff H

/-- GT `bd14(d)`: every left coset is in bijection with the subgroup. -/
def Subgroup.leftCosetEquiv (H : Subgroup G) (a : G) : (a • H : Set G) ≃ H :=
  H.leftCosetEquivSubgroup a

/-- GT `bd15` (Lagrange), in `Nat.card` form. -/
theorem Subgroup.card_mul_index_eq (H : Subgroup G) :
    Nat.card H * H.index = Nat.card G :=
  H.card_mul_index

/-- GT `bd16`: the order of an element divides the order of its group. -/
theorem orderOf_dvd_group_card (x : G) : orderOf x ∣ Nat.card G :=
  orderOf_dvd_natCard x

/-- GT `bd19`: multiplicativity of subgroup indices in a tower. -/
theorem Subgroup.relIndex_mul_index_eq {K H : Subgroup G} (hKH : K ≤ H) :
    K.relIndex H * H.index = K.index :=
  Subgroup.relIndex_mul_index hKH

/-- GT `bd22`: normality is equivalent to equality of left and right cosets. -/
theorem Subgroup.normal_iff_leftCoset_eq_rightCoset (N : Subgroup G) :
    N.Normal ↔ ∀ g : G, g • (N : Set G) = MulOpposite.op g • N :=
  normal_iff_eq_cosets N

/-- GT `bd25`: if `N` is normal, the carrier of `H ⊔ N` is the pointwise product `HN`. -/
theorem Subgroup.coe_sup_eq_mul (H N : Subgroup G) [N.Normal] :
    (↑(H ⊔ N) : Set G) = H * N :=
  Subgroup.mul_normal H N

/-- GT `bd25l`, `bd25m`, and `fg07`: the normal closure is normal, contains the
set, and is contained in every normal subgroup containing that set. -/
theorem Subgroup.normalClosure_isLeast (S : Set G) :
    (Subgroup.normalClosure S).Normal ∧
      S ⊆ Subgroup.normalClosure S ∧
      ∀ (N : Subgroup G), N.Normal → S ⊆ N → Subgroup.normalClosure S ≤ N := by
  refine ⟨inferInstance, Subgroup.subset_normalClosure, ?_⟩
  intro N hN hSN
  letI : N.Normal := hN
  exact Subgroup.normalClosure_le_normal hSN

/-- GT `bd26`: kernels of group homomorphisms are normal. -/
theorem MonoidHom.ker_normal (f : G →* G') : f.ker.Normal := by
  infer_instance

/-- GT `bd27`: a normal subgroup is the kernel of its quotient map. -/
theorem QuotientGroup.ker_mk'_eq (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N :=
  QuotientGroup.ker_mk' N

/-- GT `bd27m`: the universal map out of a quotient group. -/
def QuotientGroup.liftOfLeKer (N : Subgroup G) [N.Normal] (f : G →* G')
    (h : N ≤ f.ker) : G ⧸ N →* G' :=
  QuotientGroup.lift N f fun _x hx => MonoidHom.mem_ker.mp (h hx)

/-- GT `it01`: the first isomorphism theorem. -/
noncomputable def QuotientGroup.quotientKerMulEquivRange (f : G →* G') :
    G ⧸ f.ker ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f

/-- GT `it02`: the second isomorphism theorem. -/
noncomputable def QuotientGroup.quotientInfMulEquivSupQuotient
    (H N : Subgroup G) [N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  QuotientGroup.quotientInfEquivProdNormalQuotient H N

/-- GT `it03` and `it04`: the subgroup correspondence for a quotient. -/
def QuotientGroup.subgroupOrderIso (N : Subgroup G) [N.Normal] :
    Subgroup (G ⧸ N) ≃o {H : Subgroup G // N ≤ H} :=
  QuotientGroup.comapMk'OrderIso N

end BasicDefinitions

section InternalDirectProducts

variable {G : Type*} [Group G]

/-- GT `it05` and `it06`: complementary normal subgroups give an internal
direct product.  The hypothesis `IsComplement'` is exactly unique existence
of a factorization `g = hk`; normality forces the two factors to commute. -/
noncomputable def Subgroup.prodMulEquivOfIsComplement'
    (H K : Subgroup G) (hH : H.Normal) (hK : K.Normal)
    (h : H.IsComplement' K) : H × K ≃* G := by
  let f : H × K →* G :=
    { toFun := fun x ↦ (x.1 : G) * (x.2 : G)
      map_one' := by simp
      map_mul' := by
        intro x y
        have hc : Commute (x.2 : G) (y.1 : G) :=
          Subgroup.commute_of_normal_of_disjoint K H hK hH h.disjoint.symm
            x.2 y.1 x.2.2 y.1.2
        simp only [Prod.fst_mul, Prod.snd_mul]
        change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        calc
          _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
            simp [mul_assoc]
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
            rw [hc.eq]
          _ = _ := by simp [mul_assoc] }
  exact MulEquiv.ofBijective f h

end InternalDirectProducts

section FinitelyGeneratedCommutativeGroups

open scoped DirectSum

/-- GT `it20` and `it21`: the structure theorem for finitely generated
commutative groups, in Mathlib's prime-power invariant-factor interface. -/
theorem CommGroup.exists_mulEquiv_free_prod_primePower
    (G : Type*) [CommGroup G] [Group.FG G] :
    ∃ (ι j : Type) (_ : Fintype ι) (_ : Fintype j) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty
        (G ≃* (j → Multiplicative ℤ) ×
          ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) :=
  CommGroup.equiv_free_prod_prod_multiplicative_zmod G

/-- GT `it20` and `it21`, finite specialization: a finite commutative group is
a finite product of nontrivial finite cyclic groups. -/
theorem CommGroup.exists_mulEquiv_prod_zmod
    (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧
        Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) :=
  CommGroup.equiv_prod_multiplicative_zmod_of_finite G

/-- GT `it22`, part (a): duality for a finite commutative group. Mathlib states the
root-of-unity hypothesis explicitly, so the result applies to any suitable
coefficient monoid rather than fixing the complex numbers. -/
theorem CommGroup.nonempty_mulEquiv_dual
    (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] :
    Nonempty (G ≃* (G →* Mˣ)) := by
  exact ⟨(CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.symm⟩

/-- GT `it22`, part (b): the evaluation map identifies a finite commutative group
with its double dual. -/
noncomputable def CommGroup.doubleDualMulEquiv
    (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] :
    G ≃* ((G →* Mˣ) →* Mˣ) :=
  (CommGroup.monoidHomMonoidHomEquiv G M).symm

end FinitelyGeneratedCommutativeGroups

section FreeAndPresentedGroups

variable {X G : Type*} [Group G]

/-- GT `fg03`: the universal homomorphism from a free group. -/
def FreeGroup.liftToGroup (f : X → G) : FreeGroup X →* G :=
  FreeGroup.lift f

/-- GT `fg03`: uniqueness in the universal property of the free group. -/
theorem FreeGroup.lift_unique' (f : X → G) (g : FreeGroup X →* G)
    (h : ∀ x, g (.of x) = f x) : g = FreeGroup.lift f := by
  ext x
  simpa using h x

/-- GT `fg05`: the canonical map from the free group on the underlying set of a
group is surjective. -/
theorem FreeGroup.lift_id_surjective :
    Function.Surjective (FreeGroup.lift (id : G → G)) := by
  intro g
  exact ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩

/-- GT `fg06` (Nielsen--Schreier): subgroups of free groups are free. -/
theorem Subgroup.isFreeGroup_of_isFreeGroup [IsFreeGroup G] (H : Subgroup G) :
    IsFreeGroup H := by
  infer_instance

/-- GT `fg09`: the universal homomorphism from a presented group. -/
def PresentedGroup.liftToGroup {rels : Set (FreeGroup X)} (f : X → G)
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) : PresentedGroup rels →* G :=
  PresentedGroup.toGroup h

/-- GT `fg09`: uniqueness in the universal property of a presented group. -/
theorem PresentedGroup.lift_unique' {rels : Set (FreeGroup X)} (f : X → G)
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels →* G)
    (hg : ∀ x, g (.of x) = f x) : g = PresentedGroup.toGroup h := by
  ext x
  simpa using hg x

end FreeAndPresentedGroups

section GroupActions

variable {G X : Type*} [Group G] [MulAction G X]
open MulAction

/-- GT `ga04`: stabilizers of points in the same orbit are conjugate. -/
theorem MulAction.stabilizer_smul_eq (g : G) (x : X) :
    stabilizer G (g • x) = (stabilizer G x).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g x

/-- GT `ga07`: a transitive orbit is the quotient by a point stabilizer. -/
noncomputable def MulAction.quotientStabilizerEquivOrbit (x : X) :
    G ⧸ stabilizer G x ≃ orbit G x :=
  MulAction.orbitEquivQuotientStabilizer G x |>.symm

/-- GT `ga08`: orbit cardinality is the index of the stabilizer. -/
theorem MulAction.orbit_card_eq_index (x : X) :
    Nat.card (orbit G x) = (stabilizer G x).index :=
  by simpa using (MulAction.index_stabilizer G x).symm

/-- GT `ga09` and `ga10`: the kernel of the coset action is the normal core. -/
theorem Subgroup.normalCore_eq_cosetAction_ker (H : Subgroup G) :
    H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker :=
  H.normalCore_eq_ker

/-- GT `ga11` / `e35`: an action decomposes its underlying set as the disjoint sum of
its orbits. Cardinality formulas follow by applying cardinality. -/
noncomputable def MulAction.sigmaOrbitsEquiv :
    X ≃ Σ ω : MulAction.orbitRel.Quotient G X,
      MulAction.orbitRel.Quotient.orbit ω :=
  MulAction.selfEquivSigmaOrbits' G X

/-- GT `ga39`: for a nontrivial transitive action, primitivity is equivalent
to maximality of a point stabilizer. -/
theorem MulAction.isCoatom_stabilizer_iff_isPreprimitive
    [MulAction.IsPretransitive G X] [Nontrivial X] (x : X) :
    IsCoatom (stabilizer G x) ↔ MulAction.IsPreprimitive G X :=
  MulAction.isCoatom_stabilizer_iff_preprimitive G x

/-- GT `ga37` / `e18`: the block condition is exactly that every translate
is either equal to the block or disjoint from it. -/
theorem MulAction.isBlock_iff_smul_eq_or_disjoint (B : Set X) :
    MulAction.IsBlock G B ↔
      ∀ g : G, g • B = B ∨ Disjoint (g • B) B :=
  _root_.MulAction.isBlock_iff_smul_eq_or_disjoint (B := B)

/-- GT `ga38`, inclusion part: the stabilizer of a point in a block is
contained in the setwise stabilizer of the block. -/
theorem MulAction.stabilizer_le_stabilizer_block
    {B : Set X} (hB : MulAction.IsBlock G B) {x : X} (hx : x ∈ B) :
    stabilizer G x ≤ stabilizer G B :=
  hB.stabilizer_le hx

end GroupActions

section Permutations

variable {X : Type*}

/-- GT `ga21`: a finite permutation is the product of its pairwise-disjoint
cycle factors. -/
theorem Equiv.Perm.noncommProd_cycleFactorsFinset [Fintype X] [DecidableEq X]
    (f : Equiv.Perm X) :
    f.cycleFactorsFinset.noncommProd id
      (Equiv.Perm.cycleFactorsFinset_mem_commute f) = f :=
  f.cycleFactorsFinset_noncommProd

/-- GT `ga22`: a permutation is a product of transpositions, and its sign is
the parity of the displayed factorization length. -/
theorem Equiv.Perm.exists_swapFactors_with_sign [Fintype X] [LinearOrder X]
    (f : Equiv.Perm X) :
    ∃ l : List (Equiv.Perm X), l.prod = f ∧
      (∀ g ∈ l, Equiv.Perm.IsSwap g) ∧
      Equiv.Perm.sign f = (-1) ^ l.length := by
  let l := (Equiv.Perm.swapFactors f).1
  refine ⟨l, (Equiv.Perm.swapFactors f).2.1,
    (Equiv.Perm.swapFactors f).2.2, ?_⟩
  rw [← (Equiv.Perm.swapFactors f).2.1]
  exact Equiv.Perm.sign_prod_list_swap (Equiv.Perm.swapFactors f).2.2

/-- GT `ga23`: the alternating group is generated by three-cycles. -/
theorem Equiv.Perm.closure_isThreeCycle_eq_alternating [Fintype X] [DecidableEq X] :
    Subgroup.closure {f : Equiv.Perm X | Equiv.Perm.IsThreeCycle f} = alternatingGroup X :=
  Equiv.Perm.closure_three_cycles_eq_alternating

/-- GT `ga25`: finite permutations are conjugate exactly when their cycle
types agree. -/
theorem Equiv.Perm.isConj_iff_cycleType_eq' [Fintype X] [DecidableEq X]
    {f g : Equiv.Perm X} : IsConj f g ↔ f.cycleType = g.cycleType :=
  Equiv.Perm.isConj_iff_cycleType_eq

end Permutations

section FiniteGroups

variable {G : Type*} [Group G]

/-- GT `ga12` / `e36`: conjugacy classes partition a finite group. -/
theorem Group.sum_card_conjClasses_eq_card [Finite G] :
    ∑ᶠ C : ConjClasses G, C.carrier.ncard = Nat.card G :=
  Group.sum_card_conj_classes_eq_card G

/-- GT `ga12` / `e37`: the class equation, separating the centre from the
noncentral conjugacy classes. -/
theorem Group.card_center_add_sum_noncenter_eq_card [Finite G] :
    Nat.card (Subgroup.center G) +
      ∑ᶠ C ∈ ConjClasses.noncenter G, Nat.card C.carrier = Nat.card G :=
  Group.nat_card_center_add_sum_card_noncenter_eq_card G

/-- GT `ga13` (Cauchy): a prime divisor of the group order occurs as an element order. -/
theorem exists_orderOf_eq_prime [Fintype G] {p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card p hdiv

/-- GT `ga14`: a nontrivial finite `p`-group has nontrivial centre. -/
theorem IsPGroup.center_nontrivial {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center G) :=
  hG.center_nontrivial

/-- GT `ga17`: a cyclic quotient by the centre forces commutativity. -/
theorem commutative_of_quotient_center_cyclic
    [hcyc : IsCyclic (G ⧸ Subgroup.center G)] : ∀ a b : G, a * b = b * a := by
  exact (isMulCommutative_of_isCyclic_quotient_center_self G).is_comm.comm

/-- GT `ga16`: a group of prime-square order is commutative. -/
theorem commutative_of_card_eq_prime_sq {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm

/-- GT `ga28`: alternating groups on at least five letters are simple. -/
theorem alternatingGroup_isSimple {n : ℕ} (h : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  exact alternatingGroup.isSimpleGroup (by simpa using h)

/-- GT `st1`: the fixed-point congruence for a finite `p`-group action. -/
theorem IsPGroup.card_modEq_card_fixedPoints {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (X : Type*) [MulAction G X] [Fintype X] :
    Nat.card X ≡ Nat.card (MulAction.fixedPoints G X) [MOD p] :=
  hG.card_modEq_card_fixedPoints X

/-- GT `st2`: Sylow I in its prime-power divisor form. -/
theorem Sylow.exists_subgroup_card_pow_of_dvd [Finite G] {p r : ℕ}
    (hp : p.Prime) (hdiv : p ^ r ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ r := by
  letI : Fact p.Prime := ⟨hp⟩
  exact Sylow.exists_subgroup_card_pow_prime p hdiv

/-- GT `st7`: all Sylow subgroups are conjugate. -/
theorem Sylow.exists_smul_eq [Fact p.Prime] [Finite (Sylow p G)]
    (P Q : Sylow p G) : ∃ g : G, g • P = Q :=
  MulAction.exists_smul_eq G P Q

/-- GT `st7(b)`: the number of Sylow subgroups is one modulo `p`. -/
theorem Sylow.card_modEq_one [Fact p.Prime] [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  card_sylow_modEq_one p G

/-- GT `st7(b)`: the number of Sylow subgroups divides the Sylow index. -/
theorem Sylow.card_dvd_index' [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index :=
  P.card_dvd_index

/-- GT `st7(c)`: every `p`-subgroup lies in a Sylow `p`-subgroup. -/
theorem IsPGroup.exists_le_sylow' {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH : IsPGroup p H) :
    ∃ P : Sylow p G, H ≤ P :=
  hH.exists_le_sylow

/-- GT `st9`: a Sylow subgroup is normal exactly when it is the unique Sylow
subgroup.  `Subsingleton` is the proposition-level form of uniqueness because
`Sylow p G` is already inhabited. -/
theorem Sylow.normal_iff_subsingleton [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : P.Normal ↔ Subsingleton (Sylow p G) := by
  constructor
  · intro h
    letI : Unique (Sylow p G) := Sylow.unique_of_normal P h
    infer_instance
  · intro h
    letI : Subsingleton (Sylow p G) := h
    exact Sylow.normal_of_subsingleton P

/-- GT `ns21` (Frattini's argument). -/
theorem Sylow.normalizer_sup_normal_eq_top {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] [Finite (Sylow p N)] (P : Sylow p N) :
    Subgroup.normalizer (P.map N.subtype) ⊔ N = ⊤ :=
  P.normalizer_sup_eq_top

/-- GT `it17` (Schur--Zassenhaus), right-complement form. -/
theorem Subgroup.exists_complement_of_coprime [Finite G] (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, Subgroup.IsComplement' H N :=
  N.exists_left_complement'_of_coprime hcop

end FiniteGroups

section SolvableAndNilpotentGroups

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

/-- GT `ns04`: a faithful proposition-level formalization of the
Feit--Thompson statement.  The text cites this theorem without proving it, and
Mathlib does not currently contain it, so no inhabitant is asserted here. -/
def feitThompsonStatement : Prop :=
  ∀ (H : Type) (_ : Group H) (_ : Finite H), Nat.card H % 2 = 1 → IsSolvable H

/-- GT `ns06(a)`: subgroups of solvable groups are solvable. -/
theorem Subgroup.isSolvable [IsSolvable G] (H : Subgroup G) :
    IsSolvable H := by
  infer_instance

/-- GT `ns06(a)`: quotients of solvable groups are solvable. -/
theorem QuotientGroup.isSolvable [IsSolvable G]
    (N : Subgroup G) [N.Normal] : IsSolvable (G ⧸ N) := by
  infer_instance

/-- GT `ns06(b)`: the homomorphism form of closure of solvable groups under
extensions. -/
theorem Group.isSolvable_of_ker_le_range (f : G' →* G) (g : G →* G'')
    (h : g.ker ≤ f.range) [IsSolvable G'] [IsSolvable G''] :
    IsSolvable G :=
  solvable_of_ker_le_range f g h

/-- GT `ns07`: finite `p`-groups are solvable. -/
theorem IsPGroup.isSolvable {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) [Finite G] : IsSolvable G := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  infer_instance

/-- GT `ns09`: the commutator subgroup is characteristic. -/
theorem Subgroup.commutator_characteristic :
    (commutator G).Characteristic := by
  infer_instance

/-- GT `ns09`: the commutator subgroup is the least normal subgroup with
commutative quotient. -/
theorem Subgroup.commutator_le_iff_quotient_commutative
    (N : Subgroup G) [N.Normal] :
    commutator G ≤ N ↔ IsMulCommutative (G ⧸ N) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.symm

/-- GT `ns10`: derived-series characterization of solvability. -/
theorem Group.isSolvable_iff_derivedSeries_eq_bot :
    IsSolvable G ↔ ∃ n : ℕ, derivedSeries G n = ⊥ :=
  isSolvable_def G

/-- GT `ns12(a)`: subgroups of nilpotent groups are nilpotent. -/
theorem Subgroup.isNilpotent [Group.IsNilpotent G] (H : Subgroup G) :
    Group.IsNilpotent H := by
  infer_instance

/-- GT `ns12(b)`: quotients of nilpotent groups are nilpotent. -/
theorem QuotientGroup.isNilpotent [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] : Group.IsNilpotent (G ⧸ N) := by
  infer_instance

/-- GT `ns16`: finite `p`-groups are nilpotent. -/
theorem IsPGroup.isNilpotent' {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) [Finite G] : Group.IsNilpotent G :=
  hG.isNilpotent

/-- GT `ns17`, `ns19`, and `ns22`: Mathlib's five-way finite nilpotency
criterion simultaneously packages the normalizer condition, normality of
maximal subgroups and Sylow subgroups, and direct-product decomposition. -/
theorem Group.finite_isNilpotent_tfae [Finite G] :
    List.TFAE
      [Group.IsNilpotent G, NormalizerCondition G,
        ∀ H : Subgroup G, IsCoatom H → H.Normal,
        ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G),
          (↑P : Subgroup G).Normal,
        Nonempty
          ((∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G,
              (↑P : Subgroup G)) ≃* G)] :=
  Group.isNilpotent_of_finite_tfae

end SolvableAndNilpotentGroups

section RepresentationTheory

variable (k G : Type*) [Field k] [Group G] [Finite G]

/-- GT `r3` (Maschke): the group algebra is semisimple when its characteristic
does not divide the group order.  This is Mathlib's reusable algebraic form. -/
theorem groupAlgebra_isSemisimple
    [NeZero (Nat.card G : k)] : IsSemisimpleRing (MonoidAlgebra k G) := by
  infer_instance

/-- GT `r3` (Maschke), in the paper's invariant-complement form. -/
theorem representationSubmodule_exists_isCompl
    [NeZero (Nat.card G : k)] {V : Type*} [AddCommGroup V]
    [Module (MonoidAlgebra k G) V]
    (W : Submodule (MonoidAlgebra k G) V) :
    ∃ W' : Submodule (MonoidAlgebra k G) V, IsCompl W W' :=
  MonoidAlgebra.Submodule.exists_isCompl W

end RepresentationTheory

section SemisimpleModules

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- GT `r9`: a module is semisimple exactly when it is generated by its
simple submodules; complementedness is the definition carried by the
`IsSemisimpleModule` class. -/
theorem sSup_simpleSubmodules_eq_top_iff_isSemisimpleModule :
    sSup {N : Submodule R M | IsSimpleModule R N} = ⊤ ↔
      IsSemisimpleModule R M :=
  sSup_simples_eq_top_iff_isSemisimpleModule

/-- GT `r7`, `r8`, and `r9`: a semisimple module is an internal direct sum
of simple submodules. -/
theorem IsSemisimpleModule.exists_linearEquiv_dfinsupp'
    [IsSemisimpleModule R M] :
    ∃ (S : Set (Submodule R M))
      (_ : M ≃ₗ[R] Π₀ N : S, N.1),
      sSupIndep S ∧ ∀ N : S, IsSimpleModule R N.1 :=
  IsSemisimpleModule.exists_linearEquiv_dfinsupp R M

/-- GT `r10`: Jordan--Hölder uniqueness for module composition series,
expressed by Mathlib's equivalence of series. -/
theorem Submodule.compositionSeries_equivalent
    (s t : CompositionSeries (Submodule R M))
    (hhead : s.head = t.head) (hlast : s.last = t.last) :
    CompositionSeries.Equivalent s t :=
  CompositionSeries.jordan_holder s t hhead hlast

/-- GT `r9d`: fully invariant submodules of a semisimple module are precisely
sums of isotypic components. -/
theorem Submodule.isFullyInvariant_iff_sSup_isotypicComponents
    [IsSemisimpleModule R M] {N : Submodule R M} :
    N.IsFullyInvariant ↔
      ∃ S ⊆ isotypicComponents R M, N = sSup S :=
  _root_.isFullyInvariant_iff_sSup_isotypicComponents

/-- GT `r9c`: submodules of semisimple modules are semisimple. -/
theorem Submodule.isSemisimpleModule [IsSemisimpleModule R M]
    (N : Submodule R M) : IsSemisimpleModule R N := by
  infer_instance

/-- GT `r9c`: quotient modules of semisimple modules are semisimple. -/
theorem Submodule.quotient_isSemisimpleModule [IsSemisimpleModule R M]
    (N : Submodule R M) : IsSemisimpleModule R (M ⧸ N) := by
  infer_instance

end SemisimpleModules

section SimpleModules

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- GT `r16` (Schur): a homomorphism between simple modules is either an
isomorphism at the level of functions or zero. -/
theorem LinearMap.bijective_or_eq_zero_of_simple
    [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Bijective f ∨ f = 0 :=
  f.bijective_or_eq_zero

/-- GT `r19`: the finite-set form of the Jacobson density theorem. -/
theorem jacobsonDensity [IsSemisimpleModule R M]
    (f : Module.End (Module.End R M) M) (S : Finset M) :
    ∃ r : R, ∀ m ∈ S, f m = r • m :=
  jacobson_density f S

end SimpleModules

section WedderburnArtin

universe u

variable (F A : Type u) [CommRing F] [Ring A] [Algebra F A]

/-- GT `r21` and `r21a`: for a simple ring, semisimplicity, the Artinian
condition, and existence of a minimal left ideal are equivalent. -/
theorem simpleRing_semisimple_artinian_atom_tfae [IsSimpleRing A] :
    List.TFAE
      [IsSemisimpleRing A, IsArtinianRing A,
        ∃ I : Ideal A, IsAtom I] :=
  IsSimpleRing.tfae (R := A)

/-- GT `r15`: an Artinian simple algebra is a matrix algebra over a division
algebra. -/
theorem simpleAlgebra_exists_algEquiv_matrix_divisionRing
    [IsSimpleRing A] [IsArtinianRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D)
      (_ : Algebra F D),
      Nonempty (A ≃ₐ[F] Matrix (Fin n) (Fin n) D) :=
  IsSimpleRing.exists_algEquiv_matrix_divisionRing F A

/-- GT `r28a`: a semisimple algebra is a finite product of matrix algebras
over division algebras. -/
theorem semisimpleAlgebra_exists_algEquiv_pi_matrix_divisionRing
    [IsSemisimpleRing A] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ)
      (_ : ∀ i, DivisionRing (D i)) (_ : ∀ i, Algebra F (D i)),
      (∀ i, NeZero (d i)) ∧
        Nonempty (A ≃ₐ[F] ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing F A

end WedderburnArtin

section AlgebraicallyClosedWedderburnArtin

universe u

variable (F A : Type u) [Field F] [IsAlgClosed F] [Ring A] [Algebra F A]

/-- GT `r26` and `r31m`: over an algebraically closed field, the division
algebras in Wedderburn--Artin collapse to the base field. -/
theorem semisimpleAlgebra_exists_algEquiv_pi_matrix_of_isAlgClosed
    [IsSemisimpleRing A] [FiniteDimensional F A] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[F] ∀ i, Matrix (Fin (d i)) (Fin (d i)) F) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed F A

end AlgebraicallyClosedWedderburnArtin

section Characters

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]
  [Fintype G] [Invertible (Fintype.card G : k)]

/-- GT `r37`: the average character is the dimension of the invariant
subspace. -/
theorem FDRep.average_character_eq_finrank_invariants (V : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g =
      Module.finrank k (Representation.invariants V.ρ) :=
  FDRep.average_char_eq_finrank_invariants V

/-- GT `r38`: the character scalar product computes the dimension of the
space of equivariant maps. -/
theorem FDRep.character_scalarProduct_eq_finrank_hom (V W : FDRep k G) :
    ⅟(Fintype.card G : k) •
      ∑ g : G, W.character g * V.character g⁻¹ =
        Module.finrank k (V ⟶ W) :=
  FDRep.scalar_product_char_eq_finrank_equivariant V W

open scoped Classical in
/-- GT `r39`: characters of simple representations are orthonormal. -/
theorem FDRep.simple_character_orthonormal [IsAlgClosed k]
    (V W : FDRep k G) [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    ⅟(Fintype.card G : k) •
      ∑ g : G, V.character g * W.character g⁻¹ =
        if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  classical
  exact FDRep.char_orthonormal V W

end Characters

/-!
## Explicit omission ledger

The following stable labels are intentionally not separate declarations.  This
ledger makes those decisions machine-auditable without pretending that an
unproved proposition has been established.

* `e6` is the displayed equation inside `it21`; it is represented by
  `CommGroup.exists_mulEquiv_free_prod_primePower`.  Likewise `e34` is the
  displayed orbit--stabilizer equation represented by
  `MulAction.orbit_card_eq_index`.
* `ns06` and `ns12` are split into their subgroup, quotient, and extension
  declarations above.  The subpart suffixes are prose structure, not separate
  stable declarations.
* `ga30` and `ga31` are proof-local lemmas used in the book's proof of `ga28`;
  the target uses Mathlib's completed simplicity theorem directly.  The
  auxiliary averaging lemmas `r4`, `r5`, and `r6` are treated the same way for
  Maschke's theorem, as is the projector lemma `r36a` for `r37`.
* `fg01` and `fg02` concern the book's particular word-reduction
  implementation.  The canonical target deliberately uses Mathlib's quotient
  construction of `FreeGroup`; duplicating the private presentation would not
  expose additional mathematical structure.
* The exact Coxeter reflection-order results `fg16`, `fg17`, and `fg18` do not
  currently have a matching proved Mathlib interface.  Mathlib supplies the
  Coxeter presentation and the power relations, but not the exact-order and
  faithfulness conclusion required by the text.
* The isolated existence theorem `bd3m`, generator-replacement lemma `it19`,
  cyclicity criterion `it20a`, abelian character sums `it24` and `it25`, and
  finite-family direct-product criterion `it07` were not duplicated: their
  available library interfaces do not match the statements without substantial
  new development.
* The classification and subgroup refinements `ga13c`, `ga13m`, `ga15`,
  `ga32`, `st8`, `st10`, and `st11t` are beyond the direct wrapper layer used
  in this first experiment.  The block-stabilizer strictness clause `ga38` is
  represented only by its reusable inclusion theorem above.
* The semidirect-product comparison results `it15`, `st14`, `st15`, `st16`,
  and the complete-group splitting result `it18` require a paper-specific
  encoding of extensions that was intentionally not introduced.
* The group-theoretic Jordan--Hölder and operator-group results `ns02`, `ns14`,
  `ns15`, `ns18`, `ns24`, `ns25`, `ns26`, and `ns29` have no direct matching
  Mathlib declarations at this import frontier.  The module Jordan--Hölder
  result is formalized separately as `r10`.
* The remaining representation results `r10c`, `r17`, `r20`, `r22`, `r23`,
  `r28`, `r29`, `r30`, `r32`, `r33`, `r34`, `r34a`, `r35`, `r36`, `r41`, and
  `r9e` require interfaces for finite semisimple decompositions, regular
  characters, or centralizers that are not exposed as statement-compatible
  theorems by the imported Mathlib modules.  Their stronger structural
  backbone—semisimplicity, Schur, density, Wedderburn--Artin, and character
  orthogonality—is checked above.
-/

end GT
