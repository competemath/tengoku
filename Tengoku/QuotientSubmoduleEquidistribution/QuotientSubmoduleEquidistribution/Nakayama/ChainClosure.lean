import Tengoku.Seed.Order.Interval.Finset.Fin
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.Relabeling
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Nakayama.Combinatorics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The canonical product-of-chains closure

This file constructs, rather than assumes, the closure system whose closed
sets are independent initial segments in finitely many chains.
-/

namespace QuotientSubmoduleEquidistribution.NakayamaCombinatorics

open Set

universe u

/-- Downward closure inside each fixed-index chain.-/
def chainClosure {ι : Type u} (c : ι → ℕ) :
    QuotientSubmoduleEquidistribution.SetClosure (ChainPoint c) where
  toFun S :=
    {p | ∃ j : Fin (c p.1),
      (⟨p.1, j⟩ : ChainPoint c) ∈ S ∧ p.2 ≤ j}
  monotone' S T h p hp := by
    obtain ⟨j, hjS, hpj⟩ := hp
    exact ⟨j, h hjS, hpj⟩
  le_closure' S p hp := ⟨p.2, hp, le_rfl⟩
  idempotent' S := by
    ext p
    constructor
    · rintro ⟨j, ⟨k, hkS, hjk⟩, hpj⟩
      exact ⟨k, hkS, hpj.trans hjk⟩
    · intro hp
      refine ⟨p.2, ?_, le_rfl⟩
      simpa using hp

/--
@isnad1 id=iff.0h4v.s7.13f1b542700d from=translated src=- shape=9c980593 vocab=59ba1877
-/
@[simp]
theorem mem_chainClosure {ι : Type u} {c : ι → ℕ}
    {S : Set (ChainPoint c)} {p : ChainPoint c} :
    p ∈ chainClosure c S ↔
      ∃ j : Fin (c p.1),
        (⟨p.1, j⟩ : ChainPoint c) ∈ S ∧ p.2 ≤ j :=
  Iff.rfl

/-- Initial segments are closed under the canonical chain closure.
@isnad1 id=isclosed.0h3v.s5.d44048ac38c2 from=translated src=- shape=ea35aa9c vocab=254e6b03
-/
theorem isClosed_initialSegment {ι : Type u} {c : ι → ℕ}
    (x : CapacityVector c) :
    (chainClosure c).IsClosed (initialSegment x) := by
  rw [ClosureOperator.isClosed_iff]
  ext p
  constructor
  · rintro ⟨j, hj, hpj⟩
    change (j : ℕ) < (x p.1 : ℕ) at hj
    have hpj' : (p.2 : ℕ) ≤ (j : ℕ) := by
      exact_mod_cast hpj
    exact hpj'.trans_lt hj
  · intro hp
    exact ⟨p.2, hp, le_rfl⟩

/-- Membership in a closed chain set is downward closed within each
fiber.
@isnad1 id=mem.3h6v.s7.018961952179 from=translated src=- shape=394128c1 vocab=e4d1634f
-/
theorem mem_of_le_of_mem_isClosed
    {ι : Type u} {c : ι → ℕ}
    {S : Set (ChainPoint c)}
    (hS : (chainClosure c).IsClosed S)
    {i : ι} {j k : Fin (c i)}
    (hjk : j ≤ k) (hk : (⟨i, k⟩ : ChainPoint c) ∈ S) :
    (⟨i, j⟩ : ChainPoint c) ∈ S := by
  rw [ClosureOperator.isClosed_iff] at hS
  rw [← hS]
  exact ⟨k, hk, hjk⟩

/-- The finite set cut out by one fiber of a chain subset.-/
noncomputable def fiberFinset
    {ι : Type u} {c : ι → ℕ}
    (S : Set (ChainPoint c)) (i : ι) : Finset (Fin (c i)) := by
  classical
  exact Finset.univ.filter fun j ↦
    (⟨i, j⟩ : ChainPoint c) ∈ S

/--
@isnad1 id=iff.0h5v.s6.3c0aea3a26d0 from=translated src=- shape=2720f4c4 vocab=6ac8fc79
-/
@[simp]
theorem mem_fiberFinset
    {ι : Type u} {c : ι → ℕ}
    (S : Set (ChainPoint c)) (i : ι) (j : Fin (c i)) :
    j ∈ fiberFinset S i ↔
      (⟨i, j⟩ : ChainPoint c) ∈ S := by
  classical
  simp [fiberFinset]

/-- The cardinality of a fiber is a valid coordinate between zero and
its capacity.-/
noncomputable def fiberLength
    {ι : Type u} {c : ι → ℕ}
    (S : Set (ChainPoint c)) (i : ι) : Fin (c i + 1) := by
  classical
  refine ⟨(fiberFinset S i).card, ?_⟩
  have hle :
      (fiberFinset S i).card ≤
        (Finset.univ : Finset (Fin (c i))).card :=
    Finset.card_le_card (Finset.subset_univ _)
  simpa using Nat.lt_succ_of_le hle

/-- A closed fiber contains exactly the points below its fiber
cardinality.
@isnad1 id=iff.1h5v.s6.631ee554a66b from=translated src=- shape=90e70414 vocab=86d780dd
-/
theorem mem_isClosed_iff_lt_fiberLength
    {ι : Type u} {c : ι → ℕ}
    {S : Set (ChainPoint c)}
    (hS : (chainClosure c).IsClosed S)
    (i : ι) (j : Fin (c i)) :
    (⟨i, j⟩ : ChainPoint c) ∈ S ↔
      (j : ℕ) < (fiberLength S i : ℕ) := by
  classical
  constructor
  · intro hjS
    have hsub :
        Finset.Iic j ⊆ fiberFinset S i := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      rw [mem_fiberFinset]
      exact mem_of_le_of_mem_isClosed hS hk hjS
    have hcard :=
      Finset.card_le_card hsub
    simpa [fiberLength] using hcard
  · intro hjcard
    by_contra hjS
    have hsub :
        fiberFinset S i ⊆ Finset.Iio j := by
      intro k hk
      rw [Finset.mem_Iio]
      by_contra hnot
      have hjk : j ≤ k := le_of_not_gt hnot
      exact hjS (mem_of_le_of_mem_isClosed hS hjk
        ((mem_fiberFinset S i k).mp hk))
    have hcard := Finset.card_le_card hsub
    have hcard' :
        (fiberFinset S i).card ≤ (j : ℕ) := by
      simpa using hcard
    change (j : ℕ) < (fiberFinset S i).card at hjcard
    omega

/-- Send a capacity vector to its union of initial segments, regarded as
a closed set.-/
def capacityToClosed
    {ι : Type u} {c : ι → ℕ}
    (x : CapacityVector c) : (chainClosure c).Closeds :=
  ⟨initialSegment x, isClosed_initialSegment x⟩

/-- Read the coordinate of a closed chain set from the cardinality of
its fiber.-/
noncomputable def closedToCapacity
    {ι : Type u} {c : ι → ℕ}
    (S : (chainClosure c).Closeds) : CapacityVector c :=
  fun i ↦ fiberLength S i

/-- Different capacity vectors determine different unions of initial
segments.
@isnad1 id=injectiv.0h2v.s5.25338c91ea17 from=translated src=- shape=884ebdb3 vocab=0e404e95
-/
theorem capacityToClosed_injective
    {ι : Type u} {c : ι → ℕ} :
    Function.Injective
      (capacityToClosed :
        CapacityVector c → (chainClosure c).Closeds) := by
  intro x y hxy
  have hsets : initialSegment x = initialSegment y :=
    congrArg Subtype.val hxy
  funext i
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let j : Fin (c i) :=
      ⟨(x i : ℕ), by
        have hy := (y i).isLt
        omega⟩
    have hm :=
      Set.ext_iff.mp hsets (⟨i, j⟩ : ChainPoint c)
    change
      ((j : ℕ) < (x i : ℕ)) ↔
        ((j : ℕ) < (y i : ℕ)) at hm
    exact (not_lt_of_ge le_rfl) (hm.mpr hlt)
  · let j : Fin (c i) :=
      ⟨(y i : ℕ), by
        have hx := (x i).isLt
        omega⟩
    have hm :=
      Set.ext_iff.mp hsets (⟨i, j⟩ : ChainPoint c)
    change
      ((j : ℕ) < (x i : ℕ)) ↔
        ((j : ℕ) < (y i : ℕ)) at hm
    exact (not_lt_of_ge le_rfl) (hm.mp hgt)

/-- Recovering fibers from a closed set returns that closed set.
@isnad1 id=eq.0h3v.s6.85f42c31447c from=translated src=- shape=a43c79d7 vocab=9a55a01c
-/
theorem capacityToClosed_closedToCapacity
    {ι : Type u} {c : ι → ℕ}
    (S : (chainClosure c).Closeds) :
    capacityToClosed (closedToCapacity S) = S := by
  apply Subtype.ext
  ext p
  change
    ((p.2 : ℕ) <
      (fiberLength (S : Set (ChainPoint c)) p.1 : ℕ)) ↔
      p ∈ (S : Set (ChainPoint c))
  exact
    (mem_isClosed_iff_lt_fiberLength
      S.property p.1 p.2).symm

/-- Recovering coordinates from initial segments returns the original
capacity vector.
@isnad1 id=eq.0h3v.s4.e93c3205a536 from=translated src=- shape=c5d72623 vocab=3e1b98f1
-/
theorem closedToCapacity_capacityToClosed
    {ι : Type u} {c : ι → ℕ}
    (x : CapacityVector c) :
    closedToCapacity (capacityToClosed x) = x := by
  apply capacityToClosed_injective
  rw [capacityToClosed_closedToCapacity]

/-- Closed sets of the canonical chain closure are equivalent to the
product of their chain capacities.-/
noncomputable def capacityClosedEquiv
    {ι : Type u} {c : ι → ℕ} :
    CapacityVector c ≃ (chainClosure c).Closeds where
  toFun := capacityToClosed
  invFun := closedToCapacity
  left_inv := closedToCapacity_capacityToClosed
  right_inv := capacityToClosed_closedToCapacity

/-- Initial-segment inclusion reflects the coordinatewise order.
@isnad1 id=iff.0h4v.s7.23bed1ad74c4 from=translated src=- shape=f17fbbea vocab=0b45e062
-/
theorem capacityToClosed_le_iff
    {ι : Type u} {c : ι → ℕ}
    (x y : CapacityVector c) :
    capacityToClosed x ≤ capacityToClosed y ↔ x ≤ y := by
  constructor
  · intro h i
    apply Fin.mk_le_mk.mpr
    by_contra hnot
    have hyx : (y i : ℕ) < (x i : ℕ) := by omega
    let j : Fin (c i) :=
      ⟨(y i : ℕ), by
        have hx := (x i).isLt
        omega⟩
    have hjx :
        (⟨i, j⟩ : ChainPoint c) ∈
          ((capacityToClosed x :
            (chainClosure c).Closeds) :
            Set (ChainPoint c)) := by
      exact hyx
    have hjy := h hjx
    change (j : ℕ) < (y i : ℕ) at hjy
    exact (not_lt_of_ge le_rfl) hjy
  · intro h p hp
    change (p.2 : ℕ) < (x p.1 : ℕ) at hp
    change (p.2 : ℕ) < (y p.1 : ℕ)
    have hxy : (x p.1 : ℕ) ≤ (y p.1 : ℕ) := by
      exact_mod_cast h p.1
    exact hp.trans_le hxy

/-- The canonical product of chains, as an order isomorphism with the
closed-set lattice of downward chain closure.-/
noncomputable def chainClosedOrderIso
    {ι : Type u} {c : ι → ℕ} :
    CapacityVector c ≃o (chainClosure c).Closeds where
  toEquiv := capacityClosedEquiv
  map_rel_iff' := fun {x y} ↦
    capacityToClosed_le_iff x y

/--
@isnad1 id=eq.0h3v.s8.bfcfbf206802 from=translated src=- shape=55a7595f vocab=cc95db86
-/
@[simp]
theorem chainClosedOrderIso_apply
    {ι : Type u} {c : ι → ℕ}
    (x : CapacityVector c) :
    (((chainClosedOrderIso x :
      (chainClosure c).Closeds) :
      Set (ChainPoint c))) = initialSegment x :=
  by
    change initialSegment x = initialSegment x
    rfl

/-- The canonical chain closure supplies the parametrization used by the
Nakayama polynomial theorem.-/
noncomputable def chainFixedTopParametrization
    {ι : Type u} [Fintype ι] {c : ι → ℕ} :
    FixedTopChainParametrization (chainClosure c) c where
  pointEquiv := Equiv.refl _
  closedOrderIso := chainClosedOrderIso
  carrier_closedOrderIso x := by
    simp

/-- The level polynomial of the canonical downward chain closure is the
product of the finite geometric chain factors.
@isnad1 id=eq.0h2v.s5.2c4fd1777a69 from=translated src=- shape=b2c86788 vocab=22805704
-/
theorem chainClosure_levelPolynomial
    {ι : Type u} [Fintype ι] (c : ι → ℕ) :
    (chainClosure c).levelPolynomial =
      ∏ i, chainPolynomial (c i) :=
  FixedTopChainParametrization.levelPolynomial_eq_prod_chainPolynomial
    chainFixedTopParametrization

/-- A concrete identification of a closure system with downward closure
on fixed-index chains produces the manuscript's fixed-top
parametrization.-/
noncomputable def fixedTopParametrizationOfRelabeling
    {ι : Type u} [Fintype ι] {c : ι → ℕ}
    {E : Type*} [Finite E]
    {cl : QuotientSubmoduleEquidistribution.SetClosure E}
    (h : QuotientSubmoduleEquidistribution.SetClosure.RelabelingEquiv
      (chainClosure c) cl) :
    FixedTopChainParametrization cl c where
  pointEquiv := h.equiv
  closedOrderIso :=
    chainClosedOrderIso.trans h.closedsOrderIso
  carrier_closedOrderIso x := by
    change
      h.equiv '' initialSegment x =
        h.equiv '' initialSegment x
    rfl

/-- It is enough to identify the actual closure with the canonical
downward chain closure; the product formula then follows automatically.
@isnad1 id=eq.0h5v.s5.a3cd94763523 from=translated src=- shape=fb9051e5 vocab=2fe1799f
-/
theorem levelPolynomial_eq_prod_of_chainRelabeling
    {ι : Type u} [Fintype ι] {c : ι → ℕ}
    {E : Type*} [Finite E]
    {cl : QuotientSubmoduleEquidistribution.SetClosure E}
    (h : QuotientSubmoduleEquidistribution.SetClosure.RelabelingEquiv
      (chainClosure c) cl) :
    cl.levelPolynomial = ∏ i, chainPolynomial (c i) := by
  rw [← h.levelPolynomial_eq,
    chainClosure_levelPolynomial]

end QuotientSubmoduleEquidistribution.NakayamaCombinatorics
