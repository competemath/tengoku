import Tengoku.EgzFormalProof.EGZ.Decomposition.Reduction
import Tengoku.EgzFormalProof.EGZ.Convex.Faces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restriction to reduced nodes

The reduced bases form a nonempty finite join-closed set.  Restriction to
this set preserves every local contribution, since a non-reduced base has
zero local weight.  The resulting flag has the same proper points, viewed
through the inclusion of its nodes in the original flag.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/--
@isnad1 id=ex.0h4v.s5.76f4905d089b from=translated src=- shape=0e8ce87c vocab=3545b7fd
-/
theorem exists_isReducedElement (Φ : FlagDecomposition p d f) :
    ∃ x, Φ.IsReducedElement x := by
  obtain ⟨q, hq⟩ := Φ.faces_visible ⊤ (RationalPolytope.Face.top _)
  exact ⟨q.base, q, hq.1, rfl⟩

/-- The join-closed set of bases which occur among the proper points.-/
abbrev ReducedNode (Φ : FlagDecomposition p d f) :=
  {x : Φ.flag.Node // Φ.IsReducedElement x}

noncomputable instance (Φ : FlagDecomposition p d f) : Fintype Φ.ReducedNode :=
  Subtype.fintype _

instance (Φ : FlagDecomposition p d f) : Nonempty Φ.ReducedNode :=
  let ⟨x, hx⟩ := Φ.exists_isReducedElement
  ⟨⟨x, hx⟩⟩

instance (Φ : FlagDecomposition p d f) : SemilatticeSup Φ.ReducedNode :=
  Subtype.semilatticeSup fun _ _ hx hy ↦ Φ.isReducedElement_sup hx hy

noncomputable instance (Φ : FlagDecomposition p d f) : OrderTop Φ.ReducedNode where
  top := Finset.univ.sup' Finset.univ_nonempty id
  le_top x := Finset.le_sup' id (Finset.mem_univ x)

/-- The convex flag obtained by retaining just the reduced nodes.-/
noncomputable abbrev reducedFlag (Φ : FlagDecomposition p d f) : ConvexFlag where
  Node := Φ.ReducedNode
  rank x := Φ.flag.rank x.1
  polytope x := Φ.flag.polytope x.1
  lattice x := Φ.flag.lattice x.1
  transition h := Φ.flag.transition h
  transition_mem h := Φ.flag.transition_mem h
  transition_lattice h := Φ.flag.transition_lattice h
  transition_refl x := Φ.flag.transition_refl x.1
  transition_trans hxy hyz := Φ.flag.transition_trans hxy hyz

/-- The inclusion of points of the restricted flag in the original flag.-/
def reducedPointInclusion (Φ : FlagDecomposition p d f)
    (q : Φ.reducedFlag.Point) : Φ.flag.Point :=
  ⟨q.base.1, q.val, q.val_mem⟩

/-- A point whose base is reduced can be viewed in the restricted flag.-/
def toReducedPoint (Φ : FlagDecomposition p d f) (q : Φ.flag.Point)
    (hq : Φ.IsReducedElement q.base) : Φ.reducedFlag.Point :=
  ⟨⟨q.base, hq⟩, q.val, q.val_mem⟩

/--
@isnad1 id=eq.1h5v.s6.42de9b027dca from=translated src=- shape=1b43411f vocab=dc877d47
-/
@[simp]
theorem reducedPointInclusion_toReducedPoint (Φ : FlagDecomposition p d f)
    (q : Φ.flag.Point) (hq : Φ.IsReducedElement q.base) :
    Φ.reducedPointInclusion (Φ.toReducedPoint q hq) = q := rfl

/-- Convex combinations in the original flag descend to the restricted
flag whenever all the displayed bases are reduced.
@isnad1 id=convexco.3h8v.s7.029b1792fd16 from=translated src=- shape=6457d89e vocab=cc6bd5ad
-/
theorem convexCombination_toReducedPoint (Φ : FlagDecomposition p d f)
    {I : Type*} [Fintype I] (points : I → Φ.flag.Point)
    (weight : I → ℝ) (q : Φ.flag.Point)
    (hpoints : ∀ i, Φ.IsReducedElement (points i).base)
    (hq : Φ.IsReducedElement q.base)
    (hcomb : ConvexFlag.ConvexCombination points weight q) :
    ConvexFlag.ConvexCombination
      (fun i ↦ Φ.toReducedPoint (points i) (hpoints i)) weight
      (Φ.toReducedPoint q hq) := by
  refine ⟨hcomb.nonnegative, hcomb.sum_eq_one, ?_, hcomb.val_eq⟩
  constructor
  · intro i hi
    exact hcomb.base_isLUB.1 i hi
  · intro x hx
    exact hcomb.base_isLUB.2 hx

/-- Inclusion into the original flag preserves convex combinations.  The
finite join of the active bases is reduced, so it can be used to compare
the two least-upper-bound conditions.
@isnad1 id=convexco.1h8v.s6.4e512aba8120 from=translated src=- shape=082ce8ad vocab=fee92a8f
-/
theorem convexCombination_reducedPointInclusion (Φ : FlagDecomposition p d f)
    {I : Type*} [Fintype I] (points : I → Φ.reducedFlag.Point)
    (weight : I → ℝ) (q : Φ.reducedFlag.Point)
    (hcomb : ConvexFlag.ConvexCombination points weight q) :
    ConvexFlag.ConvexCombination (fun i ↦ Φ.reducedPointInclusion (points i))
      weight (Φ.reducedPointInclusion q) := by
  have hpos : ∃ i, 0 < weight i := by
    by_contra! h
    have hz : ∀ i, weight i = 0 := fun i ↦ le_antisymm (h i) (hcomb.nonnegative i)
    have hs := hcomb.sum_eq_one
    simp [hz] at hs
  let s := (Finset.univ.filter fun i ↦ 0 < weight i).image
    (fun i ↦ (points i).base.1)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨(points i).base.1, Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩⟩
  have hred : Φ.IsReducedElement (s.sup' hs id) := by
    apply Φ.isReducedElement_sup'
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (points i).base.2
  refine ⟨hcomb.nonnegative, hcomb.sum_eq_one, ?_, hcomb.val_eq⟩
  constructor
  · intro i hi
    exact hcomb.base_isLUB.1 i hi
  · intro x hx
    have hqle : q.base ≤ (⟨s.sup' hs id, hred⟩ : Φ.ReducedNode) := by
      apply hcomb.base_isLUB.2
      intro i hi
      exact Finset.le_sup' id (show (points i).base.1 ∈ s from
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, hi⟩, rfl⟩)
    apply le_trans (show q.base.1 ≤ s.sup' hs id from hqle)
    apply Finset.sup'_le
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hx i (Finset.mem_filter.mp hi).2

/-- The original representation restricted to the reduced nodes.-/
noncomputable def reducedRepresentation (Φ : FlagDecomposition p d f) :
    FpRepresentation p d Φ.reducedFlag where
  space x := Φ.representation.space x.1
  map x := Φ.representation.map x.1
  space_mono h := Φ.representation.space_mono h
  map_surjective x := Φ.representation.map_surjective x.1
  compatible h := Φ.representation.compatible h
  lattice_eq_standard x := Φ.representation.lattice_eq_standard x.1

/--
@isnad1 id=eq.1h5v.s7.94ffedd54ccc from=translated src=- shape=e5dd708c vocab=671ee7f8
-/
theorem sum_reducedNode_eq (Φ : FlagDecomposition p d f) (hp : Odd p)
    (v : FpCoord p d) :
    ∑ x : Φ.ReducedNode, Φ.localWeight x.1 v = ∑ x, Φ.localWeight x v := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun x ↦ Φ.IsReducedElement x) (fun x ↦ Φ.localWeight x v)
  have hz : (∑ x : {x // ¬ Φ.IsReducedElement x}, Φ.localWeight x.1 v) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact Φ.localWeight_eq_zero_of_not_isReducedElement hp x.2 v
  simpa only [hz, add_zero] using h

/--
@isnad1 id=eq.1h6v.s6.ff4315792131 from=translated src=- shape=6dd60af1 vocab=7c401f8e
-/
theorem cumulativeWeight_reducedNode (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (v : FpCoord p d) :
    FlagDecompositionRaw.cumulativeWeight (F := Φ.reducedFlag)
      (fun y ↦ Φ.localWeight y.1) x v = Φ.cumulativeWeight x.1 v := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun y ↦ Φ.IsReducedElement y) (fun y ↦ if y ≤ x.1 then Φ.localWeight y v else 0)
  have hz : (∑ y : {y // ¬ Φ.IsReducedElement y},
      if y.1 ≤ x.1 then Φ.localWeight y.1 v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    simp [Φ.localWeight_eq_zero_of_not_isReducedElement hp y.2 v]
  simpa only [cumulativeWeight, FlagDecompositionRaw.cumulativeWeight,
    hz, add_zero, Subtype.coe_le_coe] using h

/--
@isnad1 id=eq.1h6v.s7.3e561088e996 from=translated src=- shape=fee9ab31 vocab=edced268
-/
theorem hat_reducedNode (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (z : IntCoord (Φ.flag.rank x.1)) :
    FlagDecompositionRaw.hat Φ.reducedRepresentation
      (fun y ↦ Φ.localWeight y.1) x z = Φ.hat x.1 z := by
  unfold FlagDecompositionRaw.hat hat
  have hw : FlagDecompositionRaw.cumulativeWeight (F := Φ.reducedFlag)
      (fun y ↦ Φ.localWeight y.1) x = Φ.cumulativeWeight x.1 :=
    funext (Φ.cumulativeWeight_reducedNode hp x)
  rw [hw]
  rfl

/--
@isnad1 id=iff.0h5v.s7.6681ad55e845 from=translated src=- shape=c8a9536e vocab=9cc2e161
-/
theorem omegaZero_reducedPointInclusion_iff (Φ : FlagDecomposition p d f)
    (q : Φ.reducedFlag.Point) :
    q ∈ FlagDecompositionRaw.omegaZero Φ.reducedRepresentation
        (fun x ↦ Φ.localWeight x.1) ↔
      Φ.reducedPointInclusion q ∈ Φ.omegaZero := Iff.rfl

/-- Inclusion identifies the proper-point set of the restricted data with
the original proper points whose bases lie in the restriction.
@isnad1 id=iff.0h5v.s7.540ed06a8d51 from=translated src=- shape=c8a9536e vocab=d121f5aa
-/
theorem omega_reducedPointInclusion_iff (Φ : FlagDecomposition p d f)
    (q : Φ.reducedFlag.Point) :
    q ∈ FlagDecompositionRaw.omega Φ.reducedRepresentation
        (fun x ↦ Φ.localWeight x.1) ↔
      Φ.reducedPointInclusion q ∈ Φ.omega := by
  constructor
  · rintro ⟨n, points, weight, hpoints, hcomb⟩
    exact ⟨n, fun i ↦ Φ.reducedPointInclusion (points i), weight,
      fun i ↦ (Φ.omegaZero_reducedPointInclusion_iff _).mp (hpoints i),
      Φ.convexCombination_reducedPointInclusion points weight q hcomb⟩
  · rintro ⟨n, points, weight, hpoints, hcomb⟩
    have hred (i : Fin n) : Φ.IsReducedElement (points i).base :=
      ⟨points i, ConvexFlag.subset_convexHull Φ.flag Φ.omegaZero (hpoints i), rfl⟩
    refine ⟨n, fun i ↦ Φ.toReducedPoint (points i) (hred i), weight, ?_, ?_⟩
    · intro i
      exact hpoints i
    · exact Φ.convexCombination_toReducedPoint points weight
        (Φ.reducedPointInclusion q) hred q.base.2 hcomb

/-- Restrict a decomposition to its reduced nodes.  No local mass is lost.
The odd-modulus assumption ensures that zero local lifts detect exactly
zero local finite-field weights.-/
noncomputable abbrev reduced (Φ : FlagDecomposition p d f) (hp : Odd p) :
    FlagDecomposition p d f where
  flag := Φ.reducedFlag
  representation := Φ.reducedRepresentation
  localWeight x := Φ.localWeight x.1
  local_supported x := Φ.local_supported x.1
  retained_le v := by
    change (∑ x : Φ.ReducedNode, Φ.localWeight x.1 v) ≤ f v
    rw [Φ.sum_reducedNode_eq hp]
    exact Φ.retained_le v
  liftedSupport x := Φ.liftedSupport x.1
  liftedSupport_spec x z := by
    rw [Φ.hat_reducedNode hp]
    exact Φ.liftedSupport_spec x.1 z
  liftedSupport_nonempty x := Φ.liftedSupport_nonempty x.1
  polytope_eq_liftedSupport x := Φ.polytope_eq_liftedSupport x.1
  faces_visible x Γ := by
    obtain ⟨q, hq, hbase, hcoord⟩ := Φ.faces_visible x.1 Γ
    have hred : Φ.IsReducedElement q.base := ⟨q, hq, rfl⟩
    refine ⟨Φ.toReducedPoint q hred, ?_, hbase, hcoord⟩
    exact (Φ.omega_reducedPointInclusion_iff _).mpr hq

/--
@isnad1 id=eq.1h5v.s6.3f495805d6f5 from=translated src=- shape=87c878ed vocab=080b6a25
-/
@[simp]
theorem reduced_localWeight (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) : (Φ.reduced hp).localWeight x = Φ.localWeight x.1 := rfl

/--
@isnad1 id=eq.1h5v.s6.0c12def2b8c3 from=translated src=- shape=87c878ed vocab=637b0ebe
-/
@[simp]
theorem reduced_cumulativeWeight (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) :
    (Φ.reduced hp).cumulativeWeight x = Φ.cumulativeWeight x.1 :=
  funext (Φ.cumulativeWeight_reducedNode hp x)

/--
@isnad1 id=eq.1h4v.s5.a5e0abf651a5 from=translated src=- shape=e4f1f54a vocab=7081449c
-/
@[simp]
theorem reduced_retainedWeight (Φ : FlagDecomposition p d f) (hp : Odd p) :
    (Φ.reduced hp).retainedWeight = Φ.retainedWeight :=
  funext (Φ.sum_reducedNode_eq hp)

/--
@isnad1 id=eq.1h4v.s5.ef63858095ca from=translated src=- shape=1dc25ff5 vocab=8dc2a6d1
-/
@[simp]
theorem reduced_retainedMass (Φ : FlagDecomposition p d f) (hp : Odd p) :
    (Φ.reduced hp).retainedMass = Φ.retainedMass := by
  simp only [retainedMass, Φ.reduced_retainedWeight hp]

/-- Removing non-reduced nodes cannot increase the number of nodes.
@isnad1 id=le.1h4v.s6.d4c07b61ac94 from=translated src=- shape=11890288 vocab=f29e7916
-/
theorem card_reduced_le (Φ : FlagDecomposition p d f) (hp : Odd p) :
    Fintype.card (Φ.reduced hp).flag.Node ≤ Fintype.card Φ.flag.Node :=
  Fintype.card_subtype_le _

/--
@isnad1 id=eq.1h5v.s6.b87ca0aa9377 from=translated src=- shape=51ffad32 vocab=64073be2
-/
@[simp]
theorem reduced_hat (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) : (Φ.reduced hp).hat x = Φ.hat x.1 :=
  funext (Φ.hat_reducedNode hp x)

/--
@isnad1 id=eq.1h5v.s6.20ecfdd08881 from=translated src=- shape=6199f34e vocab=480617c0
-/
@[simp]
theorem reduced_gap (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) : (Φ.reduced hp).gap x = Φ.gap x.1 := by
  simp only [gap, Φ.reduced_hat hp]

/--
@isnad1 id=iff.1h5v.s6.56d694f48961 from=translated src=- shape=83a45ee4 vocab=a39b6020
-/
@[simp]
theorem reduced_omega_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (q : Φ.reducedFlag.Point) :
    q ∈ (Φ.reduced hp).omega ↔ Φ.reducedPointInclusion q ∈ Φ.omega :=
  Φ.omega_reducedPointInclusion_iff q

/-- Every original proper point is retained: its base is reduced by
definition.  Thus inclusion identifies the two full proper-point sets.
@isnad1 id=eq.1h4v.s6.7aa66aa62788 from=translated src=- shape=26da72d9 vocab=879e45ef
-/
theorem image_reduced_omega (Φ : FlagDecomposition p d f) (hp : Odd p) :
    Φ.reducedPointInclusion '' (Φ.reduced hp).omega = Φ.omega := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    exact (Φ.reduced_omega_iff hp q').mp hq'
  · intro hq
    have hred : Φ.IsReducedElement q.base := ⟨q, hq, rfl⟩
    exact ⟨Φ.toReducedPoint q hred, (Φ.reduced_omega_iff hp _).mpr hq, rfl⟩

/-- Every retained node is reduced in the restricted decomposition.
@isnad1 id=isreduce.1h4v.s5.fe1360d2446a from=translated src=- shape=da4f1842 vocab=66f7a18b
-/
theorem reduced_isReduced (Φ : FlagDecomposition p d f) (hp : Odd p) :
    (Φ.reduced hp).IsReduced := by
  intro x
  obtain ⟨q, hq, hbase⟩ := x.2
  have hred : Φ.IsReducedElement q.base := ⟨q, hq, rfl⟩
  refine ⟨Φ.toReducedPoint q hred, (Φ.reduced_omega_iff hp _).mpr hq, ?_⟩
  exact Subtype.ext hbase

/-- Restriction preserves the same coordinate bound at every retained node.
@isnad1 id=iskbound.2h5v.s6.1a5eeee899c9 from=translated src=- shape=b6f48617 vocab=dcc7fd32
-/
theorem reduced_isKBounded (Φ : FlagDecomposition p d f) (hp : Odd p)
    {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) :
    (Φ.reduced hp).IsKBounded (fun x ↦ K x.1) :=
  fun x z hz ↦ hK x.1 z hz

/--
@isnad1 id=eq.1h6v.s6.e154244aff5f from=translated src=- shape=556b09f9 vocab=f3863704
-/
@[simp]
theorem reduced_liftedMassOn (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (S : Set (RealCoord (Φ.flag.rank x.1))) :
    (Φ.reduced hp).liftedMassOn x S = Φ.liftedMassOn x.1 S := by
  unfold liftedMassOn
  rw [Φ.reduced_hat hp]

/--
@isnad1 id=iff.1h6v.s6.a68e2b527847 from=translated src=- shape=3a648fc3 vocab=42a64eff
-/
@[simp]
theorem reduced_isLargeElement_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (ε : ℝ) (x : Φ.ReducedNode) :
    (Φ.reduced hp).IsLargeElement ε x ↔ Φ.IsLargeElement ε x.1 := by
  simp only [IsLargeElement, Φ.reduced_liftedMassOn hp, Φ.reduced_retainedMass hp]

/--
@isnad1 id=iff.1h7v.s7.2b8e95376f79 from=translated src=- shape=fc3defa1 vocab=08a81bbe
-/
@[simp]
theorem reduced_isLargeFace_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (ε : ℝ) (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    (Φ.reduced hp).IsLargeFace ε x Γ ↔ Φ.IsLargeFace ε x.1 Γ := by
  simp only [IsLargeFace, Φ.reduced_liftedMassOn hp, Φ.reduced_retainedMass hp]

/--
@isnad1 id=iff.1h7v.s6.36fc9e1ed327 from=translated src=- shape=9eb04c08 vocab=98815512
-/
@[simp]
theorem reduced_isCompleteElement_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (t : ℕ) (δ : ℝ) :
    (Φ.reduced hp).IsCompleteElement x t δ ↔ Φ.IsCompleteElement x.1 t δ := by
  simp only [IsCompleteElement, Φ.reduced_cumulativeWeight hp]
  rfl

/-- The ambient affine spans and affine integer generating sets at retained
nodes are unchanged, so minimality is preserved.
@isnad1 id=isminima.2h4v.s5.b394ae2661ef from=translated src=- shape=9ea171b1 vocab=df3c4d4a
-/
theorem reduced_isMinimal (Φ : FlagDecomposition p d f) (hp : Odd p)
    (hmin : Φ.IsMinimal) : (Φ.reduced hp).IsMinimal := by
  intro x
  obtain ⟨hspace, hspan⟩ := hmin x.1
  refine ⟨?_, hspan⟩
  rw [Φ.reduced_cumulativeWeight hp]
  exact hspace

/--
@isnad1 id=iff.1h7v.s7.370c2e850c30 from=translated src=- shape=a4ffe0cb vocab=146fdd50
-/
theorem reduced_pointsOnFace_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face)
    (q : Φ.reducedFlag.Point) :
    q ∈ (Φ.reduced hp).pointsOnFace x Γ ↔
      Φ.reducedPointInclusion q ∈ Φ.pointsOnFace x.1 Γ := by
  change (q ∈ (Φ.reduced hp).omega ∧
      ∃ h : q.base ≤ x, q.coord h ∈ Γ.carrier) ↔
    (Φ.reducedPointInclusion q ∈ Φ.omega ∧
      ∃ h : q.base.1 ≤ x.1, (Φ.reducedPointInclusion q).coord h ∈ Γ.carrier)
  rw [Φ.reduced_omega_iff hp]
  rfl

/--
@isnad1 id=iff.1h7v.s8.bc8441bd131e from=translated src=- shape=5335a6d4 vocab=c99a8230
-/
theorem reduced_faceBases_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x y : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    y ∈ (Φ.reduced hp).faceBases x Γ ↔ y.1 ∈ Φ.faceBases x.1 Γ := by
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, hbase⟩
    exact ⟨Φ.reducedPointInclusion q,
      (Φ.reduced_pointsOnFace_iff hp x Γ q).mp hq,
      congrArg Subtype.val hbase⟩
  · rintro ⟨q, hq, hbase⟩
    have hred : Φ.IsReducedElement q.base := ⟨q, hq.1, rfl⟩
    exact ⟨Φ.toReducedPoint q hred,
      (Φ.reduced_pointsOnFace_iff hp x Γ _).mpr hq,
      Subtype.ext hbase⟩

/-- The face index computed after restriction is the same original node.
Every face index is reduced, which makes it available in the restriction.
@isnad1 id=eq.1h6v.s7.8e998503bd14 from=translated src=- shape=85fc2760 vocab=082e5d5d
-/
theorem reduced_faceIndex_val (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    ((Φ.reduced hp).faceIndex x Γ).1 = Φ.faceIndex x.1 Γ := by
  apply le_antisymm
  · have hle : (Φ.reduced hp).faceIndex x Γ ≤
        (⟨Φ.faceIndex x.1 Γ, Φ.isReducedElement_faceIndex x.1 Γ⟩ : Φ.ReducedNode) := by
      unfold faceIndex
      apply Finset.sup'_le
      intro y hy
      exact Finset.le_sup' id ((Φ.reduced_faceBases_iff hp x y Γ).mp hy)
    exact hle
  · unfold faceIndex
    apply Finset.sup'_le
    intro y hy
    have hyred : Φ.IsReducedElement y := by
      simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      exact ⟨q, hq.1, rfl⟩
    have hynew := (Φ.reduced_faceBases_iff hp x ⟨y, hyred⟩ Γ).mpr hy
    have hle : (⟨y, hyred⟩ : Φ.ReducedNode) ≤ (Φ.reduced hp).faceIndex x Γ :=
      Finset.le_sup' id hynew
    exact hle

/--
@isnad1 id=eq.1h6v.s7.7fd3ef3bbd90 from=translated src=- shape=28932cef vocab=8f444702
-/
theorem reduced_faceIndex (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    (Φ.reduced hp).faceIndex x Γ =
      (⟨Φ.faceIndex x.1 Γ, Φ.isReducedElement_faceIndex x.1 Γ⟩ : Φ.ReducedNode) :=
  Subtype.ext (Φ.reduced_faceIndex_val hp x Γ)

/--
@isnad1 id=iff.1h6v.s7.2e526bac320c from=translated src=- shape=ae01d584 vocab=874ce53e
-/
@[simp]
theorem reduced_isRealizedFace_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    (Φ.reduced hp).IsRealizedFace x Γ ↔ Φ.IsRealizedFace x.1 Γ := by
  have hcongr (a b : Φ.flag.Node) (ha : a ≤ x.1) (hb : b ≤ x.1)
      (hab : a = b) :
      (∀ q ∈ (Φ.flag.polytope a).carrier, (Φ.flag.transition ha).real q ∈ Γ.carrier) ↔
      (∀ q ∈ (Φ.flag.polytope b).carrier, (Φ.flag.transition hb).real q ∈ Γ.carrier) := by
    subst b
    rfl
  exact hcongr _ _ ((Φ.reduced hp).faceIndex_le x Γ) (Φ.faceIndex_le x.1 Γ)
    (Φ.reduced_faceIndex_val hp x Γ)

/-- Restriction preserves completeness with the same thresholds at every
retained node and the same parameters.
@isnad1 id=iscomple.2h7v.s6.b85551b84fe8 from=translated src=- shape=d428706e vocab=289c66a7
-/
theorem reduced_isComplete (Φ : FlagDecomposition p d f) (hp : Odd p)
    {T : Φ.flag.Node → ℕ} {ε δ : ℝ} (hcomplete : Φ.IsComplete T ε δ) :
    (Φ.reduced hp).IsComplete (fun x ↦ T x.1) ε δ := by
  refine ⟨Φ.reduced_isMinimal hp hcomplete.1, Φ.reduced_isReduced hp, ?_, ?_⟩
  · intro x hx
    exact (Φ.reduced_isCompleteElement_iff hp x (T x.1) δ).mpr
      (hcomplete.2.2.1 x.1 ((Φ.reduced_isLargeElement_iff hp ε x).mp hx))
  · intro x Γ hΓ
    exact (Φ.reduced_isRealizedFace_iff hp x Γ).mpr
      (hcomplete.2.2.2 x.1 Γ ((Φ.reduced_isLargeFace_iff hp ε x Γ).mp hΓ))

end EGZ.FlagDecomposition
