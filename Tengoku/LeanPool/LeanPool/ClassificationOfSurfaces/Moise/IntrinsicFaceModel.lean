/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.IntrinsicSubdivision
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.Anchors

/-!
# Standard plane models for intrinsic faces

Every maximal face of an intrinsic complex is a closed barycentric triangle.  This file gives
the explicit coordinate reindexing homeomorphism to the standard plane triangle.  It is the
source-side bridge used to apply the already proved polygonal Schoenflies extension cellwise.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open scoped BigOperators _root_.Topology

/--
@isnad1 id=ispure2.0h0v.s1.7dad4e1bda35 from=translated src=- shape=49959d42 vocab=49612675
-/
theorem standardTrianglePlaneComplex_pure : standardTrianglePlaneComplex.IsPure2 := by
  intro s hs
  refine ⟨Finset.univ, ?_, Finset.subset_univ s, ?_⟩
  · change (Finset.univ : Finset (Fin 3)) ∈
      (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty)
    simp
  · change (Finset.univ : Finset (Fin 3)).card = 3
    decide

/--
@isnad1 id=mem.0h0v.s5.bc34a0be9d65 from=translated src=- shape=7cf1b3f5 vocab=de9a2f0e
-/
theorem standardTriangle_univ_mem_cells :
    (Finset.univ : Finset (Fin 3)) ∈ standardTrianglePlaneComplex.cells := by
  change (Finset.univ : Finset (Fin 3)) ∈
    (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty).filter
      fun t => t.card = 3
  decide

/-- The unique maximal face of the standard triangle mesh. -/
noncomputable def standardTriangleMeshFace :
    standardTrianglePlaneComplex.toTriangleMesh.Triangle :=
  ⟨Finset.univ, standardTriangle_univ_mem_cells⟩

/--
@isnad1 id=eq.0h0v.s7.7c9db417899d from=translated src=- shape=b2ead6d5 vocab=a7c10749
-/
theorem standardTrianglePlaneComplex_support :
    standardTrianglePlaneComplex.support =
      convexHull ℝ (Set.range standardTriangleVertex) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    rw [PlaneComplex.cellCarrier] at hxs
    apply convexHull_mono _ hxs
    rintro y ⟨i, hi, rfl⟩
    exact ⟨i, rfl⟩
  · intro x hx
    apply standardTrianglePlaneComplex.cellCarrier_subset_support
      (standardTrianglePlaneComplex.mem_simplexes_of_mem_cells
        standardTriangle_univ_mem_cells)
    rw [PlaneComplex.cellCarrier]
    change x ∈ convexHull ℝ
      (standardTriangleVertex '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)))
    simpa only [Finset.coe_univ, Set.image_univ] using hx

/--
@isnad1 id=eq.0h0v.s4.ff3b6be67093 from=translated src=- shape=55f2a188 vocab=de97afbb
-/
theorem standardTriangle_cellCarrier_univ :
    standardTrianglePlaneComplex.cellCarrier (Finset.univ : Finset (Fin 3)) =
      standardTrianglePlaneComplex.support := by
  rw [PlaneComplex.cellCarrier, standardTrianglePlaneComplex_position]
  change convexHull ℝ
    (standardTriangleVertex '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = _
  rw [Finset.coe_univ, Set.image_univ, ← standardTrianglePlaneComplex_support]

/--
@isnad1 id=istriang.0h0v.s1.95a16042de8c from=translated src=- shape=87ceb31f vocab=9e01521f
-/
theorem standardTrianglePlaneComplex_isTriangle :
    IsTriangle standardTrianglePlaneComplex.support := by
  exact ⟨standardTriangleVertex, standardTriangleVertex_affineIndependent,
    standardTrianglePlaneComplex_support⟩

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/--
@isnad1 id=eq.0h1v.s8.62c7749064da from=translated src=- shape=c3258795 vocab=1bd02b07
-/
@[simp] theorem finEquiv_symm_three (i : ZMod 3) :
    (ZMod.finEquiv 3).symm i = i := rfl

/-- The chosen ordering of one intrinsic face, viewed as an embedding into all vertices. -/
noncomputable def faceVertexEmbedding (t : K.Face) : Fin 3 ↪ K.Vertex where
  toFun i := (K.faceVertexEquiv t i).1
  inj' := fun _ _ hij => (K.faceVertexEquiv t).injective (Subtype.ext hij)

/-- The two standard indices belonging to cyclic side `i`. -/
noncomputable def faceStandardEdge (i : ZMod 3) : Finset (Fin 3) :=
  {(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)}

/--
@isnad1 id=eq.0h3v.s8.397abbdf62df from=translated src=- shape=cc55027c vocab=02364901
-/
theorem faceVertexEmbedding_cyclic (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t ((ZMod.finEquiv 3).symm i) = K.faceVertex t i := rfl

/--
@isnad1 id=eq.0h3v.s6.f0fd9b46c10c from=translated src=- shape=5004c8cd vocab=98b7ba05
-/
theorem faceStandardEdge_map (t : K.Face) (i : ZMod 3) :
    (faceStandardEdge i).map (K.faceVertexEmbedding t) = (K.faceEdge t i).1 := by
  simp only [faceStandardEdge, Finset.map_insert, Finset.map_singleton,
    faceVertexEmbedding, K.faceEdge_val]
  rfl

/--
@isnad1 id=mem.0h1v.s5.4dc1250ab3de from=translated src=- shape=c5bdba75 vocab=aa1fa090
-/
theorem faceStandardEdge_mem_simplexes (i : ZMod 3) :
    faceStandardEdge i ∈ standardTrianglePlaneComplex.simplexes := by
  change faceStandardEdge i ∈
    (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  exact ⟨i, Finset.mem_insert_self i {i + 1}⟩

/-- The geometric carrier of a standard cyclic edge is its polygon side.
@isnad1 id=eq.0h1v.s4.23d3a8f61d33 from=translated src=- shape=3966c185 vocab=4fa2fb08
-/
theorem standard_cellCarrier_faceStandardEdge (i : ZMod 3) :
    standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) =
      standardTriangleCircle.edgeSegment i := by
  change standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) =
    segment ℝ (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
      (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
  rw [PlaneComplex.cellCarrier, ← convexHull_pair]
  congr 1
  ext p
  constructor
  · rintro ⟨j, hj, rfl⟩
    change j ∈ ({(ZMod.finEquiv 3).symm i,
      (ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)) at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl rfl
    · have hj' := Finset.mem_singleton.mp hj
      subst j
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(ZMod.finEquiv 3).symm i, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨(ZMod.finEquiv 3).symm (i + 1),
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl⟩

/-- The one-skeleton of the standard triangle complex is exactly its polygonal frontier.
@isnad1 id=eq.0h0v.s3.ccd7c4f8622e from=translated src=- shape=f0e44a99 vocab=bd9a5f71
-/
theorem standardTriangle_oneSkeleton_support :
    standardTrianglePlaneComplex.oneSkeleton.support =
      standardTriangleCircle.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hsData := standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mp hs
    have hsSide : ∃ i : ZMod 3, s ⊆ faceStandardEdge i := by
      by_cases h0 : (0 : Fin 3) ∈ s
      · by_cases h1 : (1 : Fin 3) ∈ s
        · have h2 : (2 : Fin 3) ∉ s := by
            intro h2
            have hsub : ({0, 1, 2} : Finset (Fin 3)) ⊆ s := by
              simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
              exact ⟨h0, h1, h2⟩
            have hcard := Finset.card_le_card hsub
            have hthree : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
            rw [hthree] at hcard
            exact (by omega : ¬ (3 : ℕ) ≤ 2) (hcard.trans hsData.2)
          refine ⟨0, ?_⟩
          change s ⊆ ({0, 1} : Finset (Fin 3))
          intro j hj
          fin_cases j
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact (h2 hj).elim
        · refine ⟨2, ?_⟩
          change s ⊆ ({2, 0} : Finset (Fin 3))
          intro j hj
          fin_cases j
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact (h1 hj).elim
          · exact Finset.mem_insert_self _ _
      · refine ⟨1, ?_⟩
        change s ⊆ ({1, 2} : Finset (Fin 3))
        intro j hj
        fin_cases j
        · exact (h0 hj).elim
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨i, hsi⟩ := hsSide
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← standard_cellCarrier_faceStandardEdge i]
    exact convexHull_mono (Set.image_mono hsi) hxs
  · intro x hx
    change x ∈ ⋃ i : ZMod 3, standardTriangleCircle.edgeSegment i at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [← standard_cellCarrier_faceStandardEdge i] at hxi
    rw [PlaneComplex.support]
    apply Set.mem_iUnion₂.mpr
    refine ⟨faceStandardEdge i, ?_, hxi⟩
    apply standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
    refine ⟨faceStandardEdge_mem_simplexes i, ?_⟩
    rw [faceStandardEdge]
    calc
      ({(ZMod.finEquiv 3).symm i,
          (ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)).card ≤
          ({(ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by rw [Finset.card_singleton]

/-- One closed maximal face, as a subtype of the intrinsic realization. -/
abbrev ClosedFace (t : K.Face) := {x : K.realization // x ∈ K.faceCarrier t.1}

/-- Reindex the barycentric coordinates of an intrinsic face by its chosen `Fin 3` ordering. -/
noncomputable def faceReindexToStandard (t : K.Face) (x : K.ClosedFace t) :
    standardTrianglePlaneComplex.toIntrinsic.realization := by
  let z : Fin 3 → ℝ := fun i => x.1.1 (K.faceVertexEquiv t i).1
  refine ⟨z, ⟨?_, ?_⟩, ⟨Finset.univ, standardTriangle_univ_mem_cells, ?_⟩⟩
  · intro i
    exact x.1.2.1.1 _
  · calc
      ∑ i, z i = ∑ v : t.1, x.1.1 v.1 :=
        (K.faceVertexEquiv t).sum_comp (fun v : t.1 => x.1.1 v.1)
      _ = ∑ v ∈ t.1, x.1.1 v := by rw [Finset.sum_coe_sort]
      _ = ∑ v, x.1.1 v :=
        Finset.sum_subset (Finset.subset_univ t.1) fun v _ hv => x.2 v hv
      _ = 1 := x.1.2.1.2
  · intro i hi
    exact (hi (Finset.mem_univ i)).elim

/-- Extend standard barycentric coordinates by zero away from the chosen intrinsic face. -/
noncomputable def faceReindexFromStandard (t : K.Face)
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) : K.ClosedFace t := by
  let x : K.Vertex → ℝ := fun v =>
    if hv : v ∈ t.1 then z.1 ((K.faceVertexEquiv t).symm ⟨v, hv⟩) else 0
  refine ⟨⟨x, ⟨?_, ?_⟩, ⟨t.1, t.2, ?_⟩⟩, ?_⟩
  · intro v
    dsimp [x]
    split_ifs with hv
    · exact z.2.1.1 _
    · exact le_rfl
  · calc
      ∑ v, x v = ∑ v ∈ t.1, x v :=
        (Finset.sum_subset (Finset.subset_univ t.1) fun v _ hv => by
          simp [x, hv]).symm
      _ = ∑ v : t.1, z.1 ((K.faceVertexEquiv t).symm v) := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro v hv
        simp [x, v.2]
      _ = ∑ i : Fin 3, z.1 i :=
        (K.faceVertexEquiv t).symm.sum_comp (fun i : Fin 3 => z.1 i)
      _ = 1 := z.2.1.2
  · intro v hv
    simp [x, hv]
  · intro v hv
    simp [x, hv]

/--
@isnad1 id=eq.0h3v.s4.ed28025be660 from=translated src=- shape=9a6007cb vocab=33ef414a
-/
@[simp] theorem faceReindexFromStandard_toStandard (t : K.Face) (x : K.ClosedFace t) :
    K.faceReindexFromStandard t (K.faceReindexToStandard t x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ t.1
  · simp [faceReindexFromStandard, faceReindexToStandard, hv]
  · simp [faceReindexFromStandard, hv, x.2 v hv]

/--
@isnad1 id=eq.0h3v.s4.bc29247347e3 from=translated src=- shape=2ba38d80 vocab=d5365dc0
-/
@[simp] theorem faceReindexToStandard_fromStandard (t : K.Face)
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    K.faceReindexToStandard t (K.faceReindexFromStandard t z) = z := by
  apply Subtype.ext
  funext i
  simp [faceReindexToStandard, faceReindexFromStandard]

/--
@isnad1 id=continuo.0h2v.s7.adb3fd862405 from=translated src=- shape=0feac41f vocab=b772cfd3
-/
theorem continuous_faceReindexToStandard (t : K.Face) :
    Continuous (K.faceReindexToStandard t) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply (K.faceVertexEquiv t i).1).comp continuous_subtype_val).comp
    continuous_subtype_val

/-- The canonical barycentric homeomorphism from one intrinsic face to the standard intrinsic
triangle. -/
noncomputable def faceReindexHomeomorph (t : K.Face) :
    K.ClosedFace t ≃ₜ standardTrianglePlaneComplex.toIntrinsic.realization := by
  let e : K.ClosedFace t ≃ standardTrianglePlaneComplex.toIntrinsic.realization := {
    toFun := K.faceReindexToStandard t
    invFun := K.faceReindexFromStandard t
    left_inv := K.faceReindexFromStandard_toStandard t
    right_inv := K.faceReindexToStandard_fromStandard t }
  letI : CompactSpace (K.ClosedFace t) :=
    isCompact_iff_compactSpace.mp (K.faceCarrier_closed t.1).isCompact
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (K.continuous_faceReindexToStandard t)

/-- Reindexing carries any selected standard subface exactly to the corresponding intrinsic
vertex set.
@isnad1 id=iff.0h4v.s6.0b1ec6884ad7 from=translated src=- shape=9f3d5e88 vocab=6b075699
-/
theorem faceReindexToStandard_mem_faceCarrier (t : K.Face) (s : Finset (Fin 3))
    (x : K.ClosedFace t) :
    K.faceReindexToStandard t x ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s ↔
      x.1 ∈ K.faceCarrier (s.map (K.faceVertexEmbedding t)) := by
  constructor
  · intro hz v hv
    by_cases hvt : v ∈ t.1
    · let j : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hvt⟩
      have hj : j ∉ s := by
        intro hjs
        apply hv
        apply Finset.mem_map.mpr
        refine ⟨j, hjs, ?_⟩
        exact congrArg Subtype.val ((K.faceVertexEquiv t).apply_symm_apply ⟨v, hvt⟩)
      have := hz j hj
      change x.1.1 (K.faceVertexEmbedding t j) = 0 at this
      rw [show K.faceVertexEmbedding t j = v from
        congrArg Subtype.val ((K.faceVertexEquiv t).apply_symm_apply ⟨v, hvt⟩)] at this
      exact this
    · exact x.2 v hvt
  · intro hx j hj
    change x.1.1 (K.faceVertexEmbedding t j) = 0
    apply hx
    intro hmem
    obtain ⟨k, hks, hkj⟩ := Finset.mem_map.mp hmem
    have hkj' : k = j := (K.faceVertexEmbedding t).injective hkj
    exact hj (hkj' ▸ hks)

/-- The standard plane realization of one intrinsic closed face. -/
noncomputable def facePlaneHomeomorph (t : K.Face) :
    K.ClosedFace t ≃ₜ standardTrianglePlaneComplex.support :=
  (K.faceReindexHomeomorph t).trans
    (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure)

/-- Restrict ambient intrinsic barycentric coordinates to the ordered vertices of one face. -/
noncomputable def faceCoordRestrictionAffine (t : K.Face) :
    (K.Vertex → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  AffineMap.pi fun j =>
    (LinearMap.proj (K.faceVertexEmbedding t j)).toAffineMap

/--
@isnad1 id=eq.0h4v.s8.36f523cb08e1 from=translated src=- shape=544c6814 vocab=4a0790d0
-/
@[simp] theorem faceCoordRestrictionAffine_apply (t : K.Face)
    (x : K.Vertex → ℝ) (j : Fin 3) :
    K.faceCoordRestrictionAffine t x j =
      x (K.faceVertexEmbedding t j) := by
  rfl

/-- The forward standard-plane chart is affine in the ambient intrinsic barycentric
coordinates. -/
noncomputable def facePlaneForwardAffine (t : K.Face) :
    (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
  standardTrianglePlaneComplex.baryEvalAffine.comp
    (K.faceCoordRestrictionAffine t)

/--
@isnad1 id=eq.0h3v.s10.0c717e39d9eb from=translated src=- shape=8169c7f5 vocab=f322f246
-/
theorem facePlaneHomeomorph_val_eq_forwardAffine (t : K.Face)
    (x : K.ClosedFace t) :
    (K.facePlaneHomeomorph t x).1 =
      K.facePlaneForwardAffine t x.1.1 := by
  change standardTrianglePlaneComplex.baryEval
      (K.faceReindexToStandard t x).1 =
    standardTrianglePlaneComplex.baryEval
      (K.faceCoordRestrictionAffine t x.1.1)
  apply congrArg standardTrianglePlaneComplex.baryEval
  funext j
  rfl

/-- Affinely extend standard face coordinates by zero away from the selected intrinsic face. -/
noncomputable def faceCoordExtensionAffine (t : K.Face) :
    (Fin 3 → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  AffineMap.pi fun v =>
    if hv : v ∈ t.1 then
      (LinearMap.proj ((K.faceVertexEquiv t).symm ⟨v, hv⟩)).toAffineMap
    else
      AffineMap.const ℝ (Fin 3 → ℝ) 0

/--
@isnad1 id=eq.1h4v.s9.809316358795 from=translated src=- shape=ae225ed4 vocab=811faf51
-/
@[simp] theorem faceCoordExtensionAffine_apply_of_mem (t : K.Face)
    (z : Fin 3 → ℝ) {v : K.Vertex} (hv : v ∈ t.1) :
    K.faceCoordExtensionAffine t z v =
      z ((K.faceVertexEquiv t).symm ⟨v, hv⟩) := by
  simp [faceCoordExtensionAffine, hv]

/--
@isnad1 id=eq.1h4v.s8.1038a2fc5627 from=translated src=- shape=d4e99eb3 vocab=c2b1cf1f
-/
@[simp] theorem faceCoordExtensionAffine_apply_of_notMem (t : K.Face)
    (z : Fin 3 → ℝ) {v : K.Vertex} (hv : v ∉ t.1) :
    K.faceCoordExtensionAffine t z v = 0 := by
  simp [faceCoordExtensionAffine, hv]

/-- The barycentric-coordinate formula for the inverse standard plane chart of one intrinsic
face. -/
noncomputable def facePlaneInverseAffine (t : K.Face) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
  (K.faceCoordExtensionAffine t).comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

/-- The inverse-chart affine formula takes each standard corner to the corresponding intrinsic
unit barycentric coordinate.
@isnad1 id=eq.0h3v.s9.b96a30b7e530 from=translated src=- shape=21dcfa46 vocab=c0960f1f
-/
theorem facePlaneInverseAffine_standardVertex (t : K.Face) (j : Fin 3) :
    K.facePlaneInverseAffine t (standardTriangleVertex j) =
      Pi.single (K.faceVertexEmbedding t j) 1 := by
  have hc := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace (v := j) (by
      change j ∈ (Finset.univ : Finset (Fin 3))
      simp)
  rw [standardTrianglePlaneComplex_position] at hc
  funext v
  by_cases hv : v ∈ t.1
  · rw [facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_mem _ _ hv, hc]
    by_cases hvj : v = K.faceVertexEmbedding t j
    · have hkj : (K.faceVertexEquiv t).symm ⟨v, hv⟩ = j := by
        apply (K.faceVertexEquiv t).injective
        rw [(K.faceVertexEquiv t).apply_symm_apply]
        apply Subtype.ext
        exact hvj
      rw [hkj, hvj]
      simp
    · have hkj : (K.faceVertexEquiv t).symm ⟨v, hv⟩ ≠ j := by
        intro h
        apply hvj
        change v = (K.faceVertexEquiv t j).1
        exact congrArg Subtype.val ((K.faceVertexEquiv t).symm_apply_eq.mp h)
      simp [hkj, hvj]
  · rw [facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_notMem _ _ hv]
    have hvj : v ≠ K.faceVertexEmbedding t j := by
      intro hvj
      apply hv
      rw [hvj]
      exact (K.faceVertexEquiv t j).2
    simp [hvj]

/-- The first endpoint of a cyclic face edge belongs to the containing face.
@isnad1 id=mem.0h3v.s6.b93b27bd3c97 from=translated src=- shape=75842cca vocab=3bba79a6
-/
theorem edgeFirst_faceEdge_mem_face (t : K.Face) (i : ZMod 3) :
    K.edgeFirst (K.faceEdge t i) ∈ t.1 := by
  have h := K.edgeFirst_mem (K.faceEdge t i)
  rw [K.faceEdge_val] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · simpa only [h] using K.faceVertex_mem t i
  · simpa only [h] using K.faceVertex_mem t (i + 1)

/-- The second endpoint of a cyclic face edge belongs to the containing face.
@isnad1 id=mem.0h3v.s6.89d0b11fffa2 from=translated src=- shape=75842cca vocab=9a55a65a
-/
theorem edgeSecond_faceEdge_mem_face (t : K.Face) (i : ZMod 3) :
    K.edgeSecond (K.faceEdge t i) ∈ t.1 := by
  have h := K.edgeSecond_mem (K.faceEdge t i)
  rw [K.faceEdge_val] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · simpa only [h] using K.faceVertex_mem t i
  · simpa only [h] using K.faceVertex_mem t (i + 1)

/-- The standard corner corresponding to the globally chosen first endpoint of a face edge. -/
noncomputable def faceEdgeFirstIndex (t : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv t).symm
    ⟨K.edgeFirst (K.faceEdge t i), K.edgeFirst_faceEdge_mem_face t i⟩

/-- The standard corner corresponding to the globally chosen second endpoint of a face edge. -/
noncomputable def faceEdgeSecondIndex (t : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv t).symm
    ⟨K.edgeSecond (K.faceEdge t i), K.edgeSecond_faceEdge_mem_face t i⟩

/--
@isnad1 id=eq.0h3v.s5.2aebdeb3a5be from=translated src=- shape=f20bc67f vocab=f415cfb0
-/
@[simp] theorem faceVertexEmbedding_faceEdgeFirstIndex (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t (K.faceEdgeFirstIndex t i) =
      K.edgeFirst (K.faceEdge t i) := by
  change ((K.faceVertexEquiv t) ((K.faceVertexEquiv t).symm _)).1 = _
  rw [(K.faceVertexEquiv t).apply_symm_apply]

/--
@isnad1 id=eq.0h3v.s5.a8a3700587fe from=translated src=- shape=f20bc67f vocab=669f022d
-/
@[simp] theorem faceVertexEmbedding_faceEdgeSecondIndex (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t (K.faceEdgeSecondIndex t i) =
      K.edgeSecond (K.faceEdge t i) := by
  change ((K.faceVertexEquiv t) ((K.faceVertexEquiv t).symm _)).1 = _
  rw [(K.faceVertexEquiv t).apply_symm_apply]

/-- The two standard endpoint indices are exactly the cyclic standard side, with the order
chosen globally by the intrinsic edge.
@isnad1 id=eq.0h3v.s6.41eef5d122a2 from=translated src=- shape=767afadc vocab=63db67f3
-/
theorem faceStandardEdge_eq_endpointIndices (t : K.Face) (i : ZMod 3) :
    faceStandardEdge i =
      {K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} := by
  apply Finset.map_injective (K.faceVertexEmbedding t)
  rw [K.faceStandardEdge_map t i, Finset.map_insert, Finset.map_singleton,
    K.faceVertexEmbedding_faceEdgeFirstIndex,
    K.faceVertexEmbedding_faceEdgeSecondIndex, K.edge_eq_pair]

/-- The standard source point on a face side, oriented by the global intrinsic edge ordering. -/
noncomputable def faceEdgeSourcePoint (t : K.Face) (i : ZMod 3) (r : ℝ) : Plane :=
  AffineMap.lineMap
    (standardTriangleVertex (K.faceEdgeFirstIndex t i))
    (standardTriangleVertex (K.faceEdgeSecondIndex t i)) r

/-- The inverse face chart carries the oriented standard side parameter to the corresponding
intrinsic barycentric line parameter.
@isnad1 id=eq.0h4v.s9.7ba309d1bac9 from=translated src=- shape=4aee227a vocab=1558ae35
-/
theorem facePlaneInverseAffine_faceEdgeSourcePoint (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.facePlaneInverseAffine t (K.faceEdgeSourcePoint t i r) =
      (AffineMap.lineMap (k := ℝ)
        (Pi.single (K.edgeFirst (K.faceEdge t i)) (1 : ℝ) : K.Vertex → ℝ)
        (Pi.single (K.edgeSecond (K.faceEdge t i)) (1 : ℝ) : K.Vertex → ℝ)) r := by
  rw [faceEdgeSourcePoint, AffineMap.apply_lineMap,
    K.facePlaneInverseAffine_standardVertex,
    K.facePlaneInverseAffine_standardVertex,
    K.faceVertexEmbedding_faceEdgeFirstIndex,
    K.faceVertexEmbedding_faceEdgeSecondIndex]

/-- On the oriented standard side, the second intrinsic barycentric coordinate is its affine
parameter.
@isnad1 id=eq.0h4v.s9.c12f67e10fd5 from=translated src=- shape=8f33a1af vocab=195491d7
-/
theorem facePlaneInverseAffine_faceEdgeSourcePoint_apply_second
    (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.facePlaneInverseAffine t (K.faceEdgeSourcePoint t i r)
        (K.edgeSecond (K.faceEdge t i)) = r := by
  rw [K.facePlaneInverseAffine_faceEdgeSourcePoint]
  simp [AffineMap.lineMap_apply_module,
    K.edgeFirst_ne_edgeSecond (K.faceEdge t i)]

/-- Every unit-interval source point lies on the corresponding standard side.
@isnad1 id=mem.1h4v.s5.40672659643d from=translated src=- shape=eecf8465 vocab=e3002f90
-/
theorem faceEdgeSourcePoint_mem_standardEdge (t : K.Face) (i : ZMod 3)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint t i r ∈
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices t i, PlaneComplex.cellCarrier]
  change AffineMap.lineMap
      (standardTriangleVertex (K.faceEdgeFirstIndex t i))
      (standardTriangleVertex (K.faceEdgeSecondIndex t i)) r ∈
    convexHull ℝ
      (standardTriangleVertex ''
        (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
          Set (Fin 3)))
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex t i),
        standardTriangleVertex (K.faceEdgeSecondIndex t i)} by
    ext p
    simp]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact ⟨r, hr, rfl⟩

/-- The oriented unit interval covers exactly the corresponding standard side.
@isnad1 id=eq.0h3v.s5.cfd2da1976df from=translated src=- shape=03c4fd7c vocab=85726f41
-/
theorem faceEdgeSourcePoint_image_Icc (t : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint t i '' Set.Icc (0 : ℝ) 1 =
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices t i, PlaneComplex.cellCarrier]
  have himage : standardTriangleVertex ''
      (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex t i),
        standardTriangleVertex (K.faceEdgeSecondIndex t i)} := by
    ext p
    simp
  rw [himage, convexHull_pair, segment_eq_image_lineMap]
  rfl

/-- The inverse face chart is the restriction of `facePlaneInverseAffine` to the closed
standard triangle.
@isnad1 id=eq.0h3v.s10.9c2be12fa7b8 from=translated src=- shape=f76afa78 vocab=f1da49a6
-/
theorem facePlaneHomeomorph_symm_val (t : K.Face)
    (p : standardTrianglePlaneComplex.support) :
    ((K.facePlaneHomeomorph t).symm p).1.1 = K.facePlaneInverseAffine t p.1 := by
  let z := (standardTrianglePlaneComplex.realizationHomeomorph
    standardTrianglePlaneComplex_pure).symm p
  have hz : z.1 = standardTrianglePlaneComplex.faceCoords
      standardTriangleMeshFace p.1 := by
    apply standardTrianglePlaneComplex.realizationHomeomorph_symm_val_eq_faceCoords
      standardTrianglePlaneComplex_pure standardTriangleMeshFace p
    change p.1 ∈ standardTrianglePlaneComplex.cellCarrier
      (Finset.univ : Finset (Fin 3))
    rw [standardTriangle_cellCarrier_univ]
    exact p.2
  change (K.faceReindexFromStandard t z).1.1 = K.facePlaneInverseAffine t p.1
  funext v
  by_cases hv : v ∈ t.1
  · simp only [faceReindexFromStandard, dite_eq_left hv,
      facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_mem _ _ hv]
    exact congrFun hz ((K.faceVertexEquiv t).symm ⟨v, hv⟩)
  · simp [faceReindexFromStandard, facePlaneInverseAffine, hv]

/-- The standard plane chart sends cyclic intrinsic edge `i` exactly onto cyclic side `i` of
the standard triangle.
@isnad1 id=eq.0h3v.s9.9fdbe43f34d1 from=translated src=- shape=2b672fcd vocab=fd730a9a
-/
theorem facePlaneHomeomorph_image_edge (t : K.Face) (i : ZMod 3) :
    (fun x : K.ClosedFace t => (K.facePlaneHomeomorph t x).1) ''
        {x : K.ClosedFace t | x.1 ∈ K.faceCarrier (K.faceEdge t i).1} =
      standardTriangleCircle.edgeSegment i := by
  let s := faceStandardEdge i
  have hs : s ∈ standardTrianglePlaneComplex.simplexes :=
    faceStandardEdge_mem_simplexes i
  have hgeom := standardTrianglePlaneComplex.realizationHomeomorph_image_faceCarrier
    standardTrianglePlaneComplex_pure hs
  rw [standard_cellCarrier_faceStandardEdge i] at hgeom
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    let z := K.faceReindexToStandard t x
    have hz : z ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s := by
      rw [K.faceReindexToStandard_mem_faceCarrier t s x,
        K.faceStandardEdge_map t i]
      exact hx
    rw [← hgeom]
    refine ⟨z, hz, ?_⟩
    rfl
  · intro p hp
    rw [← hgeom] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    let x : K.ClosedFace t := (K.faceReindexHomeomorph t).symm z
    have hxEdge : x.1 ∈ K.faceCarrier (K.faceEdge t i).1 := by
      rw [← K.faceStandardEdge_map t i,
        ← K.faceReindexToStandard_mem_faceCarrier t s x]
      have heq : K.faceReindexToStandard t x = z := by
        change K.faceReindexHomeomorph t x = z
        exact (K.faceReindexHomeomorph t).apply_symm_apply z
      rw [heq]
      exact hz
    refine ⟨x, hxEdge, ?_⟩
    change (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure (K.faceReindexHomeomorph t x)).1 = p
    simpa [x] using hzp

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
