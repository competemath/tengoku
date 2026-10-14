/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteFaceFilling
public import Tengoku

/-!
# Cellwise assembly for locally finite PL face fillings

This file transports every polygonal Schoenflies filling back to its native abstract face.  A
single compatibility package records the three geometric facts needed for global assembly:
filled interiors are pairwise disjoint, the replacement graph misses every filled interior, and
the family of filled closed regions is locally finite.  Under these conditions the transported
maps form a genuine locally finite triangle complex in the plane.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

namespace FacePLFilling

/-- A standard-triangle filling transported back to the native simplex of its source face. -/
noncomputable def faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    K.ClosedFace f → Plane :=
  fun x ↦ F.map (K.facePlaneHomeomorph f x).1

/--
@isnad1 id=continuo.0h5v.s8.c6811dd33e89 from=translated src=- shape=98b0255e vocab=c20be7d3
-/
theorem continuous_faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Continuous F.faceMap := by
  have hF : Continuous (fun p : standardFaceRegion ↦ F.map p.1) :=
    continuousOn_iff_continuous_domRestrict.mp F.continuousOn
  exact hF.comp (K.facePlaneHomeomorph f).continuous

/--
@isnad1 id=injectiv.0h5v.s6.eb38519067a9 from=translated src=- shape=98b0255e vocab=eb7983b8
-/
theorem injective_faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Function.Injective F.faceMap := by
  intro x y hxy
  apply (K.facePlaneHomeomorph f).injective
  apply Subtype.ext
  exact F.injectiveOn (K.facePlaneHomeomorph f x).2
    (K.facePlaneHomeomorph f y).2 hxy

/--
@isnad1 id=eq.0h5v.s6.28992bcdf206 from=translated src=- shape=57384318 vocab=c0a0908b
-/
theorem range_faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Set.range F.faceMap = (K.facePolygonalCircle (G := G) f).closedRegion := by
  rw [← F.image_eq]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(K.facePlaneHomeomorph f x).1,
      (K.facePlaneHomeomorph f x).2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    let q : standardFaceRegion := ⟨p, hp⟩
    refine ⟨(K.facePlaneHomeomorph f).symm q, ?_⟩
    change F.map (K.facePlaneHomeomorph f
      ((K.facePlaneHomeomorph f).symm q)).1 = F.map p
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]

/-- The relative interior of a filled source face maps into the bounded complementary region
of its polygonal boundary.
@isnad1 id=mapsto.0h5v.s6.0493a855948f from=translated src=- shape=88deeba4 vocab=33a9f44a
-/
theorem mapsTo_interiorRegion {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Set.MapsTo F.map (interior standardFaceRegion)
      (K.facePolygonalCircle (G := G) f).interiorRegion := by
  intro p hp
  have hpRegion : p ∈ standardFaceRegion := interior_subset hp
  have hclosed : F.map p ∈
      (K.facePolygonalCircle (G := G) f).closedRegion := by
    rw [← F.image_eq]
    exact ⟨p, hpRegion, rfl⟩
  rw [(K.facePolygonalCircle (G := G) f).closedRegion_eq_union] at hclosed
  rcases hclosed with hbounded | hcarrier
  · exact hbounded
  · rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hcarrier
    obtain ⟨q, hq, hqmap⟩ := hcarrier
    have hmapEq : F.map p = F.map q := by
      rw [F.eqOn_boundary hq]
      exact hqmap.symm
    have hpq : p = q := F.injectiveOn hpRegion
      (standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hq) hmapEq
    subst q
    exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hp hq)

end FacePLFilling

/-! ## Boundary recognition from global barycentric coordinates -/

/--
@isnad1 id=ex.1h4v.s6.c90aea8d307b from=translated src=- shape=06ae727c vocab=45816a9f
-/
theorem exists_faceVertex_eq_of_mem (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) : ∃ i : ZMod 3, K.faceVertex f i = v := by
  let w : {w // w ∈ K.faceVertices f} := ⟨v, hv⟩
  let j : Fin 3 := (K.faceVertexEquiv f).symm w
  let i : ZMod 3 := ZMod.finEquiv 3 j
  refine ⟨i, ?_⟩
  change ((K.faceVertexEquiv f)
    ((ZMod.finEquiv 3).symm (ZMod.finEquiv 3 j))).1 = v
  rw [(ZMod.finEquiv 3).symm_apply_apply,
    (K.faceVertexEquiv f).apply_symm_apply]

/-- Every abstract edge contained in a maximal face is one of its three cyclic edges.
@isnad1 id=ex.1h4v.s6.1328c7c6a7f4 from=translated src=- shape=4af38cc5 vocab=04434327
-/
theorem exists_faceEdge_eq_of_subset (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) :
    ∃ i : ZMod 3, K.faceEdge f i = e := by
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem f (hef (K.edgeFirst_mem e))
  obtain ⟨j, hj⟩ := K.exists_faceVertex_eq_of_mem f (hef (K.edgeSecond_mem e))
  have hij : i ≠ j := by
    intro h
    apply K.edgeFirst_ne_edgeSecond e
    rw [← hi, ← hj, h]
  rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
    h | h | h
  · exact (hij h.symm).elim
  · subst j
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [K.faceEdge_val, K.edge_eq_pair, hi, hj]
  · subst j
    refine ⟨i + 2, ?_⟩
    apply Subtype.ext
    rw [K.faceEdge_val, K.edge_eq_pair]
    have hcycle : i + 2 + 1 = i :=
      (by decide : ∀ k : ZMod 3, k + 2 + 1 = k) i
    rw [hcycle]
    rw [hi, hj]
    ext v
    simp [or_comm]

/-- If equal global barycentric coordinates are represented on distinct vertex triples, the
standard coordinate on the first triangle lies on its frontier.
@isnad1 id=mem.2h6v.s10.435d5f9f3991 from=translated src=- shape=d939f29e vocab=11c10eb7
-/
theorem faceChart_mem_frontier_of_extended_eq
    {f g : K.Face} (hfg : K.faceVertices f ≠ K.faceVertices g)
    {x : K.ClosedFace f} {y : K.ClosedFace g}
    (hxy : extendFaceCoordinates (K.faceVertices f) x =
      extendFaceCoordinates (K.faceVertices g) y) :
    (K.facePlaneHomeomorph f x).1 ∈ frontier standardFaceRegion := by
  classical
  let inter := K.faceVertices f ∩ K.faceVertices g
  have hinterCard : inter.card ≤ 2 := by
    have hle : inter.card ≤ 3 := by
      calc
        inter.card ≤ (K.faceVertices f).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = 3 := K.faceVertices_card f
    by_contra hnot
    have hthree : inter.card = 3 := by omega
    have hleft : inter = K.faceVertices f :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [K.faceVertices_card f, hthree])
    have hright : inter = K.faceVertices g :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [K.faceVertices_card g, hthree])
    exact hfg (hleft.symm.trans hright)
  have hinterNonempty : inter.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hxzero : ∀ v : {v // v ∈ K.faceVertices f}, x v = 0 := by
      intro v
      have hvNotG : v.1 ∉ K.faceVertices g := by
        intro hvg
        have : v.1 ∈ inter := Finset.mem_inter.mpr ⟨v.2, hvg⟩
        rw [hempty] at this
        exact Finset.notMem_empty _ this
      have hc := congrFun hxy v.1
      rw [extendFaceCoordinates_of_mem (K.faceVertices f) x v.2,
        extendFaceCoordinates_of_notMem (K.faceVertices g) y hvNotG] at hc
      exact hc
    have hzero : (∑ v, x v) = 0 := by simp [hxzero]
    have hone : (∑ v, x v) = 1 := stdSimplex.sum_eq_one x
    rw [hzero] at hone
    norm_num at hone
  have htwo : 2 ≤ (K.faceVertices f).card := by
    rw [K.faceVertices_card f]
    omega
  obtain ⟨e, hinterE, hEf, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq Finset.inter_subset_left
      hinterCard htwo
  let E : K.Edge := ⟨e, hEcard, f, hEf⟩
  have hxSupported : ∀ v : {v // v ∈ K.faceVertices f},
      v.1 ∉ E.1 → x v = 0 := by
    intro v hvE
    have hvNotG : v.1 ∉ K.faceVertices g := by
      intro hvg
      exact hvE (hinterE (Finset.mem_inter.mpr ⟨v.2, hvg⟩))
    have hc := congrFun hxy v.1
    rw [extendFaceCoordinates_of_mem (K.faceVertices f) x v.2,
      extendFaceCoordinates_of_notMem (K.faceVertices g) y hvNotG] at hc
    exact hc
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset f E hEf
  have hxSide : x ∈ K.faceSide f i := by
    change ∀ v, v.1 ∉ (K.faceEdge f i).1 → x v = 0
    simpa only [hi] using hxSupported
  have hpSide : (K.facePlaneHomeomorph f x).1 ∈
      standardTriangleCircle.edgeSegment i := by
    rw [← K.facePlaneHomeomorph_image_edge f i]
    exact ⟨x, hxSide, rfl⟩
  have hpCarrier : (K.facePlaneHomeomorph f x).1 ∈
      standardTriangleCircle.carrier := Set.mem_iUnion.mpr ⟨i, hpSide⟩
  rw [standardTriangleCircle_carrier] at hpCarrier
  simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier

/-- Lifting the standard coordinate of a boundary point recovers its original ambient support
point.
@isnad1 id=eq.1h4v.s11.9ceae11048f5 from=translated src=- shape=c7ab0ce3 vocab=8f84f799
-/
theorem faceBoundaryLift_facePlaneHomeomorph (f : K.Face) (x : K.ClosedFace f)
    (hp : (K.facePlaneHomeomorph f x).1 ∈ frontier standardFaceRegion) :
    (K.faceBoundaryLift f
      ⟨(K.facePlaneHomeomorph f x).1, hp⟩).1 =
      faceToSupport (K := K) f x := by
  apply Subtype.ext
  change K.faceMap f
      ((K.facePlaneHomeomorph f).symm
        ⟨(K.facePlaneHomeomorph f x).1,
          standardFaceBoundary_mem_region
            ⟨(K.facePlaneHomeomorph f x).1, hp⟩⟩) = K.faceMap f x
  congr 1
  apply (K.facePlaneHomeomorph f).injective
  rw [(K.facePlaneHomeomorph f).apply_symm_apply]

/-! ## Global cellwise compatibility -/

/-- The geometric conditions under which the independently chosen polygonal face fillings
assemble to a locally finite plane complex.  The first field rules out duplicate maximal-face
labels; the remaining fields say that different filled cells meet only along the replacement
graph and remain locally finite. -/
structure CellwiseCompatibility (G : K.PlaneGraphRealization) : Prop where
  faceVertices_injective : Function.Injective K.faceVertices
  graphAvoidsInteriors : ∀ f : K.Face,
    Disjoint (Set.range G.graphReplacementMap)
      (K.facePolygonalCircle (G := G) f).interiorRegion
  interiorsDisjoint : ∀ f g : K.Face, f ≠ g →
    Disjoint (K.facePolygonalCircle (G := G) f).interiorRegion
      (K.facePolygonalCircle (G := G) g).interiorRegion
  closedRegions_mem_region : ∀ f : K.Face,
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region
  locallyFiniteClosedRegions : LocallyFinite fun f : K.Face ↦
    {q : G.region | q.1 ∈ (K.facePolygonalCircle (G := G) f).closedRegion}

namespace CellwiseCompatibility

/--
@isnad1 id=ne.2h5v.s5.2377173147ff from=translated src=- shape=28d42a07 vocab=4630ac7e
-/
theorem distinct_faceVertices (H : K.CellwiseCompatibility G)
    {f g : K.Face} (hfg : f ≠ g) :
    K.faceVertices f ≠ K.faceVertices g := by
  exact fun h ↦ hfg (CellwiseCompatibility.faceVertices_injective H h)

/-- The transported chosen fillings have exactly the same overlap relation as the original
abstract triangles.
@isnad1 id=iff.1h7v.s7.40c567596b38 from=translated src=- shape=2e9ab74d vocab=989a10d6
-/
theorem faceMap_eq_iff (H : K.CellwiseCompatibility G)
    {f g : K.Face} {x : K.ClosedFace f} {y : K.ClosedFace g} :
    (K.facePLFilling (G := G) f).faceMap x =
        (K.facePLFilling (G := G) g).faceMap y ↔
      extendFaceCoordinates (K.faceVertices f) x =
        extendFaceCoordinates (K.faceVertices g) y := by
  let F := K.facePLFilling (G := G) f
  let L := K.facePLFilling (G := G) g
  let p := K.facePlaneHomeomorph f x
  let q := K.facePlaneHomeomorph g y
  change F.map p.1 = L.map q.1 ↔ _
  constructor
  · intro hmap
    by_cases hfg : f = g
    · subst g
      have hxy : x = y := F.injective_faceMap hmap
      subst y
      rfl
    have hverts := distinct_faceVertices H hfg
    have hpNotInterior : p.1 ∉ interior standardFaceRegion := by
      intro hpInterior
      have hpFilled : F.map p.1 ∈
          (K.facePolygonalCircle (G := G) f).interiorRegion :=
        F.mapsTo_interiorRegion hpInterior
      by_cases hqInterior : q.1 ∈ interior standardFaceRegion
      · have hqFilled : L.map q.1 ∈
            (K.facePolygonalCircle (G := G) g).interiorRegion :=
          L.mapsTo_interiorRegion hqInterior
        exact Set.disjoint_left.mp (H.interiorsDisjoint f g hfg) hpFilled
          (hmap ▸ hqFilled)
      · have hqFrontier : q.1 ∈ frontier standardFaceRegion := by
          rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
          exact ⟨q.2, hqInterior⟩
        have hqGraph : L.map q.1 ∈ Set.range G.graphReplacementMap := by
          refine ⟨K.faceBoundaryLift g ⟨q.1, hqFrontier⟩, ?_⟩
          rw [L.eqOn_boundary hqFrontier,
            K.faceBoundaryMap_apply (G := G) g ⟨q.1, hqFrontier⟩]
        exact Set.disjoint_left.mp (H.graphAvoidsInteriors f) hqGraph
          (hmap ▸ hpFilled)
    have hqNotInterior : q.1 ∉ interior standardFaceRegion := by
      intro hqInterior
      have hqFilled : L.map q.1 ∈
          (K.facePolygonalCircle (G := G) g).interiorRegion :=
        L.mapsTo_interiorRegion hqInterior
      have hpFrontier : p.1 ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨p.2, hpNotInterior⟩
      have hpGraph : F.map p.1 ∈ Set.range G.graphReplacementMap := by
        refine ⟨K.faceBoundaryLift f ⟨p.1, hpFrontier⟩, ?_⟩
        rw [F.eqOn_boundary hpFrontier,
          K.faceBoundaryMap_apply (G := G) f ⟨p.1, hpFrontier⟩]
      exact Set.disjoint_left.mp (H.graphAvoidsInteriors g) hpGraph
        (hmap ▸ hqFilled)
    have hpFrontier : p.1 ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨p.2, hpNotInterior⟩
    have hqFrontier : q.1 ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨q.2, hqNotInterior⟩
    have hgraph :
        G.graphReplacementMap (K.faceBoundaryLift f ⟨p.1, hpFrontier⟩) =
          G.graphReplacementMap (K.faceBoundaryLift g ⟨q.1, hqFrontier⟩) := by
      rw [← K.faceBoundaryMap_apply (G := G) f ⟨p.1, hpFrontier⟩,
        ← K.faceBoundaryMap_apply (G := G) g ⟨q.1, hqFrontier⟩,
        ← F.eqOn_boundary hpFrontier, ← L.eqOn_boundary hqFrontier]
      exact hmap
    have hlift := G.graphReplacementMap_injective hgraph
    have hsupp : faceToSupport (K := K) f x = faceToSupport (K := K) g y := by
      calc
        faceToSupport (K := K) f x =
            (K.faceBoundaryLift f ⟨p.1, hpFrontier⟩).1 :=
          (K.faceBoundaryLift_facePlaneHomeomorph f x hpFrontier).symm
        _ = (K.faceBoundaryLift g ⟨q.1, hqFrontier⟩).1 :=
          congrArg Subtype.val hlift
        _ = faceToSupport (K := K) g y :=
          K.faceBoundaryLift_facePlaneHomeomorph g y hqFrontier
    exact K.faceMap_eq_iff.mp (congrArg Subtype.val hsupp)
  · intro hcoords
    by_cases hfg : f = g
    · subst g
      have hxy : x = y := K.faceMap_injective f (K.faceMap_eq_iff.mpr hcoords)
      subst y
      rfl
    have hpFrontier := K.faceChart_mem_frontier_of_extended_eq
      (distinct_faceVertices H hfg) hcoords
    have hqFrontier := K.faceChart_mem_frontier_of_extended_eq
      (distinct_faceVertices H (Ne.symm hfg)) hcoords.symm
    exact K.facePLFilling_eq_of_boundaryLift_eq
      (f := f) (g := g) (p := ⟨p.1, hpFrontier⟩) (q := ⟨q.1, hqFrontier⟩) (by
        apply Subtype.ext
        rw [K.faceBoundaryLift_facePlaneHomeomorph f x hpFrontier,
          K.faceBoundaryLift_facePlaneHomeomorph g y hqFrontier]
        exact Subtype.ext (K.faceMap_eq_iff.mpr hcoords))

end CellwiseCompatibility

/-! ## The assembled replacement complex -/

/-- Replace every face of a locally finite complex by its coherent polygonal Schoenflies
filling.  The abstract vertices and faces are unchanged. -/
noncomputable abbrev polygonalReplacementComplex (H : K.CellwiseCompatibility G) :
    LocallyFiniteTriangleComplex G.region where
  Vertex := K.Vertex
  Face := K.Face
  faceVertices := K.faceVertices
  faceVertices_card := K.faceVertices_card
  vertex_used := K.vertex_used
  faceMap f x := ⟨(K.facePLFilling (G := G) f).faceMap x,
    H.closedRegions_mem_region f <|
      (K.facePLFilling (G := G) f).range_faceMap ▸ Set.mem_range_self x⟩
  faceMap_continuous f := by
    apply Continuous.subtype_mk
    exact (K.facePLFilling (G := G) f).continuous_faceMap
  faceMap_eq_iff := by
    intro f g x y
    constructor
    · intro h
      exact (CellwiseCompatibility.faceMap_eq_iff H).mp
        (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (CellwiseCompatibility.faceMap_eq_iff H).mpr h
  locallyFinite := by
    convert H.locallyFiniteClosedRegions using 1
    funext f
    ext q
    constructor
    · rintro ⟨x, hx⟩
      change q.1 ∈ (K.facePolygonalCircle (G := G) f).closedRegion
      rw [← (K.facePLFilling (G := G) f).range_faceMap]
      exact ⟨x, congrArg Subtype.val hx⟩
    · intro hq
      rw [← (K.facePLFilling (G := G) f).range_faceMap] at hq
      obtain ⟨x, hx⟩ := hq
      exact ⟨x, Subtype.ext hx⟩

/--
@isnad1 id=eq.1h4v.s7.626432b018ce from=translated src=- shape=d24fd11a vocab=e45b2ceb
-/
@[simp] theorem polygonalReplacementComplex_faceVertices
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    (K.polygonalReplacementComplex H).faceVertices f = K.faceVertices f := rfl

/--
@isnad1 id=eq.1h5v.s7.e2e8aec8364b from=translated src=- shape=77937e9d vocab=7a70e0b9
-/
@[simp] theorem polygonalReplacementComplex_faceMap
    (H : K.CellwiseCompatibility G) (f : K.Face) (x : K.ClosedFace f) :
    ((K.polygonalReplacementComplex H).faceMap f x).1 =
      (K.facePLFilling (G := G) f).faceMap x := rfl

/--
@isnad1 id=eq.1h4v.s7.49739b231322 from=translated src=- shape=c7e63279 vocab=a990d049
-/
theorem polygonalReplacementComplex_faceCarrier
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    (K.polygonalReplacementComplex H).faceCarrier f =
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion} := by
  ext q
  constructor
  · rintro ⟨x, hx⟩
    change q.1 ∈ (K.facePolygonalCircle (G := G) f).closedRegion
    rw [← (K.facePLFilling (G := G) f).range_faceMap]
    exact ⟨x, congrArg Subtype.val hx⟩
  · intro hq
    rw [← (K.facePLFilling (G := G) f).range_faceMap] at hq
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, Subtype.ext hx⟩

/-! ## The canonical homeomorphism onto the replacement -/

/-- A chosen maximal face containing a point of the support. -/
noncomputable def supportFace (p : K.support) : K.Face :=
  Classical.choose (Set.mem_iUnion.mp p.2)

/--
@isnad1 id=mem.0h3v.s5.84a29d33b006 from=translated src=- shape=551dd433 vocab=c559e6da
-/
theorem mem_faceCarrier_supportFace (p : K.support) :
    p.1 ∈ K.faceCarrier (K.supportFace p) :=
  Classical.choose_spec (Set.mem_iUnion.mp p.2)

/-- Chosen barycentric coordinates for a support point in its chosen maximal face. -/
noncomputable def supportFacePoint (p : K.support) : K.ClosedFace (K.supportFace p) :=
  Classical.choose (K.mem_faceCarrier_supportFace p)

/--
@isnad1 id=eq.0h3v.s5.feac6d55e464 from=translated src=- shape=8cea890e vocab=a45815ab
-/
theorem faceMap_supportFacePoint (p : K.support) :
    K.faceMap (K.supportFace p) (K.supportFacePoint p) = p.1 :=
  Classical.choose_spec (K.mem_faceCarrier_supportFace p)

/--
@isnad1 id=eq.0h3v.s6.9098ac44c981 from=translated src=- shape=4c72e295 vocab=0a26bf20
-/
theorem faceInSupport_eq_preimage (f : K.Face) :
    faceInSupport (K := K) f =
      Subtype.val ⁻¹' K.faceCarrier f := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact Set.mem_range_self x
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hx

/--
@isnad1 id=locallyf.0h2v.s5.84cfe7f7be00 from=translated src=- shape=dc927cd9 vocab=572066a7
-/
theorem locallyFinite_faceInSupport :
    LocallyFinite (faceInSupport (K := K)) := by
  have h := K.locallyFinite.preimage_continuous
    (g := fun p : K.support ↦ p.1) continuous_subtype_val
  convert h using 1
  funext f
  exact K.faceInSupport_eq_preimage f

/-- The image of one source face, regarded as a subset of the permitted open plane region. -/
def PlaneGraphRealization.faceImageInRegion (G : K.PlaneGraphRealization)
    (f : K.Face) : Set G.region :=
  {q | q.1 ∈ G.map '' faceInSupport (K := K) f}

/-- Source faces remain locally finite after passing through a realization which is closed
relative to its perturbation region.
@isnad1 id=locallyf.0h3v.s6.1462354b0599 from=translated src=- shape=a595d37e vocab=cfd22775
-/
theorem PlaneGraphRealization.locallyFinite_faceImagesInRegion
    (G : K.PlaneGraphRealization) :
    LocallyFinite G.faceImageInRegion := by
  let mapInRegion : K.support → G.region := fun p ↦ ⟨G.map p, G.map_mem_region p⟩
  have hEmbedding : _root_.Topology.IsEmbedding mapInRegion :=
    G.isEmbedding.codRestrict G.region G.map_mem_region
  have hlocal : LocallyFinite fun f : K.Face ↦
      mapInRegion '' faceInSupport (K := K) f :=
    PlaneGraphRealization.locallyFinite_image_isEmbedding_of_isClosed_range
      K.locallyFinite_faceInSupport hEmbedding G.mapClosedInRegion
  have heq : (fun f : K.Face ↦ mapInRegion '' faceInSupport (K := K) f) =
      G.faceImageInRegion := by
    funext f
    ext q
    constructor
    · rintro ⟨p, hp, hpq⟩
      exact ⟨p, hp, congrArg Subtype.val hpq⟩
    · rintro ⟨p, hp, hpq⟩
      refine ⟨p, hp, ?_⟩
      apply Subtype.ext
      exact hpq
  rwa [← heq]

/--
@isnad1 id=eq.0h2v.s5.d8725b4a063a from=translated src=- shape=8f49c85c vocab=d38a2c20
-/
theorem iUnion_faceInSupport :
    (⋃ f : K.Face, faceInSupport (K := K) f) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  apply Set.mem_iUnion.mpr
  refine ⟨K.supportFace p, K.supportFacePoint p, ?_⟩
  apply Subtype.ext
  exact K.faceMap_supportFacePoint p

/--
@isnad1 id=isembedd.0h3v.s9.d3800d66bdb5 from=translated src=- shape=4271e8a0 vocab=9002be56
-/
theorem isEmbedding_faceToSupport [T2Space S] (f : K.Face) :
    _root_.Topology.IsEmbedding (faceToSupport (K := K) f) :=
  (K.isEmbedding_faceMap f).codRestrict K.support
    (fun x ↦ Set.mem_iUnion.mpr ⟨f, Set.mem_range_self x⟩)

/-- A closed abstract face is homeomorphic to its carrier inside the whole support. -/
noncomputable def faceToSupportHomeomorph [T2Space S] (f : K.Face) :
    K.ClosedFace f ≃ₜ faceInSupport (K := K) f :=
  (K.isEmbedding_faceToSupport f).toHomeomorph

/--
@isnad1 id=eq.0h4v.s10.df23258efb69 from=translated src=- shape=0afb7cb5 vocab=97b0e576
-/
@[simp] theorem faceToSupportHomeomorph_apply [T2Space S]
    (f : K.Face) (x : K.ClosedFace f) :
    (K.faceToSupportHomeomorph f x).1 = faceToSupport (K := K) f x := rfl

variable [T2Space S]

/-- The coherent cellwise filling as a map into the support of the assembled plane complex. -/
noncomputable def polygonalReplacementMap (H : K.CellwiseCompatibility G) :
    K.support → (K.polygonalReplacementComplex H).support :=
  fun p ↦ ⟨⟨(K.facePLFilling (G := G) (K.supportFace p)).faceMap
      (K.supportFacePoint p), H.closedRegions_mem_region (K.supportFace p) <|
        (K.facePLFilling (G := G) (K.supportFace p)).range_faceMap ▸
          Set.mem_range_self (K.supportFacePoint p)⟩,
    Set.mem_iUnion.mpr ⟨K.supportFace p,
      Set.mem_range_self (K.supportFacePoint p)⟩⟩

omit [T2Space S] in
/-- On every named source face, the global replacement map is the chosen face filling.
@isnad1 id=eq.1h5v.s7.cf7212e725aa from=translated src=- shape=3635b283 vocab=cb2e3a0e
-/
theorem polygonalReplacementMap_faceToSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) (x : K.ClosedFace f) :
    K.polygonalReplacementMap H (faceToSupport (K := K) f x) =
      faceToSupport (K := K.polygonalReplacementComplex H) f x := by
  apply Subtype.ext
  apply Subtype.ext
  change (K.facePLFilling (G := G)
      (K.supportFace (faceToSupport (K := K) f x))).faceMap
        (K.supportFacePoint (faceToSupport (K := K) f x)) =
    (K.facePLFilling (G := G) f).faceMap x
  apply (CellwiseCompatibility.faceMap_eq_iff H).mpr
  apply K.faceMap_eq_iff.mp
  rw [K.faceMap_supportFacePoint]
  rfl

/-- The source face formula, expressed on a carrier subtype. -/
noncomputable def polygonalReplacementMapOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    faceInSupport (K := K) f → (K.polygonalReplacementComplex H).support :=
  fun p ↦ faceToSupport (K := K.polygonalReplacementComplex H) f
    ((K.faceToSupportHomeomorph f).symm p)

/--
@isnad1 id=continuo.1h4v.s8.4386dffef81a from=translated src=- shape=12178803 vocab=88a623b8
-/
theorem continuous_polygonalReplacementMapOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    Continuous (K.polygonalReplacementMapOnFace H f) := by
  exact (continuous_faceToSupport
    (K := K.polygonalReplacementComplex H) f).comp
      (K.faceToSupportHomeomorph f).symm.continuous

/--
@isnad1 id=eq.1h5v.s7.02462b88065b from=translated src=- shape=6745a4fe vocab=1dbb6828
-/
theorem polygonalReplacementMap_eqOn_faceInSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    ∀ p : faceInSupport (K := K) f,
      K.polygonalReplacementMap H p.1 =
        K.polygonalReplacementMapOnFace H f p := by
  rintro ⟨p, x, rfl⟩
  rw [K.polygonalReplacementMap_faceToSupport H f x]
  congr 1
  exact (K.faceToSupportHomeomorph f).symm_apply_apply x |>.symm

/--
@isnad1 id=continuo.1h3v.s8.3a109793c434 from=translated src=- shape=5086703d vocab=2a2e2e02
-/
theorem continuous_polygonalReplacementMap (H : K.CellwiseCompatibility G) :
    Continuous (K.polygonalReplacementMap H) := by
  apply K.locallyFinite_faceInSupport.continuous K.iUnion_faceInSupport
  · intro f
    exact (isCompact_faceInSupport (K := K) f).isClosed
  · intro f
    rw [continuousOn_iff_continuous_domRestrict]
    convert K.continuous_polygonalReplacementMapOnFace H f using 1
    funext p
    exact K.polygonalReplacementMap_eqOn_faceInSupport H f p

/-- Read the old face map in coordinates chosen from a point of the replacement support. -/
noncomputable def polygonalReplacementInverse (H : K.CellwiseCompatibility G) :
    (K.polygonalReplacementComplex H).support → K.support :=
  fun p ↦ faceToSupport (K := K)
    ((K.polygonalReplacementComplex H).supportFace p)
    ((K.polygonalReplacementComplex H).supportFacePoint p)

omit [T2Space S] in
/-- On every replacement face, the inverse is the original face parametrization.
@isnad1 id=eq.1h5v.s7.63671d5f74df from=translated src=- shape=e38c5400 vocab=f81d8ab8
-/
theorem polygonalReplacementInverse_faceToSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) (x : K.ClosedFace f) :
    K.polygonalReplacementInverse H
        (faceToSupport (K := K.polygonalReplacementComplex H) f x) =
      faceToSupport (K := K) f x := by
  let L := K.polygonalReplacementComplex H
  let p : L.support := faceToSupport (K := L) f x
  let g := L.supportFace p
  let y := L.supportFacePoint p
  apply Subtype.ext
  change K.faceMap g y = K.faceMap f x
  apply K.faceMap_eq_iff.mpr
  apply L.faceMap_eq_iff.mp
  calc
    L.faceMap g y = p.1 := L.faceMap_supportFacePoint p
    _ = L.faceMap f x := rfl

/-- The inverse face formula on one replacement carrier. -/
noncomputable def polygonalReplacementInverseOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    faceInSupport (K := K.polygonalReplacementComplex H) f → K.support :=
  fun p ↦ faceToSupport (K := K) f
    (((K.polygonalReplacementComplex H).faceToSupportHomeomorph f).symm p)

omit [T2Space S] in
/--
@isnad1 id=continuo.1h4v.s9.b0acc7603aa7 from=translated src=- shape=66100aee vocab=6eba5264
-/
theorem continuous_polygonalReplacementInverseOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    Continuous (K.polygonalReplacementInverseOnFace H f) := by
  exact (continuous_faceToSupport (K := K) f).comp
    ((K.polygonalReplacementComplex H).faceToSupportHomeomorph f).symm.continuous

omit [T2Space S] in
/--
@isnad1 id=eq.1h5v.s9.47a0c2a9095d from=translated src=- shape=8a63823f vocab=faa27801
-/
theorem polygonalReplacementInverse_eqOn_faceInSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    ∀ p : faceInSupport (K := K.polygonalReplacementComplex H) f,
      K.polygonalReplacementInverse H p.1 =
        K.polygonalReplacementInverseOnFace H f p := by
  rintro ⟨p, x, rfl⟩
  rw [K.polygonalReplacementInverse_faceToSupport H f x]
  congr 1
  exact ((K.polygonalReplacementComplex H).faceToSupportHomeomorph f).symm_apply_apply x |>.symm

omit [T2Space S] in
/--
@isnad1 id=continuo.1h3v.s8.49f67f0e034e from=translated src=- shape=60280039 vocab=a3acd449
-/
theorem continuous_polygonalReplacementInverse (H : K.CellwiseCompatibility G) :
    Continuous (K.polygonalReplacementInverse H) := by
  let L := K.polygonalReplacementComplex H
  apply L.locallyFinite_faceInSupport.continuous L.iUnion_faceInSupport
  · intro f
    exact (isCompact_faceInSupport (K := L) f).isClosed
  · intro f
    rw [continuousOn_iff_continuous_domRestrict]
    convert K.continuous_polygonalReplacementInverseOnFace H f using 1
    funext p
    exact K.polygonalReplacementInverse_eqOn_faceInSupport H f p

omit [T2Space S] in
/--
@isnad1 id=eq.1h4v.s5.798dcac465f0 from=translated src=- shape=2d3820f6 vocab=86aee57b
-/
theorem polygonalReplacementInverse_apply_map
    (H : K.CellwiseCompatibility G) (p : K.support) :
    K.polygonalReplacementInverse H (K.polygonalReplacementMap H p) = p := by
  let f := K.supportFace p
  let x := K.supportFacePoint p
  have hpresentation : faceToSupport (K := K) f x = p := by
    apply Subtype.ext
    exact K.faceMap_supportFacePoint p
  rw [← hpresentation, K.polygonalReplacementMap_faceToSupport H f x,
    K.polygonalReplacementInverse_faceToSupport H f x]

omit [T2Space S] in
/--
@isnad1 id=eq.1h4v.s7.cf6ac0a8f18c from=translated src=- shape=8c05f2a3 vocab=482d752a
-/
theorem polygonalReplacementMap_apply_inverse
    (H : K.CellwiseCompatibility G)
    (p : (K.polygonalReplacementComplex H).support) :
    K.polygonalReplacementMap H (K.polygonalReplacementInverse H p) = p := by
  let L := K.polygonalReplacementComplex H
  let f := L.supportFace p
  let x := L.supportFacePoint p
  have hpresentation : faceToSupport (K := L) f x = p := by
    apply Subtype.ext
    exact L.faceMap_supportFacePoint p
  rw [← hpresentation, K.polygonalReplacementInverse_faceToSupport H f x,
    K.polygonalReplacementMap_faceToSupport H f x]

/-- The source support and its coherent polygonal replacement are canonically homeomorphic. -/
noncomputable def polygonalReplacementHomeomorph (H : K.CellwiseCompatibility G) :
    K.support ≃ₜ (K.polygonalReplacementComplex H).support where
  toFun := K.polygonalReplacementMap H
  invFun := K.polygonalReplacementInverse H
  left_inv := K.polygonalReplacementInverse_apply_map H
  right_inv := K.polygonalReplacementMap_apply_inverse H
  continuous_toFun := K.continuous_polygonalReplacementMap H
  continuous_invFun := K.continuous_polygonalReplacementInverse H

/-- The canonical replacement homeomorphism preserves every named closed face exactly.  This
is stronger than preservation of the total support and is the bridge used when a finite family
of replacement faces is pulled back to a finite source subcomplex.
@isnad1 id=iff.1h5v.s10.39e4d3546390 from=translated src=- shape=c9937356 vocab=03e01e32
-/
theorem polygonalReplacementHomeomorph_mem_faceCarrier_iff
    (H : K.CellwiseCompatibility G) (f : K.Face) (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1 ∈
        (K.polygonalReplacementComplex H).faceCarrier f ↔
      p.1 ∈ K.faceCarrier f := by
  constructor
  · rintro ⟨x, hx⟩
    have htarget :
        faceToSupport (K := K.polygonalReplacementComplex H) f x =
          K.polygonalReplacementHomeomorph H p :=
      Subtype.ext hx
    have hsource :
        (K.polygonalReplacementHomeomorph H).symm
            (faceToSupport (K := K.polygonalReplacementComplex H) f x) = p := by
      rw [htarget, (K.polygonalReplacementHomeomorph H).symm_apply_apply]
    change K.polygonalReplacementInverse H
        (faceToSupport (K := K.polygonalReplacementComplex H) f x) = p at hsource
    rw [K.polygonalReplacementInverse_faceToSupport H f x] at hsource
    exact ⟨x, congrArg Subtype.val hsource⟩
  · rintro ⟨x, hx⟩
    have hsource : faceToSupport (K := K) f x = p := Subtype.ext hx
    have hmap := K.polygonalReplacementMap_faceToSupport H f x
    change K.polygonalReplacementHomeomorph H
        (faceToSupport (K := K) f x) =
          faceToSupport (K := K.polygonalReplacementComplex H) f x at hmap
    rw [hsource] at hmap
    exact ⟨x, (congrArg Subtype.val hmap).symm⟩

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
