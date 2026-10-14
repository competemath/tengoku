/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.ChartInductionCore
import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.FineSubdivision
import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.IntrinsicMarkedFan
public import Tengoku

/-!
# The Radó crossing weld and chart induction

This file completes the chart-induction framework developed in `ChartInductionCore`. It constructs
the crossing weld, packages the one-chart induction step, and assembles the final triangulation.
-/

@[expose] public section

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

open PartialTriangulation.PolygonalReplacementSourceAtlas
open PartialTriangulation.RelativeSynchronizedTarget

private theorem extendFaceCoordinates_vertex {V : Type*} [DecidableEq V]
    (F : Finset V) (v : {v // v ∈ F}) :
    extendFaceCoordinates F (stdSimplex.vertex v) = Pi.single v.1 1 := by
  funext w
  by_cases hwv : w = v.1
  · subst w
    simp [extendFaceCoordinates, v.2]
  · by_cases hw : w ∈ F
    · have hsub : (⟨w, hw⟩ : {w // w ∈ F}) ≠ v :=
        fun h ↦ hwv (congrArg Subtype.val h)
      simp [extendFaceCoordinates, hw, hwv, hsub]
    · simp [extendFaceCoordinates, hw, hwv]

private def simplexLineMap {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) (r : Set.Icc (0 : ℝ) 1) : stdSimplex ℝ V :=
  ⟨AffineMap.lineMap x.1 y.1 r.1,
    (convex_stdSimplex ℝ V).lineMap_mem x.2 y.2 r.2⟩

private theorem extendFaceCoordinates_simplexLineMap {V : Type*} [DecidableEq V]
    (F : Finset V) (x y : stdSimplex ℝ {v // v ∈ F}) (r : Set.Icc (0 : ℝ) 1) :
    extendFaceCoordinates F (simplexLineMap x y r) =
      (1 - r.1) • extendFaceCoordinates F x + r.1 • extendFaceCoordinates F y := by
  funext v
  by_cases hv : v ∈ F
  · rw [extendFaceCoordinates_of_mem _ _ hv]
    simp only [simplexLineMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [extendFaceCoordinates_of_mem _ _ hv, extendFaceCoordinates_of_mem _ _ hv]
    change
      (AffineMap.lineMap x.1 y.1 r.1) ⟨v, hv⟩ =
        (1 - r.1) * x ⟨v, hv⟩ + r.1 * y ⟨v, hv⟩
    rw [AffineMap.lineMap_apply_module]
    rfl
  · rw [extendFaceCoordinates_of_notMem _ _ hv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [extendFaceCoordinates_of_notMem _ _ hv, extendFaceCoordinates_of_notMem _ _ hv]
    simp

private theorem extendFaceCoordinates_simplexLineMap_vertices_eq
    {V : Type*} [DecidableEq V] (F G : Finset V)
    (a b : {v // v ∈ F}) (c d : {v // v ∈ G})
    (hac : a.1 = c.1) (hbd : b.1 = d.1) (r : Set.Icc (0 : ℝ) 1) :
    extendFaceCoordinates F
        (simplexLineMap (stdSimplex.vertex a) (stdSimplex.vertex b) r) =
      extendFaceCoordinates G
        (simplexLineMap (stdSimplex.vertex c) (stdSimplex.vertex d) r) := by
  rw [extendFaceCoordinates_simplexLineMap, extendFaceCoordinates_simplexLineMap,
    extendFaceCoordinates_vertex, extendFaceCoordinates_vertex,
    extendFaceCoordinates_vertex, extendFaceCoordinates_vertex, hac, hbd]

private theorem map_simplexLineMap_vertices {V W : Type*} [Fintype V] [DecidableEq V]
    (map : stdSimplex ℝ V → W → ℝ) (point : V → W → ℝ)
    (hline : ∀ (x y : stdSimplex ℝ V) (r : Set.Icc (0 : ℝ) 1),
      map (simplexLineMap x y r) = AffineMap.lineMap (map x) (map y) r.1)
    (hvertex : ∀ v, map (stdSimplex.vertex v) = point v)
    (a b : V) (r : Set.Icc (0 : ℝ) 1) :
    map (simplexLineMap (stdSimplex.vertex a) (stdSimplex.vertex b) r) =
      AffineMap.lineMap (point a) (point b) r.1 := by
  rw [hline, hvertex, hvertex]

private theorem mem_faceCarrier_of_val_eq_lineMap {K : IntrinsicTwoComplex}
    (s : Finset K.Vertex) (p₀ p₁ q : K.realization) (r : ℝ)
    (hp₀ : p₀ ∈ K.faceCarrier s) (hp₁ : p₁ ∈ K.faceCarrier s)
    (hq : q.1 = AffineMap.lineMap p₀.1 p₁.1 r) :
    q ∈ K.faceCarrier s := by
  intro k hk
  rw [hq]
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hp₀ k hk, hp₁ k hk]
  ring

private theorem edgeParameterValue_eq_lineMap {K : IntrinsicTwoComplex}
    (M : K.EdgeMarking) (e : K.Edge) (p₀ p₁ q : K.realization) (r : ℝ)
    (hp₀ : p₀ ∈ K.faceCarrier e.1) (hp₁ : p₁ ∈ K.faceCarrier e.1)
    (hq : q.1 = AffineMap.lineMap p₀.1 p₁.1 r) :
    M.edgeParameterValue e q =
      (1 - r) * M.edgeParameterValue e p₀ + r * M.edgeParameterValue e p₁ := by
  have hqEdge := mem_faceCarrier_of_val_eq_lineMap e.1 p₀ p₁ q r hp₀ hp₁ hq
  rw [M.edgeParameterValue_eq e hqEdge,
    M.edgeParameterValue_eq e hp₀, M.edgeParameterValue_eq e hp₁,
    K.edgeParameter_eq_secondCoordinate e q hqEdge,
    K.edgeParameter_eq_secondCoordinate e p₀ hp₀,
    K.edgeParameter_eq_secondCoordinate e p₁ hp₁,
    hq, AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem coordinates_eq_of_comparison
    {X Y P C : Type*} (mapX : X → P) (mapY : Y → P)
    (coordinatesX : X → C) (coordinatesY : Y → C)
    (mapX_eq : ∀ {x x'}, mapX x = mapX x' → coordinatesX x = coordinatesX x')
    (mapY_eq : ∀ {y y'}, mapY y = mapY y' → coordinatesY y = coordinatesY y')
    (map_eq_of_coordinates :
      ∀ {x y}, coordinatesX x = coordinatesY y → mapX x = mapY y)
    {x x' : X} {y y' : Y}
    (hxy : mapX x = mapY y)
    (hcomparison : coordinatesX x' = coordinatesY y')
    (hy : mapY y' = mapY y) :
    coordinatesX x = coordinatesY y := by
  have hyCoordinates := mapY_eq hy
  have hcomparisonMap := map_eq_of_coordinates hcomparison
  have hx := mapX_eq (hxy.trans (hy.symm.trans hcomparisonMap.symm))
  exact hx.trans (hcomparison.trans hyCoordinates)

/-- An affine subdivision carries a source face map back to the barycentric combination of the
lifts of its vertices.  This isolates the finite-dimensional affine calculation from the chart
construction that supplies the source map. -/
private theorem subdivision_preimage_faceMap_eq_vertex_sum
    {K L : IntrinsicTwoComplex} (R : K.Subdivision)
    (source : L.realization → K.realization)
    (lift : L.UsedVertex → R.refined.realization)
    (parent : L.Face → R.refined.Face)
    (hlift : ∀ u, R.homeo (lift u) = source (L.vertexPoint u))
    (hliftFace : ∀ (t : L.Face) (v : {v // v ∈ t.1}),
      lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ R.refined.faceCarrier (parent t).1)
    (hface : ∀ (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1}),
      R.homeo.symm (source (L.faceStandardMap t x)) ∈
        R.refined.faceCarrier (parent t).1)
    (hsourceSum : ∀ (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1}),
      (source (L.faceStandardMap t x)).1 =
        ∑ v : {v // v ∈ t.1}, x v •
          (source (L.vertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1)
    (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1}) :
    (R.homeo.symm (source (L.faceStandardMap t x))).1 =
      ∑ v : {v // v ∈ t.1}, x v •
        (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 := by
  classical
  let xg : L.realization := L.faceStandardMap t x
  let s := parent t
  let y : R.refined.realization := R.homeo.symm (source xg)
  have hyFace : y ∈ R.refined.faceCarrier s.1 := hface t x
  let point : {v // v ∈ t.1} → (R.refined.Vertex → ℝ) :=
    fun v ↦ (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1
  let weight : {v // v ∈ t.1} → ℝ := fun v ↦ x v
  have hweight : ∑ v, weight v = 1 := x.2.2
  let zfun : R.refined.Vertex → ℝ :=
    (Finset.univ : Finset {v // v ∈ t.1}).affineCombination ℝ point weight
  have hzlinear : zfun = ∑ v, weight v • point v :=
    Finset.affineCombination_eq_linear_combination Finset.univ point weight hweight
  have hznonneg : ∀ k, 0 ≤ zfun k := by
    intro k
    rw [hzlinear]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (x.2.1 v)
      ((lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.1 k)
  have hzsum : ∑ k, zfun k = 1 := by
    rw [hzlinear]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc
      (∑ v, ∑ k, weight v * (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) =
          ∑ v, weight v * ∑ k, (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
      _ = ∑ v, weight v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [(lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.2, mul_one]
      _ = 1 := hweight
  have hzsupport : ∀ k ∉ s.1, zfun k = 0 := by
    intro k hk
    rw [hzlinear]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro v _
    change weight v • (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k = 0
    rw [(hliftFace t v) k hk, smul_zero]
  let z : R.refined.realization :=
    ⟨zfun, ⟨hznonneg, hzsum⟩, ⟨s.1, s.2, hzsupport⟩⟩
  obtain ⟨b, hb⟩ := R.affineOnFace s.1 s.2
  have hbz : (R.homeo z).1 = b z.1 := hb z hzsupport
  have hbcomb : b zfun =
      (Finset.univ : Finset {v // v ∈ t.1}).affineCombination ℝ
        (b ∘ point) weight :=
    (Finset.univ : Finset {v // v ∈ t.1}).map_affineCombination
      point weight hweight b
  have hvertex (v : {v // v ∈ t.1}) :
      b (point v) = (source (L.vertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
    have hbv := hb (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) (hliftFace t v)
    rw [← hbv]
    exact congrArg Subtype.val (hlift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)
  have hzsource : (R.homeo z).1 = (source xg).1 := by
    rw [hbz, hbcomb,
      Finset.affineCombination_eq_linear_combination
        Finset.univ (b ∘ point) weight hweight]
    simp only [Function.comp_apply]
    calc
      ∑ v, weight v • b (point v) =
          ∑ v, x v •
            (source (L.vertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hvertex v]
      _ = (source (L.faceStandardMap t x)).1 := (hsourceSum t x).symm
  have hyz : y = z := by
    apply R.homeo.injective
    apply Subtype.ext
    rw [R.homeo.apply_symm_apply]
    exact hzsource.symm
  change y.1 = _
  rw [hyz]
  exact hzlinear

private theorem mem_map_univ {V W : Type*} [Fintype V]
    (e : V ↪ W) (v : V) : e v ∈ (Finset.univ : Finset V).map e :=
  Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩

private theorem mem_finset_map {V W : Type*}
    (e : V ↪ W) (F : Finset V) {v : V} (hv : v ∈ F) : e v ∈ F.map e :=
  Finset.mem_map.mpr ⟨v, hv, rfl⟩

private theorem fanVertexEmbedding_mem_globalFanFaceVertices
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace)
    (v : {p // p ∈ M.fanFaceVertices f}) :
    M.fanVertexEmbedding f v ∈ M.globalFanFaceVertices f :=
  (M.mem_globalFanFaceVertices_iff f _).mpr v.2

private theorem fanFirstVertexEmbedding_mem_globalFanFaceVertices
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace) :
    M.fanVertexEmbedding f (M.fanFirstVertex f) ∈ M.globalFanFaceVertices f :=
  fanVertexEmbedding_mem_globalFanFaceVertices M f (M.fanFirstVertex f)

private theorem fanSecondVertexEmbedding_mem_globalFanFaceVertices
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace) :
    M.fanVertexEmbedding f (M.fanSecondVertex f) ∈ M.globalFanFaceVertices f :=
  fanVertexEmbedding_mem_globalFanFaceVertices M f (M.fanSecondVertex f)

/-- The vertices of an old complex which are not identified with a local target vertex. -/
private abbrev OldVertexComplement {Local Old : Type*} (localToOld : Local ↪ Old) :=
  {v : Old // ¬ ∃ u : Local, localToOld u = v}

/-- A common vertex type obtained by replacing the local part of `Old` by `Target`. -/
private abbrev AmalgamatedVertex {Local Old : Type*} (localToOld : Local ↪ Old)
    (Target : Type*) :=
  Sum (OldVertexComplement localToOld) Target

private noncomputable def oldToAmalgamatedFun {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) :
    Old → AmalgamatedVertex localToOld Target := by
  classical
  exact fun v ↦ if hv : ∃ u : Local, localToOld u = v then
      Sum.inr (localToTarget (Classical.choose hv))
    else
      Sum.inl ⟨v, hv⟩

private theorem oldToAmalgamatedFun_injective {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) :
    Function.Injective (oldToAmalgamatedFun localToOld localToTarget) := by
  intro v w hvw
  by_cases hv : ∃ u : Local, localToOld u = v
  · by_cases hw : ∃ u : Local, localToOld u = w
    · have htarget :
          localToTarget (Classical.choose hv) =
            localToTarget (Classical.choose hw) := by
        have hs :
            (Sum.inr (localToTarget (Classical.choose hv)) :
                AmalgamatedVertex localToOld Target) =
              Sum.inr (localToTarget (Classical.choose hw)) := by
          simpa only [oldToAmalgamatedFun, dite_eq_left hv, dite_eq_left hw] using hvw
        exact Sum.inr_injective (show
          (Sum.inr (localToTarget (Classical.choose hv)) :
              OldVertexComplement localToOld ⊕ Target) =
            Sum.inr (localToTarget (Classical.choose hw)) from
          hs)
      have hlocal : Classical.choose hv = Classical.choose hw :=
        localToTarget.injective htarget
      calc
        v = localToOld (Classical.choose hv) := (Classical.choose_spec hv).symm
        _ = localToOld (Classical.choose hw) := congrArg localToOld hlocal
        _ = w := Classical.choose_spec hw
    · exfalso
      simp only [oldToAmalgamatedFun, dite_eq_left hv, dite_eq_right hw, reduceCtorEq] at hvw
  · by_cases hw : ∃ u : Local, localToOld u = w
    · exfalso
      simp only [oldToAmalgamatedFun, dite_eq_right hv, dite_eq_left hw, reduceCtorEq] at hvw
    · have hextra :
          (⟨v, hv⟩ : OldVertexComplement localToOld) = ⟨w, hw⟩ := by
        have hs :
            (Sum.inl (⟨v, hv⟩ : OldVertexComplement localToOld) :
                AmalgamatedVertex localToOld Target) =
              Sum.inl ⟨w, hw⟩ := by
          simpa only [oldToAmalgamatedFun, dite_eq_right hv, dite_eq_right hw] using hvw
        exact Sum.inl_injective (show
          (Sum.inl (⟨v, hv⟩ : OldVertexComplement localToOld) :
              OldVertexComplement localToOld ⊕ Target) =
            Sum.inl ⟨w, hw⟩ from hs)
      exact congrArg Subtype.val hextra

private noncomputable def oldToAmalgamated {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) :
    Old ↪ AmalgamatedVertex localToOld Target :=
  ⟨oldToAmalgamatedFun localToOld localToTarget,
    oldToAmalgamatedFun_injective localToOld localToTarget⟩

private def targetToAmalgamated {Local Old Target : Type*}
    (localToOld : Local ↪ Old) : Target ↪ AmalgamatedVertex localToOld Target :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- The chart-independent data used to glue a finite local complex to the marked fans in an
ambient intrinsic complex.  Keeping this data in one object prevents the compatibility proof from
inheriting the much larger chart-straightening telescope. -/
private structure MixedLocalFanData where
  ambient : IntrinsicTwoComplex
  localComplex : IntrinsicTwoComplex
  marking : ambient.EdgeMarking
  isOutside : marking.FanFace → Prop
  isOutside_decidable : DecidablePred isOutside
  localVertexPoint : localComplex.UsedVertex → ambient.realization
  localVertexPoint_injective : Function.Injective localVertexPoint
  localFaceMap : (t : localComplex.Face) →
    stdSimplex ℝ {v // v ∈ t.1} → ambient.realization

private abbrev MixedLocalFanData.OutsideFanFace (M : MixedLocalFanData) :=
  {f : M.marking.FanFace // M.isOutside f}

private instance MixedLocalFanData.instDecidablePredIsOutside (M : MixedLocalFanData) :
    DecidablePred M.isOutside := M.isOutside_decidable

private noncomputable abbrev MixedLocalFanData.oldVertexPoints (M : MixedLocalFanData) :
    Finset M.ambient.realization :=
  (Finset.univ : Finset M.localComplex.UsedVertex).image M.localVertexPoint ∪
    M.marking.fanVertices

private abbrev MixedLocalFanData.OldVertex (M : MixedLocalFanData) :=
  {p : M.ambient.realization // p ∈ M.oldVertexPoints}

private noncomputable abbrev MixedLocalFanData.localOldVertexEmbedding (M : MixedLocalFanData) :
    M.localComplex.UsedVertex ↪ M.OldVertex :=
  { toFun := fun v ↦ ⟨M.localVertexPoint v, by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
    inj' := fun _ _ h ↦ M.localVertexPoint_injective
      (congrArg (fun z : M.OldVertex ↦ z.1) h) }

private noncomputable abbrev MixedLocalFanData.fanOldVertexEmbedding (M : MixedLocalFanData) :
    M.marking.FanVertex ↪ M.OldVertex :=
  { toFun := fun v ↦ ⟨v.1, Finset.mem_union_right _ v.2⟩
    inj' := fun _ _ h ↦ Subtype.ext
      (congrArg (fun z : M.OldVertex ↦ z.1) h) }

private noncomputable abbrev MixedLocalFanData.localFaceOldVertexEmbedding
    (M : MixedLocalFanData) (t : M.localComplex.Face) : {v // v ∈ t.1} ↪ M.OldVertex :=
  { toFun := fun v ↦ M.localOldVertexEmbedding ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
    inj' := by
      intro v w hvw
      apply Subtype.ext
      have hp :
          M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ =
            M.localVertexPoint ⟨w.1, ⟨t.1, t.2, w.2⟩⟩ :=
        congrArg (fun z : M.OldVertex ↦ z.1) hvw
      exact congrArg (fun z : M.localComplex.UsedVertex ↦ z.1)
        (M.localVertexPoint_injective hp) }

private abbrev MixedLocalFanData.MixedOldFace (M : MixedLocalFanData) :=
  Sum M.localComplex.Face M.OutsideFanFace

private noncomputable abbrev MixedLocalFanData.mixedOldFaceVertices
    (M : MixedLocalFanData) : M.MixedOldFace → Finset M.OldVertex
  | Sum.inl t =>
      (Finset.univ : Finset {v // v ∈ t.1}).map (M.localFaceOldVertexEmbedding t)
  | Sum.inr f =>
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding

private noncomputable abbrev MixedLocalFanData.mixedOldFaceMap
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f} → M.ambient.realization :=
  match f with
  | Sum.inl t => fun x ↦
      M.localFaceMap t (relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x)
  | Sum.inr f => fun x ↦
      M.marking.globalFanFaceMap f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) x)

/-- The map laws shared by the construction and the full compatibility certificate. -/
private structure MixedMapCertificate (M : MixedLocalFanData) where
  mixedOldFaceVertices_card : ∀ f : M.MixedOldFace, (M.mixedOldFaceVertices f).card = 3
  continuous_mixedOldFaceMap : ∀ f : M.MixedOldFace, Continuous (M.mixedOldFaceMap f)
  mixedOldFaceMap_val : ∀ (f : M.MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}),
    (M.mixedOldFaceMap f x).1 = fun k ↦ ∑ v : M.OldVertex,
      extendFaceCoordinates (M.mixedOldFaceVertices f) x v * v.1.1 k
  localMixedFaceMap_eq_iff : ∀ {t u : M.localComplex.Face}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl u)}},
    M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inl u) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl u)) y
  fanMixedFaceMap_eq_iff : ∀ {f g : M.OutsideFanFace}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr g)}},
    M.mixedOldFaceMap (Sum.inr f) x = M.mixedOldFaceMap (Sum.inr g) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr g)) y
  mixedOldFaceMap_simplexLineMap : ∀ (f : M.MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1),
    (M.mixedOldFaceMap f (simplexLineMap x y r)).1 =
      AffineMap.lineMap (M.mixedOldFaceMap f x).1 (M.mixedOldFaceMap f y).1 r.1
  mixedOldFaceMap_vertex : ∀ (f : M.MixedOldFace)
      (v : {v // v ∈ M.mixedOldFaceVertices f}),
    M.mixedOldFaceMap f (stdSimplex.vertex v) = v.1.1

/-- The local interpolation laws shared by construction and compatibility. -/
private structure MixedLocalInterpolationCertificate (M : MixedLocalFanData) where
  localUsedVertex_mem_face_of_map_eq : ∀ (t : M.localComplex.Face)
      (z : stdSimplex ℝ {v // v ∈ t.1}) (u : M.localComplex.UsedVertex),
    M.localFaceMap t z = M.localVertexPoint u → u.1 ∈ t.1
  exists_localFacePoint_eq_of_edgeParameter_between : ∀
      (t : M.localComplex.Face) (e : M.ambient.Edge) (a b : {v // v ∈ t.1})
      (p : M.ambient.realization),
    M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩ ∈ M.ambient.faceCarrier e.1 →
    M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩ ∈ M.ambient.faceCarrier e.1 →
    p ∈ M.ambient.faceCarrier e.1 →
    M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) ≤
      M.marking.edgeParameterValue e p →
    M.marking.edgeParameterValue e p ≤ M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩) →
    M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) <
      M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩) →
    ∃ z : stdSimplex ℝ {v // v ∈ t.1}, M.localFaceMap t z = p

/-- The local facts needed by the chart-independent local/fan compatibility argument. -/
private structure MixedLocalFanCertificate (M : MixedLocalFanData)
    extends MixedMapCertificate M, MixedLocalInterpolationCertificate M where
  parentFace : M.localComplex.Face → M.ambient.Face
  outside_parent_ne : ∀ (f : M.OutsideFanFace) (t : M.localComplex.Face),
    f.1.1 ≠ parentFace t
  mixedOldFaceMap_eq_of_extendedCoordinates :
    ∀ {f g : M.MixedOldFace}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g}},
      extendFaceCoordinates (M.mixedOldFaceVertices f) x =
          extendFaceCoordinates (M.mixedOldFaceVertices g) y →
        M.mixedOldFaceMap f x = M.mixedOldFaceMap g y
  localMixedFaceMap_mem_parent :
    ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}),
      M.mixedOldFaceMap (Sum.inl t) x ∈ M.ambient.faceCarrier (parentFace t).1
  localVertexPoint_mem_parent :
    ∀ (t : M.localComplex.Face) (v : {v // v ∈ t.1}),
      M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
        M.ambient.faceCarrier (parentFace t).1
  localVertexPoint_mem_marking :
    ∀ v : M.localComplex.UsedVertex, M.localVertexPoint v ∈ M.marking.points
  positive_localVertex_mem_edge :
    ∀ (t : M.localComplex.Face) (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : M.ambient.Edge),
      M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
        ∀ (v : {v // v ∈ t.1}), 0 < x v →
          M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ M.ambient.faceCarrier e.1
  localFace_edgeParameter_eq_sum :
    ∀ (t : M.localComplex.Face) (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : M.ambient.Edge),
      M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
        M.marking.edgeParameterValue e (M.localFaceMap t x) =
          ∑ v : {v // v ∈ t.1}, x v * M.marking.edgeParameterValue e
            (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)
  edge_subset_face_of_openPoint :
    ∀ (e : M.ambient.Edge) (s : M.ambient.Face) (q : M.ambient.realization),
      q ∈ M.ambient.edgePath e '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} →
        q ∈ M.ambient.faceCarrier s.1 → e.1 ⊆ s.1
  edgeMark_lift :
    ∀ (t : M.localComplex.Face) (e : M.ambient.Edge),
      e.1 ⊆ (parentFace t).1 → ∀ p ∈ M.marking.edgeMarks e,
        ∃ u : M.localComplex.UsedVertex, M.localVertexPoint u = p
  markingPoint_lift :
    ∀ (t : M.localComplex.Face) p, p ∈ M.marking.points →
      p ∈ M.ambient.faceCarrier (parentFace t).1 →
        ∃ u : M.localComplex.UsedVertex, M.localVertexPoint u = p
  mixedLocalExtended_eq_single_of_map_eq_localVertex :
    ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)})
      (u : M.localComplex.UsedVertex),
      M.mixedOldFaceMap (Sum.inl t) x = M.localVertexPoint u →
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
          Pi.single (M.localOldVertexEmbedding u) 1
  mixedFanExtended_eq_single_of_map_eq_fanVertex :
    ∀ (f : M.OutsideFanFace)
      (y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)})
      (v : {p // p ∈ M.marking.fanFaceVertices f.1}),
      M.mixedOldFaceMap (Sum.inr f) y = v.1 →
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y =
          Pi.single (M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v)) 1

private structure LocalFanIntervalVertices
    (M : MixedLocalFanData) (t : M.localComplex.Face) (f : M.OutsideFanFace) where
  first : M.localComplex.UsedVertex
  second : M.localComplex.UsedVertex
  first_mem : first.1 ∈ t.1
  second_mem : second.1 ∈ t.1
  first_eq : M.localVertexPoint first =
    M.marking.edgeIntervalFirst (M.ambient.faceEdge f.1.1 f.1.2.1) f.1.2.2
  second_eq : M.localVertexPoint second =
    M.marking.edgeIntervalSecond (M.ambient.faceEdge f.1.1 f.1.2.1) f.1.2.2

private theorem MixedLocalFanCertificate.exists_localFanIntervalVertices
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
    (hxy : M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y)
    (hyCenter :
      (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanCenterVertex f.1) = 0)
    (hyPos :
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanFirstVertex f.1) ∧
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanSecondVertex f.1)) :
    Nonempty (LocalFanIntervalVertices M t f) := by
  let x₀ := relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x
  let yG := relabelFaceSimplex M.fanOldVertexEmbedding
    (M.marking.globalFanFaceVertices f.1) y
  let y₀ := M.marking.fanRelabelSimplex f.1 yG
  let e := M.ambient.faceEdge f.1.1 f.1.2.1
  let q := M.mixedOldFaceMap (Sum.inl t) x
  let p₀ := M.marking.edgeIntervalFirst e f.1.2.2
  let p₁ := M.marking.edgeIntervalSecond e f.1.2.2
  let a₀ := M.marking.edgeParameterValue e p₀
  let a₁ := M.marking.edgeParameterValue e p₁
  let z₀ := M.marking.edgeParameterValue e q
  have hfanEq : M.marking.fanFaceMap f.1 y₀ = q := hxy.symm
  have hqOpen :
      q ∈ M.ambient.edgePath e ''
        {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} := by
    rw [← hfanEq]
    exact M.marking.fanFaceMap_mem_edgePath_image_Ioo_of_center_zero_of_base_weights_pos
      f.1 y₀ hyCenter hyPos.1 hyPos.2
  have hqEdge : q ∈ M.ambient.faceCarrier e.1 := by
    rw [← hfanEq]
    exact M.marking.fanFaceMap_mem_baseEdge_of_center_eq_zero f.1 y₀ hyCenter
  have heSelected : e.1 ⊆ (C.parentFace t).1 :=
    C.edge_subset_face_of_openPoint e (C.parentFace t) q hqOpen
      (C.localMixedFaceMap_mem_parent t x)
  have hzInterval : z₀ ∈ Set.Ioo a₀ a₁ := by
    change M.marking.edgeParameterValue e q ∈
      Set.Ioo
        (M.marking.edgeParameterValue e (M.marking.fanFirstVertex f.1).1)
        (M.marking.edgeParameterValue e (M.marking.fanSecondVertex f.1).1)
    rw [← hfanEq]
    exact M.marking.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
      f.1 y₀ hyCenter hyPos.1 hyPos.2
  have hzAverage :
      z₀ = ∑ v : {v // v ∈ t.1}, x₀ v * M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) :=
    C.localFace_edgeParameter_eq_sum t x₀ e hqEdge
  have hgap (v : {v // v ∈ t.1}) (hvPos : 0 < x₀ v) :
      ¬M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ∈ Set.Ioo a₀ a₁ := by
    have hvEdge := C.positive_localVertex_mem_edge t x₀ e hqEdge v hvPos
    have hvMark : M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
        M.marking.edgeMarks e :=
      (M.marking.mem_edgeMarks_iff e _).mpr
        ⟨C.localVertexPoint_mem_marking ⟨v.1, ⟨t.1, t.2, v.2⟩⟩, hvEdge⟩
    exact M.marking.not_edgeMark_parameter_mem_Ioo e f.1.2.2 hvMark
  obtain ⟨⟨lo, hloPos, hlo⟩, ⟨hi, hhiPos, hhi⟩⟩ :=
    exists_positive_weight_on_both_sides_of_gap
      (weight := fun v : {v // v ∈ t.1} ↦ x₀ v)
      (value := fun v ↦ M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩))
      a₀ a₁ z₀ x₀.2.1 x₀.2.2 hzAverage hgap hzInterval
  have hloEdge := C.positive_localVertex_mem_edge t x₀ e hqEdge lo hloPos
  have hhiEdge := C.positive_localVertex_mem_edge t x₀ e hqEdge hi hhiPos
  have hp₀Mark : p₀ ∈ M.marking.edgeMarks e :=
    M.marking.edgeIntervalFirst_mem_edgeMarks e f.1.2.2
  have hp₁Mark : p₁ ∈ M.marking.edgeMarks e :=
    M.marking.edgeIntervalSecond_mem_edgeMarks e f.1.2.2
  have hp₀Edge := ((M.marking.mem_edgeMarks_iff e p₀).mp hp₀Mark).2
  have hp₁Edge := ((M.marking.mem_edgeMarks_iff e p₁).mp hp₁Mark).2
  obtain ⟨u₀, hu₀⟩ := C.edgeMark_lift t e heSelected p₀ hp₀Mark
  obtain ⟨u₁, hu₁⟩ := C.edgeMark_lift t e heSelected p₁ hp₁Mark
  have hlohi : M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨lo.1, ⟨t.1, t.2, lo.2⟩⟩) <
      M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨hi.1, ⟨t.1, t.2, hi.2⟩⟩) := by
    calc
      _ ≤ a₀ := hlo
      _ < a₁ := hzInterval.1.trans hzInterval.2
      _ ≤ _ := hhi
  have hp₀hi : M.marking.edgeParameterValue e p₀ ≤
      M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨hi.1, ⟨t.1, t.2, hi.2⟩⟩) :=
    le_trans (hzInterval.1.trans hzInterval.2).le hhi
  have hloP₁ : M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨lo.1, ⟨t.1, t.2, lo.2⟩⟩) ≤
      M.marking.edgeParameterValue e p₁ :=
    le_trans hlo (hzInterval.1.trans hzInterval.2).le
  obtain ⟨zAt, hzAt⟩ := C.exists_localFacePoint_eq_of_edgeParameter_between
    t e lo hi p₀ hloEdge hhiEdge hp₀Edge hlo hp₀hi hlohi
  obtain ⟨zBt, hzBt⟩ := C.exists_localFacePoint_eq_of_edgeParameter_between
    t e lo hi p₁ hloEdge hhiEdge hp₁Edge hloP₁ hhi hlohi
  have hu₀Face : u₀.1 ∈ t.1 :=
    C.localUsedVertex_mem_face_of_map_eq t zAt u₀ (hzAt.trans hu₀.symm)
  have hu₁Face : u₁.1 ∈ t.1 :=
    C.localUsedVertex_mem_face_of_map_eq t zBt u₁ (hzBt.trans hu₁.symm)
  exact ⟨u₀, u₁, hu₀Face, hu₁Face, hu₀, hu₁⟩

private theorem MixedLocalFanCertificate.localFanInterior_extendedCoordinates_eq
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
    (hxy : M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y)
    (hyCenter :
      (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanCenterVertex f.1) = 0)
    (hyPos :
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanFirstVertex f.1) ∧
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanSecondVertex f.1)) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y := by
  let yG := relabelFaceSimplex M.fanOldVertexEmbedding
    (M.marking.globalFanFaceVertices f.1) y
  let y₀ := M.marking.fanRelabelSimplex f.1 yG
  let e := M.ambient.faceEdge f.1.1 f.1.2.1
  let q := M.mixedOldFaceMap (Sum.inl t) x
  let p₀ := M.marking.edgeIntervalFirst e f.1.2.2
  let p₁ := M.marking.edgeIntervalSecond e f.1.2.2
  let a₀ := M.marking.edgeParameterValue e p₀
  let a₁ := M.marking.edgeParameterValue e p₁
  let z₀ := M.marking.edgeParameterValue e q
  obtain ⟨D⟩ := C.exists_localFanIntervalVertices M hxy hyCenter hyPos
  let v₀t : {v // v ∈ t.1} := ⟨D.first.1, D.first_mem⟩
  let v₁t : {v // v ∈ t.1} := ⟨D.second.1, D.second_mem⟩
  have hv₀Local : M.localFaceOldVertexEmbedding t v₀t =
      M.localOldVertexEmbedding D.first := Subtype.ext rfl
  have hv₁Local : M.localFaceOldVertexEmbedding t v₁t =
      M.localOldVertexEmbedding D.second := Subtype.ext rfl
  have hw₀LocalMem : M.localOldVertexEmbedding D.first ∈
      M.mixedOldFaceVertices (Sum.inl t) := by
    change M.localOldVertexEmbedding D.first ∈
      (Finset.univ : Finset {v // v ∈ t.1}).map (M.localFaceOldVertexEmbedding t)
    rw [← hv₀Local]
    exact mem_map_univ (M.localFaceOldVertexEmbedding t) v₀t
  have hw₁LocalMem : M.localOldVertexEmbedding D.second ∈
      M.mixedOldFaceVertices (Sum.inl t) := by
    change M.localOldVertexEmbedding D.second ∈
      (Finset.univ : Finset {v // v ∈ t.1}).map (M.localFaceOldVertexEmbedding t)
    rw [← hv₁Local]
    exact mem_map_univ (M.localFaceOldVertexEmbedding t) v₁t
  let w₀Local : {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)} :=
    ⟨M.localOldVertexEmbedding D.first, hw₀LocalMem⟩
  let w₁Local : {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)} :=
    ⟨M.localOldVertexEmbedding D.second, hw₁LocalMem⟩
  let gv₀ : M.marking.FanVertex :=
    M.marking.fanVertexEmbedding f.1 (M.marking.fanFirstVertex f.1)
  let gv₁ : M.marking.FanVertex :=
    M.marking.fanVertexEmbedding f.1 (M.marking.fanSecondVertex f.1)
  have hw₀Raw : M.localOldVertexEmbedding D.first = M.fanOldVertexEmbedding gv₀ :=
    Subtype.ext D.first_eq
  have hw₁Raw : M.localOldVertexEmbedding D.second = M.fanOldVertexEmbedding gv₁ :=
    Subtype.ext D.second_eq
  have hgv₀Mem : gv₀ ∈ M.marking.globalFanFaceVertices f.1 :=
    fanFirstVertexEmbedding_mem_globalFanFaceVertices M.marking f.1
  have hgv₁Mem : gv₁ ∈ M.marking.globalFanFaceVertices f.1 :=
    fanSecondVertexEmbedding_mem_globalFanFaceVertices M.marking f.1
  have hw₀FanMem : M.fanOldVertexEmbedding gv₀ ∈
      M.mixedOldFaceVertices (Sum.inr f) := by
    change M.fanOldVertexEmbedding gv₀ ∈
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding
    exact mem_finset_map M.fanOldVertexEmbedding _ hgv₀Mem
  have hw₁FanMem : M.fanOldVertexEmbedding gv₁ ∈
      M.mixedOldFaceVertices (Sum.inr f) := by
    change M.fanOldVertexEmbedding gv₁ ∈
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding
    exact mem_finset_map M.fanOldVertexEmbedding _ hgv₁Mem
  let w₀Fan : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    ⟨M.fanOldVertexEmbedding gv₀, hw₀FanMem⟩
  let w₁Fan : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    ⟨M.fanOldVertexEmbedding gv₁, hw₁FanMem⟩
  let β := y₀ (M.marking.fanSecondVertex f.1)
  let r : Set.Icc (0 : ℝ) 1 := ⟨β, y₀.2.1 _, stdSimplex.le_one y₀ _⟩
  let xLine := simplexLineMap (stdSimplex.vertex w₀Local) (stdSimplex.vertex w₁Local) r
  let yLine := simplexLineMap (stdSimplex.vertex w₀Fan) (stdSimplex.vertex w₁Fan) r
  have hlineCoords :
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) xLine =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) yLine :=
    extendFaceCoordinates_simplexLineMap_vertices_eq
      (M.mixedOldFaceVertices (Sum.inl t)) (M.mixedOldFaceVertices (Sum.inr f))
      w₀Local w₁Local w₀Fan w₁Fan hw₀Raw hw₁Raw r
  have hp₀Edge := M.marking.edgeIntervalFirst_mem_faceCarrier e f.1.2.2
  have hp₁Edge := M.marking.edgeIntervalSecond_mem_faceCarrier e f.1.2.2
  have hyLineVal : (M.mixedOldFaceMap (Sum.inr f) yLine).1 =
      AffineMap.lineMap p₀.1 p₁.1 β := by
    dsimp only [yLine]
    calc
      (M.mixedOldFaceMap (Sum.inr f)
          (simplexLineMap (stdSimplex.vertex w₀Fan) (stdSimplex.vertex w₁Fan) r)).1 =
          AffineMap.lineMap w₀Fan.1.1.1 w₁Fan.1.1.1 r.1 := by
        apply map_simplexLineMap_vertices
          (fun z ↦ (M.mixedOldFaceMap (Sum.inr f) z).1) (fun v ↦ v.1.1)
        · exact fun z w s ↦ C.mixedOldFaceMap_simplexLineMap (Sum.inr f) z w s
        · exact fun v ↦ congrArg Subtype.val (C.mixedOldFaceMap_vertex (Sum.inr f) v)
      _ = AffineMap.lineMap p₀.1 p₁.1 β := by rfl
  have hyLineEdge : M.mixedOldFaceMap (Sum.inr f) yLine ∈ M.ambient.faceCarrier e.1 :=
    mem_faceCarrier_of_val_eq_lineMap e.1 p₀ p₁ _ β hp₀Edge hp₁Edge hyLineVal
  have hfanEq : M.marking.fanFaceMap f.1 y₀ = q := hxy.symm
  have hqEdge : q ∈ M.ambient.faceCarrier e.1 := by
    rw [← hfanEq]
    exact M.marking.fanFaceMap_mem_baseEdge_of_center_eq_zero f.1 y₀ hyCenter
  have hyLineParameter : M.marking.edgeParameterValue e
        (M.mixedOldFaceMap (Sum.inr f) yLine) = (1 - β) * a₀ + β * a₁ :=
    edgeParameterValue_eq_lineMap M.marking e p₀ p₁ _ β hp₀Edge hp₁Edge hyLineVal
  have hqParameter : z₀ = y₀ (M.marking.fanFirstVertex f.1) * a₀ + β * a₁ := by
    change M.marking.edgeParameterValue e q =
      y₀ (M.marking.fanFirstVertex f.1) *
          M.marking.edgeParameterValue e (M.marking.fanFirstVertex f.1).1 +
        y₀ (M.marking.fanSecondVertex f.1) *
          M.marking.edgeParameterValue e (M.marking.fanSecondVertex f.1).1
    rw [← hfanEq]
    exact M.marking.edgeParameterValue_fanFaceMap_of_center_eq_zero f.1 y₀ hyCenter
  have hbaseSum := M.marking.fanBaseWeights_sum_of_center_eq_zero f.1 y₀ hyCenter
  have hfirstCoeff : 1 - β = y₀ (M.marking.fanFirstVertex f.1) := by
    dsimp only [β]
    linarith
  have hyLineEq : M.mixedOldFaceMap (Sum.inr f) yLine = q := by
    apply M.marking.edgeParameterValue_injOn e hyLineEdge hqEdge
    calc
      _ = (1 - β) * a₀ + β * a₁ := hyLineParameter
      _ = y₀ (M.marking.fanFirstVertex f.1) * a₀ + β * a₁ := by rw [hfirstCoeff]
      _ = z₀ := hqParameter.symm
      _ = M.marking.edgeParameterValue e q := rfl
  exact coordinates_eq_of_comparison
    (M.mixedOldFaceMap (Sum.inl t)) (M.mixedOldFaceMap (Sum.inr f))
    (extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)))
    (extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)))
    (fun {_ _} h ↦ C.localMixedFaceMap_eq_iff.mp h)
    (fun {_ _} h ↦ C.fanMixedFaceMap_eq_iff.mp h)
    (fun {z w} h ↦ C.mixedOldFaceMap_eq_of_extendedCoordinates
      (f := Sum.inl t) (g := Sum.inr f) (x := z) (y := w) h)
    hxy hlineCoords (hyLineEq.trans hxy)

private theorem MixedLocalFanCertificate.localFanEndpoint_extendedCoordinates_eq
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
    (hxy : M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y)
    (v : {p // p ∈ M.marking.fanFaceVertices f.1})
    (hvMark : v.1 ∈ M.marking.points)
    (hyv : (M.marking.fanFaceMap f.1
      (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))).1 = v.1.1) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y := by
  have hyEndpoint : M.mixedOldFaceMap (Sum.inr f) y = v.1 := by
    apply Subtype.ext
    exact hyv
  have hvSelected : v.1 ∈ M.ambient.faceCarrier (C.parentFace t).1 := by
    rw [← hyEndpoint, ← hxy]
    exact C.localMixedFaceMap_mem_parent t x
  obtain ⟨u, hu⟩ := C.markingPoint_lift t v.1 hvMark hvSelected
  have hxLocal :
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        Pi.single (M.localOldVertexEmbedding u) 1 :=
    C.mixedLocalExtended_eq_single_of_map_eq_localVertex
      t x u (hxy.trans (hyEndpoint.trans hu.symm))
  have hyFan :
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y =
        Pi.single
          (M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v)) 1 :=
    C.mixedFanExtended_eq_single_of_map_eq_fanVertex f y v hyEndpoint
  have hvertex :
      M.localOldVertexEmbedding u =
        M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v) := by
    apply Subtype.ext
    exact hu
  rw [hxLocal, hyFan, hvertex]

-- The raw straightening witness is kept behind one projection boundary so later phases do not
-- inherit the full dependent telescope produced by the existential straightening statement.
private theorem MixedLocalFanCertificate.localFanMixedFaceMap_eq_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}} :
    M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y := by
  let mixedFaceSimplexLineMap
      (g : M.MixedOldFace)
      (z w : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g})
      (r : Set.Icc (0 : ℝ) 1) :
      stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g} :=
    simplexLineMap z w r
  let x₀ := relabelUnivSimplex
    (M.localFaceOldVertexEmbedding t) x
  let yG := relabelFaceSimplex M.fanOldVertexEmbedding
    (M.marking.globalFanFaceVertices f.1) y
  let y₀ := M.marking.fanRelabelSimplex f.1 yG
  constructor
  · intro hxy
    have hyParent :
        M.marking.fanFaceMap f.1 y₀ ∈
          M.ambient.faceCarrier (C.parentFace t).1 := by
      have hlocal := C.localMixedFaceMap_mem_parent t x
      have hfan :
          M.marking.fanFaceMap f.1 y₀ =
            M.mixedOldFaceMap (Sum.inr f) y := rfl
      rw [hfan, ← hxy]
      exact hlocal
    have hparentNe : f.1.1 ≠ C.parentFace t :=
      C.outside_parent_ne f t
    have hyCenter :
        y₀ (M.marking.fanCenterVertex f.1) = 0 :=
      M.marking.fanCenterWeight_eq_zero_of_mem_faceCarrier_of_parent_ne
        f.1 (C.parentFace t) hparentNe y₀ hyParent
    by_cases hyPos :
        0 < y₀ (M.marking.fanFirstVertex f.1) ∧
          0 < y₀ (M.marking.fanSecondVertex f.1)
    · exact C.localFanInterior_extendedCoordinates_eq M hxy hyCenter hyPos
    · let endpointCoordinates := C.localFanEndpoint_extendedCoordinates_eq M hxy
      rcases
          M.marking.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
            f.1 y₀ hyCenter hyPos with hyFirst | hySecond
      · exact endpointCoordinates
          (M.marking.fanFirstVertex f.1)
          (((M.marking.mem_edgeMarks_iff
            (M.ambient.faceEdge f.1.1 f.1.2.1) _).mp
              (M.marking.edgeIntervalFirst_mem_edgeMarks
                (M.ambient.faceEdge f.1.1 f.1.2.1)
                f.1.2.2)).1)
          hyFirst.1
      · exact endpointCoordinates
          (M.marking.fanSecondVertex f.1)
          (((M.marking.mem_edgeMarks_iff
            (M.ambient.faceEdge f.1.1 f.1.2.1) _).mp
              (M.marking.edgeIntervalSecond_mem_edgeMarks
                (M.ambient.faceEdge f.1.1 f.1.2.1)
                f.1.2.2)).1)
          hySecond.1
  · intro hcoords
    exact C.mixedOldFaceMap_eq_of_extendedCoordinates
      (f := Sum.inl t) (g := Sum.inr f)
      (x := x) (y := y) hcoords

private theorem MixedLocalFanCertificate.mixedOldFaceMap_eq_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {f g : M.MixedOldFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g}} :
    M.mixedOldFaceMap f x = M.mixedOldFaceMap g y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices f) x =
        extendFaceCoordinates (M.mixedOldFaceVertices g) y := by
  rcases f with t | f <;> rcases g with u | g
  · exact C.localMixedFaceMap_eq_iff
  · exact C.localFanMixedFaceMap_eq_iff
  · constructor
    · intro hxy
      exact C.localFanMixedFaceMap_eq_iff.mp hxy.symm |>.symm
    · intro hcoords
      exact (C.localFanMixedFaceMap_eq_iff.mpr hcoords.symm).symm
  · exact C.fanMixedFaceMap_eq_iff

private noncomputable abbrev MixedLocalFanData.usedOldVertices (M : MixedLocalFanData) :
    Finset M.OldVertex :=
  (Finset.univ : Finset M.MixedOldFace).biUnion M.mixedOldFaceVertices

private abbrev MixedLocalFanData.UsedOldVertex (M : MixedLocalFanData) :=
  {v : M.OldVertex // v ∈ M.usedOldVertices}

private noncomputable abbrev MixedLocalFanData.mixedFaceUsedEmbedding
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    {v // v ∈ M.mixedOldFaceVertices f} ↪ M.UsedOldVertex :=
  { toFun := fun v ↦ ⟨v.1, Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ f, v.2⟩⟩
    inj' := fun _ _ h ↦ Subtype.ext
      (congrArg (fun z : M.UsedOldVertex ↦ z.1) h) }

private noncomputable abbrev MixedLocalFanData.mixedUsedFaceVertices
    (M : MixedLocalFanData) (f : M.MixedOldFace) : Finset M.UsedOldVertex :=
  (Finset.univ : Finset {v // v ∈ M.mixedOldFaceVertices f}).map
    (M.mixedFaceUsedEmbedding f)

private noncomputable abbrev MixedLocalFanData.mixedUsedFaceMap
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f} → M.ambient.realization :=
  fun x ↦ M.mixedOldFaceMap f
    (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x)

private theorem MixedLocalFanCertificate.mixedUsedFaceVertices_card
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) (f : M.MixedOldFace) :
    (M.mixedUsedFaceVertices f).card = 3 := by
  change ((Finset.univ : Finset {v // v ∈ M.mixedOldFaceVertices f}).map
    (M.mixedFaceUsedEmbedding f)).card = 3
  rw [Finset.card_map, Finset.card_univ, Fintype.card_coe,
    C.mixedOldFaceVertices_card]

private theorem MixedLocalFanCertificate.continuous_mixedUsedFaceMap
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) (f : M.MixedOldFace) :
    Continuous (M.mixedUsedFaceMap f) :=
  (C.continuous_mixedOldFaceMap f).comp
    (stdSimplex.continuous_map (univMapSubtypeEquiv (M.mixedFaceUsedEmbedding f)))

private theorem MixedLocalFanData.mixedUsedExtended_apply
    (M : MixedLocalFanData) (f : M.MixedOldFace)
    (x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f})
    (p : M.UsedOldVertex) :
    extendFaceCoordinates (M.mixedUsedFaceVertices f) x p =
      extendFaceCoordinates (M.mixedOldFaceVertices f)
        (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) p.1 := by
  by_cases hp : p.1 ∈ M.mixedOldFaceVertices f
  · let v : {v // v ∈ M.mixedOldFaceVertices f} := ⟨p.1, hp⟩
    have hemb : M.mixedFaceUsedEmbedding f v = p := Subtype.ext rfl
    have hmem : M.mixedFaceUsedEmbedding f v ∈ M.mixedUsedFaceVertices f :=
      mem_map_univ (M.mixedFaceUsedEmbedding f) v
    have hpMem : p ∈ M.mixedUsedFaceVertices f := hemb ▸ hmem
    rw [extendFaceCoordinates_of_mem _ _ hpMem,
      extendFaceCoordinates_of_mem _ _ hp]
    have hleft :
        (⟨p, hpMem⟩ : {q // q ∈ M.mixedUsedFaceVertices f}) =
          ⟨M.mixedFaceUsedEmbedding f v, hmem⟩ := Subtype.ext hemb.symm
    have hright :
        (⟨p.1, hp⟩ : {q // q ∈ M.mixedOldFaceVertices f}) = v :=
      Subtype.ext rfl
    rw [hleft, hright]
    have hmapMem :
        M.mixedFaceUsedEmbedding f v ∈
          (Finset.univ : Finset {q // q ∈ M.mixedOldFaceVertices f}).map
            (M.mixedFaceUsedEmbedding f) :=
      mem_map_univ (M.mixedFaceUsedEmbedding f) v
    have hrel := (relabelUnivSimplex_apply (M.mixedFaceUsedEmbedding f) x v).symm
    rw [extendFaceCoordinates_of_mem _ _ hmapMem] at hrel
    exact hrel
  · have hpUsed : p ∉ M.mixedUsedFaceVertices f := by
      intro hpUsed
      obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpUsed
      exact hp (congrArg (fun z : M.UsedOldVertex ↦ z.1) hv ▸ v.2)
    rw [extendFaceCoordinates_of_notMem _ _ hpUsed,
      extendFaceCoordinates_of_notMem _ _ hp]

private theorem MixedLocalFanCertificate.mixedUsedFaceMap_val
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (f : M.MixedOldFace)
    (x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f}) :
    (M.mixedUsedFaceMap f x).1 = fun k ↦ ∑ v : M.UsedOldVertex,
      extendFaceCoordinates (M.mixedUsedFaceVertices f) x v * v.1.1.1 k := by
  rw [show M.mixedUsedFaceMap f x = M.mixedOldFaceMap f
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) by rfl,
    C.mixedOldFaceMap_val]
  funext k
  have hused := sum_extendFaceCoordinates_relabelUnivSimplex
    (M.mixedFaceUsedEmbedding f) x (fun v : M.UsedOldVertex ↦ v.1.1.1 k)
  have hold :
      (∑ v : M.OldVertex,
          extendFaceCoordinates (M.mixedOldFaceVertices f)
              (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) v * v.1.1 k) =
        ∑ v ∈ M.mixedOldFaceVertices f,
          extendFaceCoordinates (M.mixedOldFaceVertices f)
              (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) v * v.1.1 k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [extendFaceCoordinates_of_notMem _ _ hv, zero_mul]
  rw [hused, hold,
    ← sum_attach_mul_eq_sum_extendFaceCoordinates
      (M.mixedOldFaceVertices f)
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x)
      (fun v : M.OldVertex ↦ v.1.1 k)]
  rfl

private theorem MixedLocalFanCertificate.mixedUsedFaceMap_eq_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {f g : M.MixedOldFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices g}} :
    M.mixedUsedFaceMap f x = M.mixedUsedFaceMap g y ↔
      extendFaceCoordinates (M.mixedUsedFaceVertices f) x =
        extendFaceCoordinates (M.mixedUsedFaceVertices g) y := by
  rw [show M.mixedUsedFaceMap f x = M.mixedOldFaceMap f
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) from rfl,
    show M.mixedUsedFaceMap g y = M.mixedOldFaceMap g
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding g) y) from rfl,
    C.mixedOldFaceMap_eq_iff]
  constructor
  · intro hcoords
    funext p
    rw [M.mixedUsedExtended_apply f x p, M.mixedUsedExtended_apply g y p,
      congrFun hcoords p.1]
  · intro hcoords
    funext p
    by_cases hp : p ∈ M.usedOldVertices
    · let q : M.UsedOldVertex := ⟨p, hp⟩
      have hq := congrFun hcoords q
      rw [M.mixedUsedExtended_apply f x q,
        M.mixedUsedExtended_apply g y q] at hq
      exact hq
    · have hpf : p ∉ M.mixedOldFaceVertices f := fun hpf ↦
        hp (Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ f, hpf⟩)
      have hpg : p ∉ M.mixedOldFaceVertices g := fun hpg ↦
        hp (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hpg⟩)
      rw [extendFaceCoordinates_of_notMem _ _ hpf,
        extendFaceCoordinates_of_notMem _ _ hpg]

private noncomputable abbrev MixedLocalFanCertificate.mixedOldComplex
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) :
    LocallyFiniteTriangleComplex M.ambient.realization where
  Vertex := M.UsedOldVertex
  Face := M.MixedOldFace
  faceVertices := M.mixedUsedFaceVertices
  faceVertices_card := C.mixedUsedFaceVertices_card
  vertex_used := by
    intro v
    obtain ⟨f, -, hvf⟩ := Finset.mem_biUnion.mp v.2
    have hvMem :
        M.mixedFaceUsedEmbedding f ⟨v.1, hvf⟩ ∈ M.mixedUsedFaceVertices f :=
      mem_map_univ (M.mixedFaceUsedEmbedding f) ⟨v.1, hvf⟩
    refine ⟨f, ?_⟩
    exact hvMem
  faceMap := M.mixedUsedFaceMap
  faceMap_continuous := C.continuous_mixedUsedFaceMap
  faceMap_eq_iff := C.mixedUsedFaceMap_eq_iff
  locallyFinite := locallyFinite_of_finite _

/-- The subdivision assembled from the local old faces and the complementary marked fan.
Keeping this construction independent of the chart weld prevents the final weld proof from
re-elaborating the full mixed-face coordinate argument. -/
private noncomputable def MixedLocalFanCertificate.mixedSubdivision
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (hsupport : (C.mixedOldComplex M).support = Set.univ) : M.ambient.Subdivision := by
  let K := C.mixedOldComplex M
  let homeo : K.compactIntrinsic.realization ≃ₜ M.ambient.realization := by
    let e : K.compactIntrinsic.realization ≃ M.ambient.realization :=
      Equiv.ofBijective K.compactEval
        ⟨K.injective_compactEval, by
          intro y
          have hy : y ∈ K.support := by
            rw [hsupport]
            exact Set.mem_univ y
          rw [← K.range_compactEval] at hy
          exact hy⟩
    exact Continuous.homeoOfEquivCompactToT2 (f := e) K.continuous_compactEval
  let barycentricAffine :
      (M.UsedOldVertex → ℝ) →ᵃ[ℝ] (M.ambient.Vertex → ℝ) :=
    (∑ v : M.UsedOldVertex,
      (LinearMap.proj v).smulRight
        (v.1.1.1 : M.ambient.Vertex → ℝ)).toAffineMap
  have barycentricAffine_apply (z : M.UsedOldVertex → ℝ) :
      barycentricAffine z = fun k ↦ ∑ v : M.UsedOldVertex, z v * v.1.1.1 k := by
    funext k
    -- These evaluation rules avoid testing whether the dependent vertex type is empty.
    simp only [barycentricAffine, LinearMap.coe_toAffineMap, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  letI : Fintype K.Vertex := K.compactIntrinsic.vertexFintype
  exact
    { refined := K.compactIntrinsic
      homeo := homeo
      affineOnFace := by
        intro s hs
        change s ∈ K.compactIntrinsic.faces at hs
        rw [K.compactIntrinsic_faces] at hs
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
        refine ⟨barycentricAffine, ?_⟩
        intro x hx
        have heval := K.compactEval_eq_faceMap f x hx
        have hhomeo :
            (homeo x).1 = (K.compactEval x).1 :=
          congrArg Subtype.val (show homeo x = K.compactEval x by rfl)
        rw [hhomeo, heval]
        change
          (M.mixedUsedFaceMap f
              (K.restrictToFace (M.mixedUsedFaceVertices f) ⟨x.1, x.2.1⟩ hx)).1 =
            barycentricAffine x.1
        rw [C.mixedUsedFaceMap_val]
        funext k
        rw [congrFun (barycentricAffine_apply x.1) k]
        apply Finset.sum_congr rfl
        intro v _
        apply congrArg (· * v.1.1.1 k)
        by_cases hv : v ∈ M.mixedUsedFaceVertices f
        · rw [extendFaceCoordinates_of_mem _ _ hv]
          rfl
        · simp [extendFaceCoordinates, hv, hx v hv]
      subordinate := by
        intro s hs
        change s ∈ K.compactIntrinsic.faces at hs
        rw [K.compactIntrinsic_faces] at hs
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
        rcases f with t | f
        · refine ⟨(C.parentFace t).1, (C.parentFace t).2, ?_⟩
          intro x hx
          have heval := K.compactEval_eq_faceMap (Sum.inl t) x hx
          change homeo x ∈ M.ambient.faceCarrier (C.parentFace t).1
          rw [show homeo x = K.compactEval x by rfl, heval]
          change
            M.mixedUsedFaceMap (Sum.inl t)
                (K.restrictToFace (M.mixedUsedFaceVertices (Sum.inl t))
                  ⟨x.1, x.2.1⟩ hx) ∈
              M.ambient.faceCarrier (C.parentFace t).1
          exact C.localMixedFaceMap_mem_parent t _
        · refine ⟨f.1.1.1, f.1.1.2, ?_⟩
          intro x hx
          have heval := K.compactEval_eq_faceMap (Sum.inr f) x hx
          change homeo x ∈ M.ambient.faceCarrier f.1.1.1
          rw [show homeo x = K.compactEval x by rfl, heval]
          change
            M.mixedUsedFaceMap (Sum.inr f)
                (K.restrictToFace (M.mixedUsedFaceVertices (Sum.inr f))
                  ⟨x.1, x.2.1⟩ hx) ∈
              M.ambient.faceCarrier f.1.1.1
          exact M.marking.globalFanFaceMap_mem_faceCarrier f.1 _ }

private noncomputable abbrev MixedLocalFanData.localUsedOldEmbedding
    (M : MixedLocalFanData) : M.localComplex.UsedVertex ↪ M.UsedOldVertex :=
  { toFun := fun u ↦ ⟨M.localOldVertexEmbedding u, by
      obtain ⟨t, ht, hut⟩ := u.2
      apply Finset.mem_biUnion.mpr
      refine ⟨Sum.inl (⟨t, ht⟩ : M.localComplex.Face), Finset.mem_univ _, ?_⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨u.1, hut⟩, Finset.mem_univ _, ?_⟩
      exact Subtype.ext rfl⟩
    inj' := fun _ _ h ↦ M.localOldVertexEmbedding.injective
      (congrArg (fun z : M.UsedOldVertex ↦ z.1) h) }

private abbrev MixedLocalFanData.localUsedVertexEmbedding
    (M : MixedLocalFanData) : M.localComplex.UsedVertex ↪ M.localComplex.Vertex :=
  ⟨Subtype.val, Subtype.val_injective⟩

private noncomputable abbrev MixedLocalFanData.CommonVertex (M : MixedLocalFanData) :=
  AmalgamatedVertex M.localUsedOldEmbedding M.localComplex.Vertex

private noncomputable abbrev MixedLocalFanData.oldToCommon (M : MixedLocalFanData) :
    M.UsedOldVertex ↪ M.CommonVertex :=
  oldToAmalgamated M.localUsedOldEmbedding M.localUsedVertexEmbedding

private noncomputable abbrev MixedLocalFanData.targetToCommon (M : MixedLocalFanData) :
    M.localComplex.Vertex ↪ M.CommonVertex :=
  targetToAmalgamated M.localUsedOldEmbedding

private noncomputable abbrev MixedLocalFanCertificate.compactVertexEquiv
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) :
    C.mixedOldComplex.compactIntrinsic.Vertex ≃ M.UsedOldVertex :=
  Equiv.refl _

private noncomputable abbrev MixedLocalFanCertificate.oldCompactToCommon
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) :
    C.mixedOldComplex.compactIntrinsic.Vertex ↪ M.CommonVertex :=
  { toFun := fun v ↦ M.oldToCommon
      (MixedLocalFanCertificate.compactVertexEquiv M C v)
    inj' := fun _ _ h ↦
      (MixedLocalFanCertificate.compactVertexEquiv M C).injective
        (M.oldToCommon.injective h) }

private noncomputable def MixedLocalFanCertificate.hasLocalCommonCoordinates
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (x : C.mixedOldComplex.compactIntrinsic.realization)
    (z : M.localComplex.realization) : Prop := by
  classical
  letI : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  exact
    (pushGeometricRealization C.oldCompactToCommon
        C.mixedOldComplex.compactIntrinsic.faces x).1 =
      (pushGeometricRealization M.targetToCommon M.localComplex.faces z).1

/-- The two geometric facts about a selected region needed to absorb an outside fan face. -/
private structure MixedFanSelectionData (M : MixedLocalFanData) where
  selectedSet : Set M.ambient.realization
  localVertex_mem_selected : ∀ u : M.localComplex.UsedVertex,
    M.localVertexPoint u ∈ selectedSet
  baseEdge_mem_selected :
    ∀ (f : M.OutsideFanFace) (p : M.ambient.realization),
      p ∈ M.ambient.faceCarrier (M.ambient.faceEdge f.1.1 f.1.2.1).1 →
      (∃ u : M.localComplex.UsedVertex,
        M.localVertexPoint u = (M.marking.fanFirstVertex f.1).1) →
      (∃ u : M.localComplex.UsedVertex,
        M.localVertexPoint u = (M.marking.fanSecondVertex f.1).1) →
      p ∈ selectedSet

private noncomputable def MixedLocalFanCertificate.relabelOldFaces
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex] :=
  relabelFaceFamily C.oldCompactToCommon C.mixedOldComplex.compactIntrinsic.faces

private noncomputable def MixedLocalFanData.relabelTargetFaces
    (M : MixedLocalFanData) [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex)) :=
  relabelFaceFamily M.targetToCommon targetFaces

private noncomputable def MixedLocalFanCertificate.relabelOldMap
    {S : Type*} (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S) :
    GeometricRealization M.CommonVertex (C.relabelOldFaces M) → S :=
  eOld ∘ (relabelGeometricRealizationHomeomorph C.oldCompactToCommon
    C.mixedOldComplex.compactIntrinsic.faces).symm

private noncomputable def MixedLocalFanData.relabelTargetMap
    {S : Type*} (M : MixedLocalFanData)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S) :
    GeometricRealization M.CommonVertex (M.relabelTargetFaces targetFaces) → S :=
  eTarget ∘ (relabelGeometricRealizationHomeomorph M.targetToCommon targetFaces).symm

private structure RelabeledWeldCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S)
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S) where
  card : ∀ t ∈ C.relabelOldFaces M ∪ M.relabelTargetFaces targetFaces, t.card = 3
  old_embedding : _root_.Topology.IsEmbedding (C.relabelOldMap M eOld)
  target_embedding : _root_.Topology.IsEmbedding (M.relabelTargetMap targetFaces eTarget)
  old_boundary : PartialTriangulation.BoundaryFacewiseRegularEmbedding
    (C.relabelOldFaces M) (C.relabelOldMap M eOld)
  target_boundary : PartialTriangulation.BoundaryFacewiseRegularEmbedding
    (M.relabelTargetFaces targetFaces) (M.relabelTargetMap targetFaces eTarget)
  range_old : Set.range (C.relabelOldMap M eOld) = Set.range eOld
  range_target : Set.range (M.relabelTargetMap targetFaces eTarget) = Set.range eTarget

private noncomputable def alignedRelativeExtraLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) : List (Plane →ᵃ[ℝ] ℝ) :=
  let n := A.commonLevel (A.tilesMeeting C hC)
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let alignmentLines := A.relativeLevelAlignmentLines C hC N anchorLines n
  anchorLines ++ baseOldMesh.coordinateLines ++ alignmentLines

private theorem exists_baseTriangle_of_alignedRelativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle) :
    ∃ u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle,
      (A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
        (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1 := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let alignmentLines := A.relativeLevelAlignmentLines C hC N anchorLines n
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement
    (A.tileFacePolygonMeeting C hC) N lines
  have htR : t.1 ∈ R.triangles :=
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      (A.tileFacePolygonMeeting C hC) N lines (fun _ ↦ True)).mp t.2 |>.1
  let tR : R.Triangle := ⟨t.1, htR⟩
  have hBaseLines : ∀ a ∈ baseOldMesh.coordinateLines,
      a ∈ N.coordinateLines ++ lines := by
    intro a ha
    apply List.mem_append_right
    change a ∈ A.tileFaceMeetingCertificateLines C hC N ++ extraLines
    apply List.mem_append_right
    change a ∈ anchorLines ++ baseOldMesh.coordinateLines ++ alignmentLines
    exact List.mem_append_left _ (List.mem_append_right _ ha)
  have hhit :
      (interior (R.triangleCarrier tR.1) ∩
        baseOldMesh.toPlaneComplex.support).Nonempty := by
    obtain ⟨p, hp⟩ := R.interior_triangleCarrier_nonempty tR
    refine ⟨p, hp, ?_⟩
    rw [A.tileFacesMeetingRelativeOldMesh_support C hC N anchorLines,
      ← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines]
    rw [localOldMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr
      ⟨t.1, Set.mem_iUnion.mpr ⟨t.2, interior_subset hp⟩⟩
  obtain ⟨u, hu⟩ :=
    (PolygonalFamily.arrangementMesh (A.tileFacePolygonMeeting C hC)
      ).exists_target_triangle_of_refineByLines_of_interior_inter_support
        baseOldMesh (N.coordinateLines ++ lines) hBaseLines tR hhit
  exact ⟨u, hu⟩

private theorem alignedRelativeOldTriangle_source_mem_levelFace
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle)
    (u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle)
    (s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
      s ∈ A.levelFaces (A.tilesMeeting C hC)})
    (p : Plane)
    (hp : p ∈ interior ((A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1))
    (htu : (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
      (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1)
    (hparent : levelFaceParent K s.1 =
      A.relativeOldTriangleParent C hC N anchorLines u)
    (hmono : ∀ k : Fin 3,
      (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).IsMonochromatic
        ((levelFaceParentCoord K s.1 k).comp
          (A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u)))
    (hcoordAtP : ∀ k : Fin 3, 0 <
      ((levelFaceParentCoord K s.1 k).comp
        (A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u)) p) :
    ∀ (r : Plane)
      (hr : r ∈ (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1),
      A.tileFacesMeetingRelativeSourceEmbed C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)
          (A.relativeOldTrianglePoint C hC N
            (alignedRelativeExtraLines A C hC N anchorLines) t ⟨r, hr⟩) ∈
        K.levelFaceCarrier s.1 := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let Rlevel := K.safeSubdivision n
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let source₁ := A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
  let F := A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u
  intro r hr
  let a : Fin 3 → (Plane →ᵃ[ℝ] ℝ) := fun k ↦ (levelFaceParentCoord K s.1 k).comp F
  have hrcoord (k : Fin 3) : 0 ≤ a k r := by
    rcases hmono k t.1 t.2 with hpos | hneg
    · apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (a k)) hr
      rintro z ⟨v, hv, rfl⟩
      exact hpos v hv
    · have hpNonpos : a k p ≤ 0 := by
        apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage (a k))
          (interior_subset hp)
        rintro z ⟨v, hv, rfl⟩
        exact hneg v hv
      exact False.elim ((not_lt_of_ge hpNonpos) (hcoordAtP k))
  let b := affineBasisOfTriangle
    (levelFaceParentPlaneAffine K s.1 ∘ standardTriangleVertex)
    (affineIndependent_comp_of_injOn_convexHull
      standardTriangleVertex standardTriangleVertex_affineIndependent
      (levelFaceParentPlaneAffine K s.1) (by
        rw [← standardTrianglePlaneComplex_support]
        exact levelFaceParentPlaneAffine_injOn K s.1))
  have hFr : F r ∈ convexHull ℝ (Set.range b) := by
    rw [b.convexHull_eq_nonneg_coord]
    exact fun k ↦ hrcoord k
  have hb : (fun i ↦ b i) =
      levelFaceParentPlaneAffine K s.1 ∘ standardTriangleVertex := by
    funext i
    rfl
  have hFr' : F r ∈ convexHull ℝ
      (Set.range (levelFaceParentPlaneAffine K s.1 ∘ standardTriangleVertex)) := by
    rwa [← congrArg Set.range hb]
  rw [Set.range_comp, ← (levelFaceParentPlaneAffine K s.1).image_convexHull,
    ← standardTrianglePlaneComplex_support] at hFr'
  obtain ⟨z', hz', hz'eq⟩ := hFr'
  let z'Support : standardTrianglePlaneComplex.support := ⟨z', hz'⟩
  let rLocal : {q : Plane // q ∈ localOldMesh.triangleCarrier t.1} := ⟨r, hr⟩
  let rBase : {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} := ⟨r, htu hr⟩
  let q' : Rlevel.refined.ClosedFace s.1 :=
    (Rlevel.refined.facePlaneHomeomorph s.1).symm z'Support
  refine ⟨q'.1, q'.2, ?_⟩
  have hsourceR :
      A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
          (A.relativeOldTrianglePoint C hC N anchorLines u rBase) =
        source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal) := by
    apply A.tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq C hC N
    rw [A.relativeOldTrianglePoint_coordinateEmbed C hC N anchorLines u rBase,
      A.relativeOldTrianglePoint_coordinateEmbed C hC N extraLines t rLocal]
  have hsourceRMem : source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal) ∈
      K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 := by
    rw [← hsourceR]
    exact A.relativeOldTriangleParent_contains C hC N anchorLines u _
      (A.relativeOldTrianglePoint_supported C hC N anchorLines u rBase)
  have hq'Parent : Rlevel.homeo q'.1 ∈
      K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 := by
    rw [← hparent]
    exact levelFaceParent_contains K s.1 q'.1 q'.2
  have hclosed :
      (⟨Rlevel.homeo q'.1, hq'Parent⟩ :
          K.ClosedFace (A.relativeOldTriangleParent C hC N anchorLines u)) =
        ⟨source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal),
          hsourceRMem⟩ := by
    apply (K.facePlaneHomeomorph
      (A.relativeOldTriangleParent C hC N anchorLines u)).injective
    apply Subtype.ext
    have hlevel := levelFaceParentPlaneAffine_eq K s.1 z'Support
    have hbase := A.relativeOldTriangleParentPlaneAffine_eq
      C hC N anchorLines u rBase
    rw [K.facePlaneHomeomorph_val_eq_forwardAffine] at hlevel hbase
    calc
      K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
          (Rlevel.homeo q'.1).1 =
          K.facePlaneForwardAffine (levelFaceParent K s.1) (Rlevel.homeo q'.1).1 := by
        rw [hparent]
      _ = levelFaceParentPlaneAffine K s.1 z' := hlevel.symm
      _ = F r := hz'eq
      _ = K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
          (A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
            (A.relativeOldTrianglePoint C hC N anchorLines u rBase)).1 := hbase
      _ = K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
          (source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal)).1 :=
        congrArg (K.facePlaneForwardAffine
          (A.relativeOldTriangleParent C hC N anchorLines u))
          (congrArg Subtype.val hsourceR)
  exact congrArg Subtype.val hclosed

private theorem exists_alignedRelativeOldTriangle_parentWitness
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle) :
    ∃ (u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle)
      (s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
        s ∈ A.levelFaces (A.tilesMeeting C hC)})
      (htu : (A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
        (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1)
      (p : {p : Plane // p ∈ interior
        ((A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1)})
      (q : (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).refined.ClosedFace s.1),
      A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
          (A.relativeOldTrianglePoint C hC N anchorLines u
            ⟨p.1, interior_subset (interior_mono htu p.2)⟩) =
        A.tileFacesMeetingRelativeSourceEmbed C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)
          (A.relativeOldTrianglePoint C hC N
            (alignedRelativeExtraLines A C hC N anchorLines) t
            ⟨p.1, interior_subset p.2⟩) ∧
      A.tileFacesMeetingRelativeSourceEmbed C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)
          (A.relativeOldTrianglePoint C hC N
            (alignedRelativeExtraLines A C hC N anchorLines) t
            ⟨p.1, interior_subset p.2⟩) =
        (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).homeo q.1 ∧
      levelFaceParent K s.1 = A.relativeOldTriangleParent C hC N anchorLines u := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let selectedLevelFaces := A.levelFaces (A.tilesMeeting C hC)
  let Rlevel := K.safeSubdivision n
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let source₁ := A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  have hsource₁Range : Set.range source₁ =
      ⋃ u : {u : K.LevelFace n // u ∈ selectedLevelFaces}, K.levelFaceCarrier u.1 :=
    A.range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces C hC N extraLines
  obtain ⟨u, htu⟩ :=
    exists_baseTriangle_of_alignedRelativeOldTriangle A C hC N anchorLines t
  obtain ⟨p, hp⟩ := localOldMesh.interior_triangleCarrier_nonempty t
  have hpBase : p ∈ interior (baseOldMesh.triangleCarrier u.1) := interior_mono htu hp
  let pLocal : {q : Plane // q ∈ localOldMesh.triangleCarrier t.1} :=
    ⟨p, interior_subset hp⟩
  let pBase : {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
    ⟨p, interior_subset hpBase⟩
  let xLocal := A.relativeOldTrianglePoint C hC N extraLines t pLocal
  let xBase := A.relativeOldTrianglePoint C hC N anchorLines u pBase
  have hsourceEq :
      A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase = source₁ xLocal := by
    apply A.tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq C hC N
    rw [A.relativeOldTrianglePoint_coordinateEmbed C hC N anchorLines u pBase,
      A.relativeOldTrianglePoint_coordinateEmbed C hC N extraLines t pLocal]
  have hxUnion : source₁ xLocal ∈
      ⋃ s : {s : K.LevelFace n // s ∈ selectedLevelFaces}, K.levelFaceCarrier s.1 := by
    rw [← hsource₁Range]
    exact Set.mem_range_self xLocal
  obtain ⟨s, q, hqFace, hqSource⟩ := Set.mem_iUnion.mp hxUnion
  have hbaseMem : source₁ xLocal ∈
      K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 := by
    rw [← hsourceEq]
    exact A.relativeOldTriangleParent_contains C hC N anchorLines u xBase
      (A.relativeOldTrianglePoint_supported C hC N anchorLines u pBase)
  have hlevelMem : source₁ xLocal ∈ K.faceCarrier (levelFaceParent K s.1).1 := by
    have h := levelFaceParent_contains K s.1 q hqFace
    rw [hqSource] at h
    exact h
  let F := A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u
  have hFimage : F '' interior (baseOldMesh.triangleCarrier u.1) ⊆
      standardTrianglePlaneComplex.support := by
    rintro z ⟨r, hr, rfl⟩
    let rBase : {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
      ⟨r, interior_subset hr⟩
    rw [A.relativeOldTriangleParentPlaneAffine_eq C hC N anchorLines u rBase]
    exact (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u) _).2
  have hFopen : IsOpen (F '' interior (baseOldMesh.triangleCarrier u.1)) :=
    (F.isOpenMap F.continuous_of_finiteDimensional
      (A.relativeOldTriangleParentPlaneAffine_surjective C hC N anchorLines u))
      (interior (baseOldMesh.triangleCarrier u.1)) isOpen_interior
  have hpFint : F p ∈ interior standardTrianglePlaneComplex.support := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (hFopen.mem_nhds ⟨p, hpBase, rfl⟩) hFimage
  have hpChartInt :
      (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u)
        ⟨source₁ xLocal, hbaseMem⟩).1 ∈
        interior standardTrianglePlaneComplex.support := by
    have hbaseMem' : A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase ∈
        K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 :=
      A.relativeOldTriangleParent_contains C hC N anchorLines u xBase
        (A.relativeOldTrianglePoint_supported C hC N anchorLines u pBase)
    have hclosed :
        (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase, hbaseMem'⟩ :
          K.ClosedFace (A.relativeOldTriangleParent C hC N anchorLines u)) =
          ⟨source₁ xLocal, hbaseMem⟩ := Subtype.ext hsourceEq
    have heq :
        (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u)
          ⟨source₁ xLocal, hbaseMem⟩).1 = F p := by
      calc
        _ = (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u)
              ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase,
                hbaseMem'⟩).1 :=
          congrArg (fun w ↦ w.1) (congrArg (K.facePlaneHomeomorph
            (A.relativeOldTriangleParent C hC N anchorLines u)) hclosed.symm)
        _ = F p :=
          (A.relativeOldTriangleParentPlaneAffine_eq C hC N anchorLines u pBase).symm
    rw [heq]
    exact hpFint
  have hparent : levelFaceParent K s.1 =
      A.relativeOldTriangleParent C hC N anchorLines u := by
    symm
    exact face_eq_of_mem_faceCarriers_of_facePlane_mem_interior K
      (A.relativeOldTriangleParent C hC N anchorLines u) (levelFaceParent K s.1)
      (source₁ xLocal) hbaseMem hlevelMem hpChartInt
  exact ⟨u, s, htu, ⟨p, hp⟩, ⟨q, hqFace⟩, hsourceEq, hqSource.symm, hparent⟩

private theorem alignedRelativeOldTriangle_planeAt_parentWitness
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle)
    (u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle)
    (s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
      s ∈ A.levelFaces (A.tilesMeeting C hC)})
    (htu : (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
      (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1)
    (p : {p : Plane // p ∈ interior
      ((A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1)})
    (q : (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).refined.ClosedFace s.1)
    (hsourceEq : A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
        (A.relativeOldTrianglePoint C hC N anchorLines u
          ⟨p.1, interior_subset (interior_mono htu p.2)⟩) =
      A.tileFacesMeetingRelativeSourceEmbed C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)
        (A.relativeOldTrianglePoint C hC N
          (alignedRelativeExtraLines A C hC N anchorLines) t
          ⟨p.1, interior_subset p.2⟩))
    (hqSource : A.tileFacesMeetingRelativeSourceEmbed C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)
        (A.relativeOldTrianglePoint C hC N
          (alignedRelativeExtraLines A C hC N anchorLines) t
          ⟨p.1, interior_subset p.2⟩) =
      (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).homeo q.1)
    (hparent : levelFaceParent K s.1 =
      A.relativeOldTriangleParent C hC N anchorLines u) :
    A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u p.1 =
      levelFaceParentPlaneAffine K s.1
        ((K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).refined
          |>.facePlaneHomeomorph s.1 q).1 := by
  let Rlevel := K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))
  let pBase : {r : Plane // r ∈
      (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1} :=
    ⟨p.1, interior_subset (interior_mono htu p.2)⟩
  let z : standardTrianglePlaneComplex.support := Rlevel.refined.facePlaneHomeomorph s.1 q
  have hbase := A.relativeOldTriangleParentPlaneAffine_eq C hC N anchorLines u pBase
  have hlevel := levelFaceParentPlaneAffine_eq K s.1 z
  rw [K.facePlaneHomeomorph_val_eq_forwardAffine] at hbase hlevel
  have hqback : ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1 = q.1 :=
    congrArg Subtype.val ((Rlevel.refined.facePlaneHomeomorph s.1).symm_apply_apply q)
  have hlevel' : levelFaceParentPlaneAffine K s.1 z.1 =
      K.facePlaneForwardAffine (levelFaceParent K s.1) (Rlevel.homeo q.1).1 := by
    calc
      _ = K.facePlaneForwardAffine (levelFaceParent K s.1)
          (Rlevel.homeo ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1).1 := hlevel
      _ = _ := congrArg (K.facePlaneForwardAffine (levelFaceParent K s.1))
        (congrArg Subtype.val (congrArg Rlevel.homeo hqback))
  calc
    _ = K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
        (A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
          (A.relativeOldTrianglePoint C hC N anchorLines u pBase)).1 := hbase
    _ = K.facePlaneForwardAffine (levelFaceParent K s.1) (Rlevel.homeo q.1).1 := by
      rw [hparent]
      exact congrArg (K.facePlaneForwardAffine
        (A.relativeOldTriangleParent C hC N anchorLines u))
        (congrArg Subtype.val (hsourceEq.trans hqSource))
    _ = _ := hlevel'.symm

private theorem exists_levelFace_of_alignedRelativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle) :
    ∃ s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
        s ∈ A.levelFaces (A.tilesMeeting C hC)},
      ∀ (p : Plane)
        (hp : p ∈ (A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1),
        A.tileFacesMeetingRelativeSourceEmbed C hC N
            (alignedRelativeExtraLines A C hC N anchorLines)
            (A.relativeOldTrianglePoint C hC N
              (alignedRelativeExtraLines A C hC N anchorLines) t ⟨p, hp⟩) ∈
          K.levelFaceCarrier s.1 := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let selectedLevelFaces := A.levelFaces (A.tilesMeeting C hC)
  let Rlevel := K.safeSubdivision n
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let alignmentLines := A.relativeLevelAlignmentLines C hC N anchorLines n
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let J := A.tileFacePolygonMeeting C hC
  let source₁ := A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  obtain ⟨u, s, htu, p, q, hsourceEq, hqSource, hparent⟩ :=
    exists_alignedRelativeOldTriangle_parentWitness A C hC N anchorLines t
  let F := A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u
  let z : standardTrianglePlaneComplex.support :=
    Rlevel.refined.facePlaneHomeomorph s.1 q
  have hplaneAtP : F p.1 = levelFaceParentPlaneAffine K s.1 z.1 :=
    alignedRelativeOldTriangle_planeAt_parentWitness
      A C hC N anchorLines t u s htu p q hsourceEq hqSource hparent
  have hmono (k : Fin 3) :
      localOldMesh.IsMonochromatic
        ((levelFaceParentCoord K s.1 k).comp F) := by
    have haAlign :
        (levelFaceParentCoord K s.1 k).comp F ∈
          alignmentLines := by
      exact A.relativeLevelAlignmentLine_mem
        C hC N anchorLines n u s.1 hparent k
    have haExtra :
        (levelFaceParentCoord K s.1 k).comp F ∈
          extraLines :=
      List.mem_append_right _ haAlign
    have haLines :
        (levelFaceParentCoord K s.1 k).comp F ∈ lines :=
      List.mem_append_right _ haExtra
    have haAll :
        (levelFaceParentCoord K s.1 k).comp F ∈
          N.coordinateLines ++ lines :=
      List.mem_append_right _ haLines
    have hR :=
      (PolygonalFamily.arrangementMesh J
        ).refineByLines_isMonochromatic_of_mem
          (N.coordinateLines ++ lines) haAll
    intro w hw
    apply hR w
    exact
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp hw |>.1
  have hcoordAtP (k : Fin 3) :
      0 <
        ((levelFaceParentCoord K s.1 k).comp F) p.1 := by
    let a := (levelFaceParentCoord K s.1 k).comp F
    have hnonneg : 0 ≤ a p.1 := by
      change 0 ≤ levelFaceParentCoord K s.1 k (F p.1)
      rw [hplaneAtP]
      exact levelFaceParentCoord_nonneg K s.1 k z
    rcases hmono k t.1 t.2 with hpos | hneg
    · have hsub :
          localOldMesh.triangleCarrier t.1 ⊆ {r | 0 ≤ a r} := by
        apply convexHull_min
        · rintro r ⟨v, hv, rfl⟩
          exact hpos v hv
        · exact ((convex_Ici (0 : ℝ)).affine_preimage a)
      have hpHalf := interior_mono hsub p.2
      rw [TriangleMesh.interior_affine_nonneg_of_surjective a
        (A.relativeLevelAlignmentLine_surjective
          C hC N anchorLines u s.1 k)] at hpHalf
      exact hpHalf
    · have hsub :
          localOldMesh.triangleCarrier t.1 ⊆ {r | a r ≤ 0} := by
        apply convexHull_min
        · rintro r ⟨v, hv, rfl⟩
          exact hneg v hv
        · exact ((convex_Iic (0 : ℝ)).affine_preimage a)
      have hpHalf := interior_mono hsub p.2
      rw [TriangleMesh.interior_affine_nonpos_of_surjective a
        (A.relativeLevelAlignmentLine_surjective
          C hC N anchorLines u s.1 k)] at hpHalf
      exact False.elim ((not_lt_of_ge hnonneg) hpHalf)
  exact ⟨s, alignedRelativeOldTriangle_source_mem_levelFace
    A C hC N anchorLines t u s p.1 p.2 htu hparent hmono hcoordAtP⟩

private structure CrossingWeldStraighteningContext
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S)
    (T : PartialTriangulation S) (A : Set S) where
  C : Set S
  hCclosed : IsClosed C
  hAC : A ⊆ interior C
  hCT : C ⊆ interior T.support
  U : Set T.toIntrinsic.realization
  hU : IsOpen U
  V : Set Plane
  hV : IsOpen V
  Q : PartialTriangulation.PolygonalReplacementPresentation U V
  Qatlas : PartialTriangulation.PolygonalReplacementSourceAtlas T.toIntrinsic U V Q
  g' : U → c.kind.modelRegion
  g : T.toIntrinsic.realization → S
  hVsub : V ⊆ c.kind.perturbationRegion
  hVavoid : ∀ z : c.kind.modelRegion, (z : Plane) ∉ V → (c.chart.symm z).1 ∈ C
  hVprotected : ∀ y : T.chartOverlap c, T.embed y.1 ∈ C → T.chartOverlapMap c y ∉ V
  hUprotected : ∀ y : T.chartOverlap c, y.1 ∉ U → T.embed y.1 ∈ C
  hgcoord : ∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1
  hUsub : U ⊆ T.chartOverlap c
  hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1
  hgfix : ∀ x, T.embed x ∈ C → g x = T.embed x
  hgmatch : MatchesAtFrontier U g T.embed
  hgcont : ContinuousOn g U
  hginj : Set.InjOn g U
  hcross : Disjoint (g '' U) (T.embed '' Uᶜ)
  hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed)
  hBoundaryPreservation : PreservesManifoldBoundary S (frontierGlue U g T.embed) T.embed

private noncomputable abbrev CrossingWeldStraighteningContext.adjusted
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S}
    {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : PartialTriangulation S :=
  T.replaceOnOpen W.U W.g W.hembed

private noncomputable def CrossingWeldStraighteningContext.remainder
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : Set S :=
  c.core \ interior W.adjusted.support

private noncomputable def CrossingWeldStraighteningContext.remainderToDomain
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : W.remainder → c.domain :=
  fun x ↦ ⟨x.1, c.core_subset_domain x.2.1⟩

private noncomputable def CrossingWeldStraighteningContext.remainderModel
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : W.remainder → c.kind.modelRegion :=
  fun x ↦ c.chart (W.remainderToDomain x)

private noncomputable def CrossingWeldStraighteningContext.remainderCoordinate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : W.remainder → Plane :=
  fun x ↦ W.remainderModel x

-- The compact chart patch and its adaptive source neighborhood form the first persistent stage.
private structure CrossingWeldPatchContext
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S) (T : PartialTriangulation S) (A : Set S) where
  straightening : CrossingWeldStraighteningContext S c T A
  N : TriangleMesh
  hN_V : N.toPlaneComplex.support ⊆ straightening.V
  hN_patch : N.toPlaneComplex.support ⊆ c.kind.patchComplex.support
  hRemainderInterior : Set.range straightening.remainderModel ⊆
    interior {p : c.kind.modelRegion | (p : Plane) ∈ N.toPlaneComplex.support}
  CN : Set straightening.V
  hCN_support : CN = {p : straightening.V | p.1 ∈ N.toPlaneComplex.support}
  hCNcompact : IsCompact CN
  hN_arrangement : N.toPlaneComplex.support ⊆
    (PolygonalFamily.arrangementMesh
      (straightening.Qatlas.tileFacePolygonMeeting CN hCNcompact)).toPlaneComplex.support
  hN_model : N.toPlaneComplex.support ⊆ c.kind.modelRegion
  hA_adjusted : A ⊆ interior straightening.adjusted.support

omit [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
-- A boundary-faithful chart core protected by the old support stays interior after the
-- frontier-glued straightening.  The two manifold strata require different local arguments.

omit [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
-- A compact part of the chart model has a finite patch submesh whose relative interior covers it.

private noncomputable def ChartInductionGeometry.n
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : ℕ :=
  P.straightening.Qatlas.commonLevel
    (P.straightening.Qatlas.tilesMeeting P.CN P.hCNcompact)

private noncomputable def ChartInductionGeometry.subdivision
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : T.toIntrinsic.Subdivision :=
  T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)

private noncomputable def ChartInductionGeometry.selectedFaces
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :=
  P.straightening.Qatlas.levelFaces
    (P.straightening.Qatlas.tilesMeeting P.CN P.hCNcompact)

private noncomputable def ChartInductionGeometry.extraLines
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) :=
  alignedRelativeExtraLines P.straightening.Qatlas P.CN P.hCNcompact
    P.N anchorLines

private noncomputable def ChartInductionGeometry.localComplex
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) :=
  P.straightening.Qatlas.tileFacesMeetingRelativeSourceComplex
    P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P anchorLines)

private noncomputable def ChartInductionGeometry.source
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) :
    (ChartInductionGeometry.localComplex P anchorLines).realization →
      T.toIntrinsic.realization :=
  P.straightening.Qatlas.tileFacesMeetingRelativeSourceEmbed
    P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P anchorLines)

@[simp]
private theorem ChartInductionGeometry.source_apply
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (x : (ChartInductionGeometry.localComplex P anchorLines).realization) :
    ChartInductionGeometry.source P anchorLines x =
      P.straightening.Qatlas.tileFacesMeetingRelativeSourceEmbed
        P.CN P.hCNcompact P.N
          (ChartInductionGeometry.extraLines P anchorLines) x := rfl

private structure ChartInductionGeometry
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S) (T : PartialTriangulation S) (A : Set S)
    (P : CrossingWeldPatchContext S c T A) where
  anchorLines : List (Plane →ᵃ[ℝ] ℝ)
  localFaceParent :
    (ChartInductionGeometry.localComplex P anchorLines).Face →
      {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P}
  localVertexPoint :
    (ChartInductionGeometry.localComplex P anchorLines).UsedVertex →
      (ChartInductionGeometry.subdivision P).refined.realization
  localVertexPoint_injective : Function.Injective localVertexPoint
  localVertex_source : ∀ u,
    ChartInductionGeometry.source P anchorLines
        ((ChartInductionGeometry.localComplex P anchorLines).vertexPoint u) =
      (ChartInductionGeometry.subdivision P).homeo (localVertexPoint u)
  source_injective : Function.Injective (ChartInductionGeometry.source P anchorLines)
  localFaceMap_val : ∀
      (t : (ChartInductionGeometry.localComplex P anchorLines).Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}),
    ((ChartInductionGeometry.subdivision P).homeo.symm
      (ChartInductionGeometry.source P anchorLines
        ((ChartInductionGeometry.localComplex P anchorLines).faceStandardMap t x))).1 =
      ∑ v : {v // v ∈ t.1}, x v •
        (localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1
  source_range : Set.range (ChartInductionGeometry.source P anchorLines) =
    ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P},
      T.toIntrinsic.levelFaceCarrier s.1
  subdivision_surface :
    (ChartInductionGeometry.subdivision P).refined.HasSurfaceEdgeValence

private abbrev ChartInductionGeometry.LevelAnchor
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :=
  Σ u : {u : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
      u ∈ ChartInductionGeometry.selectedFaces P},
    Sum {v // v ∈ u.1.1} (ZMod 3)

private noncomputable instance ChartInductionGeometry.levelAnchorFintype
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    Fintype (ChartInductionGeometry.LevelAnchor P) := by
  classical
  unfold ChartInductionGeometry.LevelAnchor
  infer_instance

private noncomputable def ChartInductionGeometry.anchorLevelPoint
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    ChartInductionGeometry.LevelAnchor P →
      (ChartInductionGeometry.subdivision P).refined.realization :=
  fun a ↦ match a.2 with
    | Sum.inl v => (ChartInductionGeometry.subdivision P).refined.facePoint a.1.1 v
    | Sum.inr i => (ChartInductionGeometry.subdivision P).refined.edgePath
        ((ChartInductionGeometry.subdivision P).refined.faceEdge a.1.1 i)
        ⟨1 / 2, by constructor <;> norm_num⟩

private noncomputable def ChartInductionGeometry.anchorSourcePoint
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    ChartInductionGeometry.LevelAnchor P → T.toIntrinsic.realization :=
  fun a ↦ (ChartInductionGeometry.subdivision P).homeo
    (ChartInductionGeometry.anchorLevelPoint P a)

private theorem ChartInductionGeometry.anchorSourcePoint_mem_selected
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (a : ChartInductionGeometry.LevelAnchor P) :
    ChartInductionGeometry.anchorSourcePoint P a ∈
      ⋃ u : {u : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          u ∈ ChartInductionGeometry.selectedFaces P},
        T.toIntrinsic.levelFaceCarrier u.1 := by
  rcases a with ⟨s, v | i⟩
  · apply Set.mem_iUnion.mpr
    refine ⟨s, (ChartInductionGeometry.subdivision P).refined.facePoint s.1 v, ?_, rfl⟩
    exact (ChartInductionGeometry.subdivision P).refined.facePoint_mem_faceCarrier s.1 v
  · let edgeHalf : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
    have hedge : (ChartInductionGeometry.subdivision P).refined.edgePath
        ((ChartInductionGeometry.subdivision P).refined.faceEdge s.1 i) edgeHalf ∈
      (ChartInductionGeometry.subdivision P).refined.faceCarrier
        ((ChartInductionGeometry.subdivision P).refined.faceEdge s.1 i).1 := by
      rw [← (ChartInductionGeometry.subdivision P).refined.range_edgePath]
      exact ⟨edgeHalf, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨s, (ChartInductionGeometry.subdivision P).refined.edgePath
      ((ChartInductionGeometry.subdivision P).refined.faceEdge s.1 i) edgeHalf, ?_, rfl⟩
    intro v hv
    exact hedge v (fun hve ↦ hv
      ((ChartInductionGeometry.subdivision P).refined.faceEdge_subset_face s.1 i hve))

private theorem ChartInductionGeometry.anchorSourcePoint_mem_open
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (a : ChartInductionGeometry.LevelAnchor P) :
    ChartInductionGeometry.anchorSourcePoint P a ∈ P.straightening.U := by
  apply P.straightening.Qatlas.sourceTileFacesMeeting_subset_open P.CN P.hCNcompact
  rw [P.straightening.Qatlas.sourceTileFacesMeeting_eq_levelFaces P.CN P.hCNcompact]
  exact ChartInductionGeometry.anchorSourcePoint_mem_selected P a

private noncomputable def ChartInductionGeometry.anchorCoordinate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : ChartInductionGeometry.LevelAnchor P → Plane :=
  fun a ↦ (P.straightening.Q.sourceHomeomorph
    ⟨ChartInductionGeometry.anchorSourcePoint P a,
      ChartInductionGeometry.anchorSourcePoint_mem_open P a⟩).1.1

private noncomputable def ChartInductionGeometry.canonicalAnchorLines
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : List (Plane →ᵃ[ℝ] ℝ) :=
  PartialTriangulation.PolygonalReplacementSourceAtlas.coordinateAnchorLines
    (ChartInductionGeometry.anchorCoordinate P)

private noncomputable def ChartInductionGeometry.canonicalLocalFaceParent
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face) :
    {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
      s ∈ ChartInductionGeometry.selectedFaces P} :=
  Classical.choose (exists_levelFace_of_alignedRelativeOldTriangle
    P.straightening.Qatlas P.CN P.hCNcompact P.N
      (ChartInductionGeometry.canonicalAnchorLines P)
    (⟨t.1, t.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
      P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
        (ChartInductionGeometry.canonicalAnchorLines P))).Triangle))

private theorem ChartInductionGeometry.canonicalLocalFaceParent_contains
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (p : Plane)
    (hp : p ∈ (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
      P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
        (ChartInductionGeometry.canonicalAnchorLines P))).triangleCarrier t.1) :
    ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
        (P.straightening.Qatlas.relativeOldTrianglePoint P.CN P.hCNcompact P.N
          (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
          (⟨t.1, t.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
            P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
              (ChartInductionGeometry.canonicalAnchorLines P))).Triangle) ⟨p, hp⟩) ∈
      T.toIntrinsic.levelFaceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P t).1 :=
  Classical.choose_spec (exists_levelFace_of_alignedRelativeOldTriangle
    P.straightening.Qatlas P.CN P.hCNcompact P.N
      (ChartInductionGeometry.canonicalAnchorLines P)
      (⟨t.1, t.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
        P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
          (ChartInductionGeometry.canonicalAnchorLines P))).Triangle)) p hp

private theorem ChartInductionGeometry.canonicalLocalFaceParent_contains_realization
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (x : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).realization)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P) x ∈
      T.toIntrinsic.levelFaceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P t).1 := by
  let localOldMesh := P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
    P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
  let p : Plane := localOldMesh.coordinateEmbed x
  have hp : p ∈ localOldMesh.triangleCarrier t.1 := by
    apply localOldMesh.toPlaneComplex.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  let y := P.straightening.Qatlas.relativeOldTrianglePoint P.CN P.hCNcompact P.N
    (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
    (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩
  have hyx : y = x := by
    apply localOldMesh.isEmbedding_coordinateEmbed.injective
    rw [P.straightening.Qatlas.relativeOldTrianglePoint_coordinateEmbed
      P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
      (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩]
  rw [← hyx]
  exact ChartInductionGeometry.canonicalLocalFaceParent_contains P t p hp

private noncomputable def ChartInductionGeometry.canonicalLocalVertexPoint
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).UsedVertex →
      (ChartInductionGeometry.subdivision P).refined.realization :=
  fun v ↦ (ChartInductionGeometry.subdivision P).homeo.symm
    (P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
      P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P)) v)

private theorem ChartInductionGeometry.canonicalLocalVertexPoint_mem_face
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face) (v : {v // v ∈ t.1}) :
    ChartInductionGeometry.canonicalLocalVertexPoint P ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
      (ChartInductionGeometry.subdivision P).refined.faceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P t).1.1 := by
  let localComplex := ChartInductionGeometry.localComplex P
    (ChartInductionGeometry.canonicalAnchorLines P)
  let uv : localComplex.UsedVertex := ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
  let xv : localComplex.realization := localComplex.vertexPoint uv
  have hxv : ∀ w ∉ t.1, xv.1 w = 0 := by
    intro w hw
    change Pi.single v.1 1 w = 0
    have hwv : w ≠ v.1 := fun h ↦ hw (h ▸ v.2)
    simp [hwv]
  obtain ⟨q, hq, hqeq⟩ :=
    ChartInductionGeometry.canonicalLocalFaceParent_contains_realization P t xv hxv
  have hlocal : (ChartInductionGeometry.subdivision P).homeo
      (ChartInductionGeometry.canonicalLocalVertexPoint P uv) =
        ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P) xv :=
    (ChartInductionGeometry.subdivision P).homeo.apply_symm_apply _
  have heq : ChartInductionGeometry.canonicalLocalVertexPoint P uv = q :=
    (ChartInductionGeometry.subdivision P).homeo.injective (hlocal.trans hqeq.symm)
  rwa [heq]

private theorem ChartInductionGeometry.canonicalSource_isEmbedding
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    _root_.Topology.IsEmbedding
      (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)) :=
  P.straightening.Qatlas.isEmbedding_tileFacesMeetingRelativeSourceEmbed
    P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))

private theorem ChartInductionGeometry.canonicalLocalFaceMap_val
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (x : stdSimplex ℝ {v // v ∈ t.1}) :
    ((ChartInductionGeometry.subdivision P).homeo.symm
      (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
        ((ChartInductionGeometry.localComplex P
          (ChartInductionGeometry.canonicalAnchorLines P)).faceStandardMap t x))).1 =
      ∑ v : {v // v ∈ t.1}, x v •
        (ChartInductionGeometry.canonicalLocalVertexPoint P
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 := by
  let Rlevel := ChartInductionGeometry.subdivision P
  let localComplex := ChartInductionGeometry.localComplex P
    (ChartInductionGeometry.canonicalAnchorLines P)
  let source₁ := ChartInductionGeometry.source P
    (ChartInductionGeometry.canonicalAnchorLines P)
  let localVertexLevelPoint := ChartInductionGeometry.canonicalLocalVertexPoint P
  let localFaceLevelFace := ChartInductionGeometry.canonicalLocalFaceParent P
  apply subdivision_preimage_faceMap_eq_vertex_sum
    Rlevel source₁ localVertexLevelPoint (fun u ↦ (localFaceLevelFace u).1)
  · exact fun u ↦ Rlevel.homeo.apply_symm_apply _
  · exact ChartInductionGeometry.canonicalLocalVertexPoint_mem_face P
  · intro u y
    let yg : localComplex.realization := localComplex.faceStandardMap u y
    have hyg : ∀ v ∉ u.1, yg.1 v = 0 := by
      intro v hv
      rw [localComplex.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem u.1 y hv
    obtain ⟨q, hq, hqeq⟩ :=
      ChartInductionGeometry.canonicalLocalFaceParent_contains_realization P u yg hyg
    have hyq : Rlevel.homeo.symm (source₁ yg) = q := by
      change (T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo.symm
        (ChartInductionGeometry.source P
          (ChartInductionGeometry.canonicalAnchorLines P) yg) = q
      calc
        _ = (T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo.symm
            ((T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo q) :=
          congrArg
            (T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo.symm hqeq.symm
        _ = q :=
          (T.toIntrinsic.safeSubdivision
            (ChartInductionGeometry.n P)).homeo.symm_apply_apply q
    rwa [hyq]
  · intro u y
    let yg : localComplex.realization := localComplex.faceStandardMap u y
    have hyg : ∀ v ∉ u.1, yg.1 v = 0 := by
      intro v hv
      rw [localComplex.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem u.1 y hv
    change (ChartInductionGeometry.source P
      (ChartInductionGeometry.canonicalAnchorLines P) yg).1 = _
    dsimp only [ChartInductionGeometry.source, source₁]
    rw [P.straightening.Qatlas.relativeSourceFaceMap_eq_vertex_sum
      P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
      (⟨u.1, u.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
        P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
          (ChartInductionGeometry.canonicalAnchorLines P))).Triangle) yg hyg]
    apply Finset.sum_congr rfl
    intro v _
    have hcoord : yg.1 v.1 = y v := by
      rw [show yg.1 = extendFaceCoordinates u.1 y from localComplex.faceStandardMap_val u y,
        extendFaceCoordinates_of_mem u.1 y v.2]
      exact congrArg y (Subtype.ext rfl)
    rw [hcoord]
    rfl

private theorem ChartInductionGeometry.canonicalLocalVertexPoint_injective
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    Function.Injective (ChartInductionGeometry.canonicalLocalVertexPoint P) := by
  intro v w hvw
  let localComplex := ChartInductionGeometry.localComplex P
    (ChartInductionGeometry.canonicalAnchorLines P)
  apply localComplex.injective_vertexPoint
  apply (ChartInductionGeometry.canonicalSource_isEmbedding P).injective
  change P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
      P.CN P.hCNcompact P.N
        (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P)) v =
    P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
      P.CN P.hCNcompact P.N
        (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P)) w
  have h := congrArg (ChartInductionGeometry.subdivision P).homeo hvw
  simpa only [ChartInductionGeometry.canonicalLocalVertexPoint,
    (ChartInductionGeometry.subdivision P).homeo.apply_symm_apply] using h

private noncomputable def ChartInductionGeometry.canonical
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    ChartInductionGeometry S c T A P where
  anchorLines := ChartInductionGeometry.canonicalAnchorLines P
  localFaceParent := ChartInductionGeometry.canonicalLocalFaceParent P
  localVertexPoint := ChartInductionGeometry.canonicalLocalVertexPoint P
  localVertexPoint_injective := ChartInductionGeometry.canonicalLocalVertexPoint_injective P
  localVertex_source := fun _ ↦
    (ChartInductionGeometry.subdivision P).homeo.apply_symm_apply _ |>.symm
  source_injective := (ChartInductionGeometry.canonicalSource_isEmbedding P).injective
  localFaceMap_val := ChartInductionGeometry.canonicalLocalFaceMap_val P
  source_range := P.straightening.Qatlas.range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces
    P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
  subdivision_surface := by
    apply T.toIntrinsic.hasSurfaceEdgeValence_iteratedMidpointSubdivision
    exact fun e he ↦ hT.combSurface e he

private noncomputable def ChartInductionGeometry.localVertexPoints
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  (Finset.univ : Finset (ChartInductionGeometry.localComplex P G.anchorLines).UsedVertex
    ).image G.localVertexPoint

private noncomputable def ChartInductionGeometry.edgeMidpointPoints
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (_G : ChartInductionGeometry S c T A P) :=
  (Finset.univ : Finset (ChartInductionGeometry.subdivision P).refined.Edge).image
    (fun e ↦ (ChartInductionGeometry.subdivision P).refined.edgePath e
      ⟨1 / 2, by constructor <;> norm_num⟩)

private noncomputable def ChartInductionGeometry.marking
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  IntrinsicTwoComplex.EdgeMarking.ofFinset
    (ChartInductionGeometry.subdivision P).refined
    (G.localVertexPoints ∪ G.edgeMidpointPoints)

@[reducible]
private noncomputable def ChartInductionGeometry.mixedData
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) : MixedLocalFanData where
  ambient := (ChartInductionGeometry.subdivision P).refined
  localComplex := ChartInductionGeometry.localComplex P G.anchorLines
  marking := G.marking
  isOutside := fun f ↦ f.1 ∉ ChartInductionGeometry.selectedFaces P
  isOutside_decidable := fun _ ↦ Classical.propDecidable _
  localVertexPoint := G.localVertexPoint
  localVertexPoint_injective := G.localVertexPoint_injective
  localFaceMap := fun t x ↦ (ChartInductionGeometry.subdivision P).homeo.symm
    (ChartInductionGeometry.source P G.anchorLines
      ((ChartInductionGeometry.localComplex P G.anchorLines).faceStandardMap t x))

private noncomputable def ChartInductionGeometry.lines
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  P.straightening.Qatlas.tileFaceMeetingLines P.CN P.hCNcompact P.N
    (ChartInductionGeometry.extraLines P G.anchorLines)

private noncomputable def ChartInductionGeometry.targetMesh
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  PartialTriangulation.RelativeSynchronizedTarget.newMesh
    (P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact)
    P.N G.lines

private noncomputable def ChartInductionGeometry.targetEmbed
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :
    GeometricRealization G.targetMesh.Vertex G.targetMesh.triangles → S :=
  PartialTriangulation.RelativeSynchronizedTarget.newSurfaceEmbed c
    (P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact)
    P.N G.lines P.hN_arrangement P.hN_model

private noncomputable def ChartInductionGeometry.mixedOldComplex
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P)
    (C : MixedLocalFanCertificate G.mixedData) := C.mixedOldComplex G.mixedData

private noncomputable def ChartInductionGeometry.oldEmbed
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P)
    (C : MixedLocalFanCertificate G.mixedData) :
      (C.mixedOldComplex G.mixedData).compactIntrinsic.realization → S :=
  fun x ↦ P.straightening.adjusted.embed
    ((ChartInductionGeometry.subdivision P).homeo
      (G.mixedOldComplex C |>.compactEval x))

private structure ChartInductionFinishContext
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S) (T : PartialTriangulation S) (A : Set S)
    (P : CrossingWeldPatchContext S c T A) where
  geometry : ChartInductionGeometry S c T A P
  chart_boundary : c.BoundaryFaithful
  triangulation_boundary : T.BoundaryFacewiseRegular
  certificate : MixedLocalFanCertificate geometry.mixedData
  fan_surface :
    geometry.marking.markedFanLocallyFiniteTriangleComplex.compactIntrinsic
      |>.HasSurfaceEdgeValence
  selectedFace_of_fanInterval_endpoints_local :
    ∀ (f : geometry.mixedData.OutsideFanFace),
      geometry.marking.edgeIntervalFirst
          ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1)
          f.1.2.2 ∈ geometry.localVertexPoints →
      geometry.marking.edgeIntervalSecond
          ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1)
          f.1.2.2 ∈ geometry.localVertexPoints →
      ∃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          s ∈ ChartInductionGeometry.selectedFaces P},
        ((ChartInductionGeometry.subdivision P).refined.faceEdge
          f.1.1 f.1.2.1).1 ⊆ s.1.1

private noncomputable def ChartInductionFinishContext.fanSelectionData
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (F : ChartInductionFinishContext S c T A P) : MixedFanSelectionData F.geometry.mixedData := by
  classical
  let G := F.geometry
  let M := G.mixedData
  let R := ChartInductionGeometry.subdivision P
  exact {
    selectedSet := {p | R.homeo p ∈
      ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          s ∈ ChartInductionGeometry.selectedFaces P},
        T.toIntrinsic.levelFaceCarrier s.1}
    localVertex_mem_selected := by
      intro u
      change R.homeo (G.localVertexPoint u) ∈
        ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
            s ∈ ChartInductionGeometry.selectedFaces P},
          T.toIntrinsic.levelFaceCarrier s.1
      rw [← G.source_range]
      refine ⟨M.localComplex.vertexPoint u, ?_⟩
      exact G.localVertex_source u
    baseEdge_mem_selected := by
      intro f p hp ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩
      have hfirstLocal :
          (M.marking.fanFirstVertex f.1).1 ∈ G.localVertexPoints := by
        rw [← hu₀]
        exact Finset.mem_image.mpr ⟨u₀, Finset.mem_univ u₀, rfl⟩
      have hsecondLocal :
          (M.marking.fanSecondVertex f.1).1 ∈ G.localVertexPoints := by
        rw [← hu₁]
        exact Finset.mem_image.mpr ⟨u₁, Finset.mem_univ u₁, rfl⟩
      obtain ⟨s, hes⟩ :=
        F.selectedFace_of_fanInterval_endpoints_local f hfirstLocal hsecondLocal
      apply Set.mem_iUnion.mpr
      refine ⟨s, p, ?_, rfl⟩
      intro v hv
      exact hp v (fun hve ↦ hv (hes hve)) }

private structure MixedLocalBarycentricCertificate
    (M : MixedLocalFanData) (parentFace : M.localComplex.Face → M.ambient.Face) where
  localMixedFaceMap_mem_parent : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}),
    M.mixedOldFaceMap (Sum.inl t) x ∈ M.ambient.faceCarrier (parentFace t).1
  localVertexPoint_mem_marking : ∀ v : M.localComplex.UsedVertex,
    M.localVertexPoint v ∈ M.marking.points
  positive_localVertex_mem_edge : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}) (e : M.ambient.Edge),
    M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
      ∀ (v : {v // v ∈ t.1}), 0 < x v →
        M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ M.ambient.faceCarrier e.1
  localFace_edgeParameter_eq_sum : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}) (e : M.ambient.Edge),
    M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
      M.marking.edgeParameterValue e (M.localFaceMap t x) =
        ∑ v : {v // v ∈ t.1}, x v * M.marking.edgeParameterValue e
          (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)

omit [T2Space S] [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- Shared finite Radó induction assembler.  It turns any clean one-chart absorption step with the
full `RadoInvariant` conclusion into an end-to-end geometric triangulation.
@isnad1 id=nonempty.1h1v.s6.e4e5be2a9f72 from=translated src=- shape=7c603002 vocab=41f0752e
-/
theorem moise_triangulation_of_induction
    (hstep : ∀ (c : MoiseChart S), c.BoundaryFaithful →
      ∀ {T : PartialTriangulation S} {A : Set S}, RadoInvariant T A →
        ∃ T' : PartialTriangulation S, RadoInvariant T' (A ∪ c.core)) :
    Nonempty (GeometricTriangulation S) := by
  classical
  obtain ⟨m, charts, hcover, hbd⟩ := moise_finite_chart_cover S
  -- Absorb the first `k` cores.
  have Hrec : ∀ k : ℕ,
      ∃ T : PartialTriangulation S,
        RadoInvariant T (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
    intro k
    induction k with
    | zero =>
        refine ⟨PartialTriangulation.empty S, ?_⟩
        have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < 0), (charts i).core) = (∅ : Set S) := by
          simp
        rw [hA]
        exact radoInvariant_empty S
    | succ k ih =>
        rcases ih with ⟨T, hT⟩
        by_cases hk : k < m
        · obtain ⟨T', hT'⟩ :=
            hstep (charts ⟨k, hk⟩) (hbd ⟨k, hk⟩) hT
          refine ⟨T', ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) ∪
                (charts ⟨k, hk⟩).core := by
            ext x
            simp only [Set.mem_iUnion, Set.mem_union]
            constructor
            · rintro ⟨i, hik, hx⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hik' | hik'
              · exact Or.inl ⟨i, hik', hx⟩
              · refine Or.inr ?_
                have : i = ⟨k, hk⟩ := Fin.ext hik'
                rwa [← this]
            · rintro (⟨i, hik, hx⟩ | hx)
              · exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
              · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩
          rw [hA]
          exact hT'
        · refine ⟨T, ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
            ext x
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨i, hik, hx⟩
              have : (i : ℕ) < k := by
                have := i.isLt
                omega
              exact ⟨i, this, hx⟩
            · rintro ⟨i, hik, hx⟩
              exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
          rw [hA]
          exact hT
  obtain ⟨T, hT⟩ := Hrec m
  have hall : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < m), (charts i).core) = Set.univ := by
    rw [← hcover]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i, i.isLt, hx⟩
  have hsupport : T.support = Set.univ := by
    have huniv : (Set.univ : Set S) ⊆ T.support := by
      rw [← hall]
      exact hT.coresCovered
    exact Set.eq_univ_of_univ_subset huniv
  exact ⟨T.toGeometricTriangulation hsupport⟩

end EvalHypotheses

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
