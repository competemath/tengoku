/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphApproximation
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.ConeExtension

/-!
# Finite PL models for intrinsic graph replacements

This file turns the topological polygonal paths constructed in
`IntrinsicGraphApproximation` into finite plane complexes.  The first step isolates the portion
of the middle PL segment model between its two last-exit parameters.  Marking those parameters
in the source arrangement makes the closed subsegment an exact finite subcomplex.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}
  {e : K.Edge} (A : K.CentralPolygonalArc hcont hinj D C e)

/-! ## Piecewise-affine formulas on the intrinsic source edge -/

/-- On the first quarter-piece of Moise's concatenated parameterization, the intrinsic edge
replacement is the affine spoke from the first vertex image to the left exit point.
@isnad1 id=eq.4h6v.s10.eed961615e81 from=translated src=- shape=9b4fb863 vocab=ba55c883
-/
theorem edgeReplacementMap_eq_left {x : K.realization}
    (hx : x ∈ K.faceCarrier e.1)
    (ht : (K.edgeParameter e x hx : ℝ) ≤ (1 / 2 : ℝ)) :
    K.edgeReplacementMap hcont hinj D C e x =
      AffineMap.lineMap (h (K.edgeFirstPoint e))
        (K.replacementArc hcont hinj D C e).leftEndpoint
        (2 * (K.edgeParameter e x hx : ℝ)) := by
  let A := K.replacementArc hcont hinj D C e
  let first := Path.segment (h (K.edgeFirstPoint e)) A.leftEndpoint
  let tail := A.middlePath.trans
    (Path.segment A.rightEndpoint (h (K.edgeSecondPoint e)))
  rw [IntrinsicTwoComplex.edgeReplacementMap,
    ← K.edgeParameter_eq_secondCoordinate e x hx,
    show K.replacementArc hcont hinj D C e = A by rfl,
    show A.completePath = first.trans tail by rfl,
    Path.extend_trans_of_le_half first tail ht]
  have hp := (K.edgeParameter e x hx).2
  have h2t : 2 * (K.edgeParameter e x hx : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hp.1, hp.2]
  rw [Path.extend_apply first h2t]
  rfl

/-- On the middle quarter-piece, the intrinsic edge replacement is the finite PL segment model
evaluated at an affine function of the barycentric edge parameter.
@isnad1 id=eq.5h6v.s10.7b459946529a from=translated src=- shape=41b36b0b vocab=ecb079b8
-/
theorem edgeReplacementMap_eq_middle {x : K.realization}
    (hx : x ∈ K.faceCarrier e.1)
    (ht0 : (1 / 2 : ℝ) ≤ (K.edgeParameter e x hx : ℝ))
    (ht1 : (K.edgeParameter e x hx : ℝ) ≤ (3 / 4 : ℝ)) :
    K.edgeReplacementMap hcont hinj D C e x =
      (K.replacementArc hcont hinj D C e).parameterization.map
        (planePoint
          ((K.replacementArc hcont hinj D C e).data.resolvedWalk.length *
            ((K.replacementArc hcont hinj D C e).exitData.left +
              ((K.replacementArc hcont hinj D C e).exitData.right -
                (K.replacementArc hcont hinj D C e).exitData.left) *
              (4 * (K.edgeParameter e x hx : ℝ) - 2))) 0) := by
  let A := K.replacementArc hcont hinj D C e
  let first := Path.segment (h (K.edgeFirstPoint e)) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (h (K.edgeSecondPoint e))
  have hp := (K.edgeParameter e x hx).2
  rw [IntrinsicTwoComplex.edgeReplacementMap,
    ← K.edgeParameter_eq_secondCoordinate e x hx,
    show K.replacementArc hcont hinj D C e = A by rfl,
    show A.completePath = first.trans (A.middlePath.trans last) by rfl,
    Path.extend_trans_of_half_le first (A.middlePath.trans last) ht0]
  have hinner : 2 * (K.edgeParameter e x hx : ℝ) - 1 ≤ (1 / 2 : ℝ) := by
    linarith
  rw [Path.extend_trans_of_le_half A.middlePath last hinner]
  have hu : 2 * (2 * (K.edgeParameter e x hx : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  rw [Path.extend_apply A.middlePath hu]
  change A.parameterization.curve
      (Path.segment A.exitData.left A.exitData.right
        ⟨2 * (2 * (K.edgeParameter e x hx : ℝ) - 1), hu⟩) = _
  rw [A.parameterization.curve_eq]
  have hscalar :
      (Path.segment A.exitData.left A.exitData.right
          ⟨2 * (2 * (K.edgeParameter e x hx : ℝ) - 1), hu⟩ : ℝ) =
        A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * (K.edgeParameter e x hx : ℝ) - 2) := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_eq_mul]
    ring
  rw [hscalar]

/-- On the final quarter-piece of Moise's concatenated parameterization, the intrinsic edge
replacement is the affine spoke from the right exit point to the second vertex image.
@isnad1 id=eq.4h6v.s10.37ce8e955c51 from=translated src=- shape=cb291571 vocab=f2eb94cc
-/
theorem edgeReplacementMap_eq_right {x : K.realization}
    (hx : x ∈ K.faceCarrier e.1)
    (ht : (3 / 4 : ℝ) ≤ (K.edgeParameter e x hx : ℝ)) :
    K.edgeReplacementMap hcont hinj D C e x =
      AffineMap.lineMap (K.replacementArc hcont hinj D C e).rightEndpoint
        (h (K.edgeSecondPoint e))
        (4 * (K.edgeParameter e x hx : ℝ) - 3) := by
  let A := K.replacementArc hcont hinj D C e
  let first := Path.segment (h (K.edgeFirstPoint e)) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (h (K.edgeSecondPoint e))
  have hp := (K.edgeParameter e x hx).2
  have houter : (1 / 2 : ℝ) ≤ (K.edgeParameter e x hx : ℝ) := by linarith
  rw [IntrinsicTwoComplex.edgeReplacementMap,
    ← K.edgeParameter_eq_secondCoordinate e x hx,
    show K.replacementArc hcont hinj D C e = A by rfl,
    show A.completePath = first.trans (A.middlePath.trans last) by rfl,
    Path.extend_trans_of_half_le first (A.middlePath.trans last) houter]
  have hinner : (1 / 2 : ℝ) ≤ 2 * (K.edgeParameter e x hx : ℝ) - 1 := by
    linarith
  rw [Path.extend_trans_of_half_le A.middlePath last hinner]
  have hu : 2 * (2 * (K.edgeParameter e x hx : ℝ) - 1) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2]
  rw [Path.extend_apply last hu]
  change AffineMap.lineMap A.rightEndpoint (h (K.edgeSecondPoint e))
      (2 * (2 * (K.edgeParameter e x hx : ℝ) - 1) - 1) = _
  congr 1
  ring

/-- The second barycentric coordinate of an intrinsic edge, as an ambient affine map. -/
noncomputable def edgeCoordinateAffine (K : IntrinsicTwoComplex) (e : K.Edge) :
    (K.Vertex → ℝ) →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (K.edgeSecond e)).toAffineMap

/--
@isnad1 id=eq.0h3v.s7.51b7fe0f6927 from=translated src=- shape=d357d6e1 vocab=d4bca1fc
-/
@[simp] theorem edgeCoordinateAffine_apply (K : IntrinsicTwoComplex) (e : K.Edge)
    (x : K.Vertex → ℝ) :
    K.edgeCoordinateAffine e x = x (K.edgeSecond e) := rfl

/-- The affine scalar which carries the middle quarter of an intrinsic source edge to the
horizontal source interval of its finite polygonal model. -/
noncomputable def edgeMiddleSourceScalarMap
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    (K.Vertex → ℝ) →ᵃ[ℝ] ℝ :=
  (A.data.resolvedWalk.length : ℝ) •
    (AffineMap.const ℝ (K.Vertex → ℝ) A.exitData.left +
      (A.exitData.right - A.exitData.left) •
        ((4 : ℝ) • K.edgeCoordinateAffine e -
          AffineMap.const ℝ (K.Vertex → ℝ) 2))

/-- The plane-valued affine middle-source map. -/
noncomputable def edgeMiddleSourceMap
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
  BrokenLineData.realAxisAffine.comp (edgeMiddleSourceScalarMap A)

/--
@isnad1 id=eq.2h7v.s10.6ee6ebf97e76 from=translated src=- shape=6e477679 vocab=2c0f24ec
-/
@[simp] theorem edgeMiddleSourceMap_apply
    (A : K.CentralPolygonalArc hcont hinj D C e) (x : K.Vertex → ℝ) :
    edgeMiddleSourceMap A x = planePoint
      (A.data.resolvedWalk.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * x (K.edgeSecond e) - 2))) 0 := by
  rfl

/-! ## The finite source breakpoint family -/

/-- The source-edge parameter corresponding to one vertex of the finite middle segment model,
before clamping to the middle quarter. -/
noncomputable def rawEdgeMiddleBreakpoint
    (A : K.CentralPolygonalArc hcont hinj D C e)
    (v : A.parameterization.source.Vertex) : ℝ :=
  (((A.parameterization.source.position v) 0 /
      A.data.resolvedWalk.length - A.exitData.left) /
      (A.exitData.right - A.exitData.left) + 2) / 4

/-- Clamp a middle-model breakpoint to the parameter interval on which the middle formula is
used. -/
noncomputable def edgeMiddleBreakpoint
    (A : K.CentralPolygonalArc hcont hinj D C e)
    (v : A.parameterization.source.Vertex) : ℝ :=
  max (1 / 2 : ℝ) (min (3 / 4 : ℝ) (rawEdgeMiddleBreakpoint A v))

/--
@isnad1 id=mem.2h7v.s7.67a9d1249920 from=translated src=- shape=c5ce4c5f vocab=6dfdc0f7
-/
theorem edgeMiddleBreakpoint_mem
    (A : K.CentralPolygonalArc hcont hinj D C e)
    (v : A.parameterization.source.Vertex) :
    edgeMiddleBreakpoint A v ∈ Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/--
@isnad1 id=eq.4h7v.s10.e82a1be2ef75 from=translated src=- shape=f0a7120d vocab=479cbfe7
-/
theorem edgeMiddleBreakpoint_eq_raw_of_mem
    (A : K.CentralPolygonalArc hcont hinj D C e)
    (v : A.parameterization.source.Vertex)
    (hv0 : A.exitData.left ≤
      A.parameterization.source.position v 0 / A.data.resolvedWalk.length)
    (hv1 : A.parameterization.source.position v 0 / A.data.resolvedWalk.length ≤
      A.exitData.right) :
    edgeMiddleBreakpoint A v = rawEdgeMiddleBreakpoint A v := by
  have hden : 0 < A.exitData.right - A.exitData.left :=
    sub_pos.mpr A.exitData.left_lt_right
  have hfrac0 : 0 ≤
      (A.parameterization.source.position v 0 / A.data.resolvedWalk.length -
        A.exitData.left) / (A.exitData.right - A.exitData.left) :=
    div_nonneg (sub_nonneg.mpr hv0) hden.le
  have hfrac1 :
      (A.parameterization.source.position v 0 / A.data.resolvedWalk.length -
        A.exitData.left) / (A.exitData.right - A.exitData.left) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith
  have hraw0 : (1 / 2 : ℝ) ≤ rawEdgeMiddleBreakpoint A v := by
    dsimp [rawEdgeMiddleBreakpoint]
    linarith
  have hraw1 : rawEdgeMiddleBreakpoint A v ≤ (3 / 4 : ℝ) := by
    dsimp [rawEdgeMiddleBreakpoint]
    linarith
  rw [edgeMiddleBreakpoint, min_eq_right hraw1, max_eq_right hraw0]

/--
@isnad1 id=eq.4h7v.s11.140303b748e4 from=translated src=- shape=5becbd3c vocab=114fda32
-/
theorem edgeMiddleSourceScalar_breakpoint
    (A : K.CentralPolygonalArc hcont hinj D C e)
    (v : A.parameterization.source.Vertex)
    (hv0 : A.exitData.left ≤
      A.parameterization.source.position v 0 / A.data.resolvedWalk.length)
    (hv1 : A.parameterization.source.position v 0 / A.data.resolvedWalk.length ≤
      A.exitData.right) :
    A.data.resolvedWalk.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * edgeMiddleBreakpoint A v - 2)) =
      A.parameterization.source.position v 0 := by
  rw [edgeMiddleBreakpoint_eq_raw_of_mem A v hv0 hv1]
  have hn : (A.data.resolvedWalk.length : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt A.resolvedWalk_length_pos)
  have hden : A.exitData.right - A.exitData.left ≠ 0 :=
    sub_ne_zero.mpr A.exitData.left_lt_right.ne'
  dsimp [rawEdgeMiddleBreakpoint]
  field_simp [hn, hden]
  ring

/-- All source breakpoints of one intrinsic replacement edge: the two spoke joins and every
vertex of the finite middle PL model. -/
abbrev EdgeBreakpoint (A : K.CentralPolygonalArc hcont hinj D C e) :=
  Option (Option A.parameterization.source.Vertex)

/-- The `edgeBreakpointParameter` declaration. -/
noncomputable def edgeBreakpointParameter
    (A : K.CentralPolygonalArc hcont hinj D C e) (b : EdgeBreakpoint A) : ℝ :=
  match b with
  | none => 1 / 2
  | some none => 3 / 4
  | some (some v) => edgeMiddleBreakpoint A v

/--
@isnad1 id=mem.2h7v.s7.62687ffe9a49 from=translated src=- shape=44727bdd vocab=894dadd9
-/
theorem edgeBreakpointParameter_mem
    (A : K.CentralPolygonalArc hcont hinj D C e) (b : EdgeBreakpoint A) :
    edgeBreakpointParameter A b ∈ Set.Icc (0 : ℝ) 1 := by
  rcases b with _ | _ | v
  · norm_num [edgeBreakpointParameter]
  · norm_num [edgeBreakpointParameter]
  · have hb := edgeMiddleBreakpoint_mem A v
    change edgeMiddleBreakpoint A v ∈ Set.Icc (0 : ℝ) 1
    constructor <;> linarith [hb.1, hb.2]

/-- The simultaneous intrinsic graph replacement is affine on any source subset contained in
the first spoke piece of one edge.
@isnad1 id=isaffine.4h6v.s8.bc0b3b90fd9a from=translated src=- shape=f08a65ff vocab=1408c5f0
-/
theorem graphReplacementMap_affineOn_left {E : Set K.realization}
    (hE : E ⊆ K.faceCarrier e.1)
    (hle : ∀ x ∈ E, x.1 (K.edgeSecond e) ≤ (1 / 2 : ℝ)) :
    K.IsAffineOnSet (K.graphReplacementMap hcont hinj D C) E := by
  let A := K.replacementArc hcont hinj D C e
  let scalar : (K.Vertex → ℝ) →ᵃ[ℝ] ℝ := (2 : ℝ) • K.edgeCoordinateAffine e
  let g : (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap (h (K.edgeFirstPoint e)) A.leftEndpoint).comp scalar
  refine ⟨g, ?_⟩
  intro x hx
  have hxe := hE hx
  have ht : (K.edgeParameter e x hxe : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [K.edgeParameter_eq_secondCoordinate e x hxe]
    exact hle x hx
  rw [K.graphReplacementMap_eq_edge hcont hinj D C e x hxe,
    edgeReplacementMap_eq_left (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      hxe ht, K.edgeParameter_eq_secondCoordinate e x hxe]
  rfl

/-- The simultaneous intrinsic graph replacement is affine on any source subset contained in
the final spoke piece of one edge.
@isnad1 id=isaffine.4h6v.s8.cb95060a9a27 from=translated src=- shape=5be6b380 vocab=1408c5f0
-/
theorem graphReplacementMap_affineOn_right {E : Set K.realization}
    (hE : E ⊆ K.faceCarrier e.1)
    (hge : ∀ x ∈ E, (3 / 4 : ℝ) ≤ x.1 (K.edgeSecond e)) :
    K.IsAffineOnSet (K.graphReplacementMap hcont hinj D C) E := by
  let A := K.replacementArc hcont hinj D C e
  let scalar : (K.Vertex → ℝ) →ᵃ[ℝ] ℝ :=
    (4 : ℝ) • K.edgeCoordinateAffine e - AffineMap.const ℝ (K.Vertex → ℝ) 3
  let g : (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap A.rightEndpoint (h (K.edgeSecondPoint e))).comp scalar
  refine ⟨g, ?_⟩
  intro x hx
  have hxe := hE hx
  have ht : (3 / 4 : ℝ) ≤ (K.edgeParameter e x hxe : ℝ) := by
    rw [K.edgeParameter_eq_secondCoordinate e x hxe]
    exact hge x hx
  rw [K.graphReplacementMap_eq_edge hcont hinj D C e x hxe,
    edgeReplacementMap_eq_right (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      hxe ht, K.edgeParameter_eq_secondCoordinate e x hxe]
  rfl

/-- A middle source piece is affine as soon as its affine source image lies in one face of the
finite segment model.  The named intrinsic edge subdivision will provide exactly this
hypothesis on each of its middle faces.
@isnad1 id=isaffine.6h6v.s10.afd16b9abd53 from=translated src=- shape=65952d54 vocab=ba7a815c
-/
theorem graphReplacementMap_affineOn_middle {E : Set K.realization}
    (hE : E ⊆ K.faceCarrier e.1)
    (hmid0 : ∀ x ∈ E, (1 / 2 : ℝ) ≤ x.1 (K.edgeSecond e))
    (hmid1 : ∀ x ∈ E, x.1 (K.edgeSecond e) ≤ (3 / 4 : ℝ))
    (hsource : ∃ s ∈ (K.replacementArc hcont hinj D C e).parameterization.source.simplexes,
      Set.MapsTo (fun x : K.realization =>
        edgeMiddleSourceMap (K.replacementArc hcont hinj D C e) x.1) E
        ((K.replacementArc hcont hinj D C e).parameterization.source.cellCarrier s)) :
    K.IsAffineOnSet (K.graphReplacementMap hcont hinj D C) E := by
  let A := K.replacementArc hcont hinj D C e
  obtain ⟨s, hs, hmaps⟩ := hsource
  obtain ⟨q, hq⟩ := A.parameterization.map_affineOn s hs
  refine ⟨q.comp (edgeMiddleSourceMap A), ?_⟩
  intro x hx
  have hxe := hE hx
  have ht0 : (1 / 2 : ℝ) ≤ (K.edgeParameter e x hxe : ℝ) := by
    rw [K.edgeParameter_eq_secondCoordinate e x hxe]
    exact hmid0 x hx
  have ht1 : (K.edgeParameter e x hxe : ℝ) ≤ (3 / 4 : ℝ) := by
    rw [K.edgeParameter_eq_secondCoordinate e x hxe]
    exact hmid1 x hx
  rw [K.graphReplacementMap_eq_edge hcont hinj D C e x hxe,
    edgeReplacementMap_eq_middle (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      hxe ht0 ht1,
    K.edgeParameter_eq_secondCoordinate e x hxe]
  exact hq (hmaps hx)

/-- The edgewise replacement map has exactly the complete polygonal replacement carrier as its
image.
@isnad1 id=eq.2h5v.s7.6c966ac446af from=translated src=- shape=0d986c67 vocab=987a832d
-/
theorem edgeReplacementMap_image_faceCarrier :
    K.edgeReplacementMap hcont hinj D C e '' K.faceCarrier e.1 =
      (K.replacementArc hcont hinj D C e).completeCarrier := by
  let A := K.replacementArc hcont hinj D C e
  rw [← A.range_completePath]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨K.edgeParameter e x hx, ?_⟩
    exact (K.edgeReplacementMap_eq_path hcont hinj D C e x hx).symm
  · rintro y ⟨t, rfl⟩
    let x := K.edgePath e t
    have hx : x ∈ K.faceCarrier e.1 := by
      rw [← K.range_edgePath e]
      exact ⟨t, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [K.edgeReplacementMap_eq_path hcont hinj D C e x hx]
    congr 1
    apply K.injective_edgePath e
    exact K.edgePath_edgeParameter e x hx

/-- The simultaneous graph replacement has the same exact edge image as the edgewise formula.
@isnad1 id=eq.2h5v.s7.f5ee46349e77 from=translated src=- shape=e64ade04 vocab=8bdf256e
-/
theorem graphReplacementMap_image_faceCarrier :
    K.graphReplacementMap hcont hinj D C '' K.faceCarrier e.1 =
      (K.replacementArc hcont hinj D C e).completeCarrier := by
  rw [← K.edgeReplacementMap_image_faceCarrier
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) (e := e)]
  apply Set.image_congr
  intro x hx
  exact K.graphReplacementMap_eq_edge hcont hinj D C e x hx

namespace CentralPolygonalArc

/-- The `leftSourcePoint` declaration. -/
noncomputable def leftSourcePoint : Plane :=
  planePoint (A.data.resolvedWalk.length * A.exitData.left) 0

/-- The `rightSourcePoint` declaration. -/
noncomputable def rightSourcePoint : Plane :=
  planePoint (A.data.resolvedWalk.length * A.exitData.right) 0

/--
@isnad1 id=mem.2h6v.s7.514c55c6918b from=translated src=- shape=dabdb257 vocab=2b3d441e
-/
theorem leftSourcePoint_mem_source : A.leftSourcePoint ∈ A.parameterization.source.support := by
  rw [A.parameterization.source_support, segment_eq_image_lineMap]
  refine ⟨A.exitData.left, ⟨A.exitData.left_nonneg,
    A.exitData.left_lt_right.le.trans A.exitData.right_le_one⟩, ?_⟩
  ext i
  fin_cases i <;>
    simp [leftSourcePoint, planePoint, AffineMap.lineMap_apply_module]; ring

/--
@isnad1 id=mem.2h6v.s7.92468669dc18 from=translated src=- shape=dabdb257 vocab=4b1aadb0
-/
theorem rightSourcePoint_mem_source : A.rightSourcePoint ∈ A.parameterization.source.support := by
  rw [A.parameterization.source_support, segment_eq_image_lineMap]
  refine ⟨A.exitData.right, ⟨A.exitData.left_nonneg.trans
    A.exitData.left_lt_right.le, A.exitData.right_le_one⟩, ?_⟩
  ext i
  fin_cases i <;>
    simp [rightSourcePoint, planePoint, AffineMap.lineMap_apply_module]; ring

/--
@isnad1 id=ne.2h6v.s7.bc62b7e95abc from=translated src=- shape=b17eedcb vocab=200bce78
-/
theorem leftSourcePoint_ne_rightSourcePoint : A.leftSourcePoint ≠ A.rightSourcePoint := by
  intro hp
  have hcoord := congrArg (fun p : Plane => p 0) hp
  have hn : (0 : ℝ) < A.data.resolvedWalk.length := by
    exact_mod_cast A.resolvedWalk_length_pos
  simp only [leftSourcePoint, rightSourcePoint, planePoint_apply_zero] at hcoord
  nlinarith [A.exitData.left_lt_right]

/--
@isnad1 id=lt.2h6v.s8.49c829010232 from=translated src=- shape=f1010f5c vocab=ce6abd07
-/
theorem leftSourcePoint_zero_lt_right :
    A.leftSourcePoint 0 < A.rightSourcePoint 0 := by
  have hn : (0 : ℝ) < A.data.resolvedWalk.length := by
    exact_mod_cast A.resolvedWalk_length_pos
  simp only [leftSourcePoint, rightSourcePoint, planePoint_apply_zero]
  nlinarith [A.exitData.left_lt_right]

/-- The two source points at which the middle polygonal path exits the endpoint disks. -/
noncomputable def trimMark : Fin 2 → Plane
  | ⟨0, _⟩ => A.leftSourcePoint
  | ⟨1, _⟩ => A.rightSourcePoint

/--
@isnad1 id=eq.2h6v.s7.9183c26b4c4e from=translated src=- shape=9b7d25f1 vocab=dc6a68fe
-/
@[simp] theorem trimMark_zero : A.trimMark 0 = A.leftSourcePoint := rfl

/--
@isnad1 id=eq.2h6v.s7.bf405720ad85 from=translated src=- shape=9b7d25f1 vocab=8960b74a
-/
@[simp] theorem trimMark_one : A.trimMark 1 = A.rightSourcePoint := rfl

/-- The source graph refined at both last-exit points. -/
noncomputable def trimSubdivision : PlaneComplex :=
  A.parameterization.source.markedEdgeSubdivision A.trimMark

/-- The exact closed source interval between the two exits. -/
noncomputable def trimSource : PlaneComplex :=
  A.trimSubdivision.restrictedTo (segment ℝ A.leftSourcePoint A.rightSourcePoint)

private theorem sourcePoint_mem_axis_segment_iff {p : Plane}
    (hp : p ∈ A.parameterization.source.support) :
    p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ A.data.resolvedWalk.length := by
  rw [A.parameterization.source_support, segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  constructor
  · simp [AffineMap.lineMap_apply_module, planePoint]
  · have hn : (0 : ℝ) ≤ A.data.resolvedWalk.length := by positivity
    constructor
    · simpa [AffineMap.lineMap_apply_module, planePoint] using mul_nonneg ht.1 hn
    · simp [AffineMap.lineMap_apply_module, planePoint]
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hn]

private theorem mem_sourceSubsegment_of_axis_bounds {p : Plane}
    (hpAxis : p 1 = 0)
    (hpLeft : A.leftSourcePoint 0 ≤ p 0)
    (hpRight : p 0 ≤ A.rightSourcePoint 0) :
    p ∈ segment ℝ A.leftSourcePoint A.rightSourcePoint := by
  rw [segment_eq_image_lineMap]
  let q : ℝ := (p 0 - A.leftSourcePoint 0) /
    (A.rightSourcePoint 0 - A.leftSourcePoint 0)
  have hden : 0 < A.rightSourcePoint 0 - A.leftSourcePoint 0 :=
    sub_pos.mpr A.leftSourcePoint_zero_lt_right
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hpLeft) hden.le
    · exact (div_le_one hden).mpr (by linarith)
  refine ⟨q, hq, ?_⟩
  ext i
  fin_cases i
  · simp only [AffineMap.lineMap_apply_module]
    dsimp [q]
    field_simp [hden.ne']
    ring
  · simp [AffineMap.lineMap_apply_module, leftSourcePoint, rightSourcePoint,
      planePoint, hpAxis]

private theorem exists_trimSubdivision_vertex (i : Fin 2) :
    ∃ w : A.trimSubdivision.Vertex,
      ({w} : Finset A.trimSubdivision.Vertex) ∈ A.trimSubdivision.simplexes ∧
        A.trimSubdivision.position w = A.trimMark i := by
  apply A.parameterization.source.exists_markedEdgeSubdivision_vertex A.trimMark i
  fin_cases i
  · exact A.leftSourcePoint_mem_source
  · exact A.rightSourcePoint_mem_source

/-- Marking the two exits makes the interval between them an exact finite subcomplex.
@isnad1 id=eq.2h6v.s8.855b5c53cf32 from=translated src=- shape=1f961b76 vocab=5175ef36
-/
theorem trimSource_support :
    A.trimSource.support = segment ℝ A.leftSourcePoint A.rightSourcePoint := by
  unfold trimSource
  apply A.trimSubdivision.restrictedTo_support_eq
  intro x hx
  by_cases hxL : x = A.leftSourcePoint
  · obtain ⟨w, hw, hpos⟩ := A.exists_trimSubdivision_vertex 0
    have hpos' : A.trimSubdivision.position w = A.leftSourcePoint :=
      hpos.trans A.trimMark_zero
    refine ⟨{w}, hw, ?_, ?_⟩
    · rw [hxL, ← hpos']
      exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩
    · intro y hy
      have hy' : y = A.trimSubdivision.position w := by
        rw [PlaneComplex.cellCarrier] at hy
        have himage : A.trimSubdivision.position ''
            (({w} : Finset A.trimSubdivision.Vertex) : Set A.trimSubdivision.Vertex) =
            {A.trimSubdivision.position w} := by
          ext z
          simp
        rw [himage, convexHull_singleton] at hy
        exact hy
      rw [hy', hpos']
      exact left_mem_segment ℝ _ _
  · by_cases hxR : x = A.rightSourcePoint
    · obtain ⟨w, hw, hpos⟩ := A.exists_trimSubdivision_vertex 1
      have hpos' : A.trimSubdivision.position w = A.rightSourcePoint :=
        hpos.trans A.trimMark_one
      refine ⟨{w}, hw, ?_, ?_⟩
      · rw [hxR, ← hpos']
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩
      · intro y hy
        have hy' : y = A.trimSubdivision.position w := by
          rw [PlaneComplex.cellCarrier] at hy
          have himage : A.trimSubdivision.position ''
              (({w} : Finset A.trimSubdivision.Vertex) : Set A.trimSubdivision.Vertex) =
              {A.trimSubdivision.position w} := by
            ext z
            simp
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hy', hpos']
        exact right_mem_segment ℝ _ _
    · have hxSource : x ∈ A.parameterization.source.support := by
        rw [A.parameterization.source_support]
        apply (convex_segment (planePoint 0 0)
          (planePoint A.data.resolvedWalk.length 0)).segment_subset
        · rw [← A.parameterization.source_support]
          exact A.leftSourcePoint_mem_source
        · rw [← A.parameterization.source_support]
          exact A.rightSourcePoint_mem_source
        · exact hx
      have hxTrimSupport : x ∈ A.trimSubdivision.support := by
        rw [trimSubdivision,
          A.parameterization.source.markedEdgeSubdivision_support_eq A.trimMark
            A.parameterization.source_card_le_two]
        exact hxSource
      rw [PlaneComplex.support] at hxTrimSupport
      simp only [Set.mem_iUnion] at hxTrimSupport
      obtain ⟨u, hu, hxu⟩ := hxTrimSupport
      have huData := (A.parameterization.source.markedEdgeChain A.trimMark
        |>.arrangementMesh.toPlaneComplex.mem_subordinateTo_simplexes_iff
          A.parameterization.source).mp hu
      obtain ⟨huArr, s, hs, hus⟩ := huData
      let M := (A.parameterization.source.markedEdgeChain A.trimMark).arrangementMesh
      have hxCoord := A.sourcePoint_mem_axis_segment_iff hxSource
      have hxBounds : A.leftSourcePoint 0 < x 0 ∧
          x 0 < A.rightSourcePoint 0 := by
        have hxClosed : A.leftSourcePoint 0 ≤ x 0 ∧
            x 0 ≤ A.rightSourcePoint 0 := by
          rw [segment_eq_image_lineMap] at hx
          obtain ⟨t, ht, rfl⟩ := hx
          constructor <;>
            simp [AffineMap.lineMap_apply_module] <;>
            nlinarith [A.leftSourcePoint_zero_lt_right, ht.1, ht.2]
        exact ⟨lt_of_le_of_ne hxClosed.1
            (Ne.symm (fun h => hxL (plane_ext h hxCoord.1))),
          lt_of_le_of_ne hxClosed.2 (fun h => hxR (plane_ext h hxCoord.1))⟩
      have hlow := M.nonneg_on_face_of_monochromatic_of_pos
        (A.parameterization.source.markedEdgeArrangement_monochromatic_vertical
          A.trimMark 0) huArr hxu (by
            change 0 < x 0 - A.leftSourcePoint 0
            linarith [hxBounds.1])
      have hhigh := M.nonpos_on_face_of_monochromatic_of_neg
        (A.parameterization.source.markedEdgeArrangement_monochromatic_vertical
          A.trimMark 1) huArr hxu (by
            change x 0 - A.rightSourcePoint 0 < 0
            linarith [hxBounds.2])
      have huSegment : A.trimSubdivision.cellCarrier u ⊆
          segment ℝ A.leftSourcePoint A.rightSourcePoint := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          have hvSource : M.position v ∈ A.parameterization.source.support := by
            apply A.parameterization.source.cellCarrier_subset_support hs
            apply hus
            exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
          have hvAxis := A.sourcePoint_mem_axis_segment_iff hvSource
          apply A.mem_sourceSubsegment_of_axis_bounds hvAxis.1
          · have hlo := hlow v hv
            change 0 ≤ M.position v 0 - A.leftSourcePoint 0 at hlo
            linarith
          · have hhi := hhigh v hv
            change M.position v 0 - A.rightSourcePoint 0 ≤ 0 at hhi
            linarith
        · exact convex_segment _ _
      exact ⟨u, hu, hxu, huSegment⟩

/-- Remove the unused vertices retained by `restrictedTo`. -/
noncomputable def trimActive : PlaneComplex :=
  PlaneComplex.active A.trimSource

/--
@isnad1 id=eq.2h6v.s8.2b770286757c from=translated src=- shape=1f961b76 vocab=42e030d1
-/
theorem trimActive_support :
    A.trimActive.support = segment ℝ A.leftSourcePoint A.rightSourcePoint := by
  rw [trimActive, A.trimSource.active_support, A.trimSource_support]

/--
@isnad1 id=mem.2h7v.s7.5d356e1a28b4 from=translated src=- shape=7af1dc66 vocab=8af5b2e8
-/
theorem trimActive_vertex_mem_support (v : A.trimActive.Vertex) :
    A.trimActive.position v ∈ A.trimActive.support := by
  change A.trimSource.position v.1 ∈ (PlaneComplex.active A.trimSource).support
  rw [A.trimSource.active_support]
  exact v.2

/--
@isnad1 id=le.3h7v.s7.8d7361c6f69d from=translated src=- shape=0c0fc459 vocab=18417cf2
-/
theorem trimActive_card_le_two :
    ∀ s ∈ A.trimActive.simplexes, s.card ≤ 2 := by
  intro s hs
  let u : Finset A.trimSubdivision.Vertex := s.map A.trimSource.activeEmbedding
  have huTrim : u ∈ A.trimSource.simplexes := A.trimSource.mem_activeSimplexes.mp hs
  have huR : u ∈ A.trimSubdivision.simplexes :=
    (A.trimSubdivision.mem_restrictedTo_simplexes_iff _).mp huTrim |>.1
  have hsub := A.parameterization.source.markedEdgeSubdivision_subdivides A.trimMark
    A.parameterization.source_card_le_two
  obtain ⟨t, ht, hut⟩ := hsub.2 u huR
  have huCard : u.card ≤ 2 :=
    PlaneComplex.card_le_two_of_cellCarrier_subset_face huR ht
      (A.parameterization.source_card_le_two t ht) hut
  calc
    s.card = u.card := by
      dsimp [u]
      exact (Finset.card_map _).symm
    _ ≤ 2 := huCard

/--
@isnad1 id=injon.2h6v.s7.736dbd69d84d from=translated src=- shape=dd50cc32 vocab=3ad583b5
-/
theorem trimActive_map_injective :
    Set.InjOn A.parameterization.map A.trimActive.support := by
  apply A.parameterization.map_injectiveOn.mono
  rw [A.trimActive_support]
  intro x hx
  rw [A.parameterization.source_support]
  apply (convex_segment (planePoint 0 0)
    (planePoint A.data.resolvedWalk.length 0)).segment_subset
  · rw [← A.parameterization.source_support]
    exact A.leftSourcePoint_mem_source
  · rw [← A.parameterization.source_support]
    exact A.rightSourcePoint_mem_source
  · exact hx

/--
@isnad1 id=isaffine.3h7v.s7.aa93b2e05f72 from=translated src=- shape=6b9ba208 vocab=1ce90684
-/
theorem trimActive_map_affine :
    ∀ s ∈ A.trimActive.simplexes,
      IsAffineOn A.parameterization.map (A.trimActive.cellCarrier s) := by
  intro s hs
  let u : Finset A.trimSubdivision.Vertex := s.map A.trimSource.activeEmbedding
  have huTrim : u ∈ A.trimSource.simplexes := A.trimSource.mem_activeSimplexes.mp hs
  have huR : u ∈ A.trimSubdivision.simplexes :=
    (A.trimSubdivision.mem_restrictedTo_simplexes_iff _).mp huTrim |>.1
  have hsub := A.parameterization.source.markedEdgeSubdivision_subdivides A.trimMark
    A.parameterization.source_card_le_two
  obtain ⟨t, ht, hut⟩ := hsub.2 u huR
  apply (A.parameterization.map_affineOn t ht).mono
  intro x hx
  apply hut
  have hx' := A.trimSource.active_cellCarrier s ▸ hx
  change x ∈ A.trimSource.cellCarrier u at hx'
  unfold trimSource at hx'
  rw [A.trimSubdivision.restrictedTo_cellCarrier] at hx'
  exact hx'

/-- The finite target graph carried by the trimmed polygonal middle. -/
noncomputable def trimTarget : PlaneComplex :=
  A.trimActive.mapGraph A.parameterization.map A.trimActive_vertex_mem_support
    A.trimActive_map_injective A.trimActive_card_le_two A.trimActive_map_affine

/--
@isnad1 id=eq.2h6v.s8.d9051b6102a8 from=translated src=- shape=770d85af vocab=bc25dc89
-/
theorem map_image_sourceSegment :
    A.parameterization.map '' segment ℝ A.leftSourcePoint A.rightSourcePoint =
      A.trimmedCarrier := by
  rw [trimmedCarrier]
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    let t : ℝ := AffineMap.lineMap A.exitData.left A.exitData.right u
    have ht : t ∈ Set.Icc A.exitData.left A.exitData.right := by
      rw [← segment_eq_Icc A.exitData.left_lt_right.le, segment_eq_image_lineMap]
      exact ⟨u, hu, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [A.parameterization.curve_eq]
    congr 2
    ext i
    fin_cases i <;>
      simp [t, leftSourcePoint, rightSourcePoint, planePoint,
        AffineMap.lineMap_apply_module]; ring
  · rintro ⟨t, ht, rfl⟩
    have htSeg : t ∈ segment ℝ A.exitData.left A.exitData.right := by
      rwa [segment_eq_Icc A.exitData.left_lt_right.le]
    rw [segment_eq_image_lineMap] at htSeg
    obtain ⟨u, hu, rfl⟩ := htSeg
    refine ⟨AffineMap.lineMap A.leftSourcePoint A.rightSourcePoint u,
      ?_, ?_⟩
    · rw [segment_eq_image_lineMap]
      exact ⟨u, hu, rfl⟩
    rw [A.parameterization.curve_eq]
    congr 2
    ext i
    fin_cases i <;>
      simp [leftSourcePoint, rightSourcePoint, planePoint,
        AffineMap.lineMap_apply_module]; ring

/--
@isnad1 id=eq.2h6v.s7.31e5f1c4a5fb from=translated src=- shape=328969f2 vocab=e0f38ed7
-/
theorem trimTarget_support : A.trimTarget.support = A.trimmedCarrier := by
  rw [trimTarget, A.trimActive.mapGraph_support A.parameterization.map
    A.trimActive_vertex_mem_support A.trimActive_map_injective
    A.trimActive_card_le_two A.trimActive_map_affine,
    A.trimActive_support, A.map_image_sourceSegment]

private theorem exists_trimActive_vertex (i : Fin 2) :
    ∃ v : A.trimActive.Vertex,
      ({v} : Finset A.trimActive.Vertex) ∈ A.trimActive.simplexes ∧
        A.trimActive.position v = A.trimMark i := by
  obtain ⟨w, hw, hpos⟩ := A.exists_trimSubdivision_vertex i
  have hmarkSegment : A.trimMark i ∈
      segment ℝ A.leftSourcePoint A.rightSourcePoint := by
    fin_cases i <;> simp [trimMark, left_mem_segment, right_mem_segment]
  have hwSub : A.trimSubdivision.cellCarrier {w} ⊆
      segment ℝ A.leftSourcePoint A.rightSourcePoint := by
    intro x hx
    have hxw : x = A.trimSubdivision.position w := by
      rw [PlaneComplex.cellCarrier] at hx
      have himage : A.trimSubdivision.position ''
          (({w} : Finset A.trimSubdivision.Vertex) : Set A.trimSubdivision.Vertex) =
          {A.trimSubdivision.position w} := by
        ext z
        simp
      rw [himage, convexHull_singleton] at hx
      exact hx
    rw [hxw, hpos]
    exact hmarkSegment
  have hwTrim : ({w} : Finset A.trimSource.Vertex) ∈ A.trimSource.simplexes := by
    unfold trimSource
    exact A.trimSubdivision.mem_restrictedTo_simplexes_iff _ |>.mpr ⟨hw, hwSub⟩
  have hwSupport : A.trimSource.position w ∈ A.trimSource.support :=
    A.trimSource.cellCarrier_subset_support hwTrim
      (subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩)
  let v : A.trimSource.ActiveVertex := ⟨w, hwSupport⟩
  refine ⟨v, ?_, ?_⟩
  · change ({v} : Finset A.trimSource.ActiveVertex) ∈
      (PlaneComplex.active A.trimSource).simplexes
    apply A.trimSource.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    exact hwTrim
  · exact hpos

/-- The `leftTrimVertex` declaration. -/
noncomputable def leftTrimVertex : A.trimTarget.Vertex :=
  Classical.choose (private_decl% (A.exists_trimActive_vertex 0))

/-- The `rightTrimVertex` declaration. -/
noncomputable def rightTrimVertex : A.trimTarget.Vertex :=
  Classical.choose (private_decl% (A.exists_trimActive_vertex 1))

/--
@isnad1 id=mem.2h6v.s7.c58c746ec985 from=translated src=- shape=6c22d196 vocab=0b0e0922
-/
theorem leftTrimVertex_face :
    ({A.leftTrimVertex} : Finset A.trimTarget.Vertex) ∈ A.trimTarget.simplexes :=
  (Classical.choose_spec (A.exists_trimActive_vertex 0)).1

/--
@isnad1 id=mem.2h6v.s7.d69940710ab8 from=translated src=- shape=6c22d196 vocab=6695ff19
-/
theorem rightTrimVertex_face :
    ({A.rightTrimVertex} : Finset A.trimTarget.Vertex) ∈ A.trimTarget.simplexes :=
  (Classical.choose_spec (A.exists_trimActive_vertex 1)).1

/--
@isnad1 id=eq.2h6v.s7.fb372954e4cd from=translated src=- shape=4aafab36 vocab=bfc381d1
-/
theorem leftTrimVertex_sourcePosition :
    A.trimActive.position A.leftTrimVertex = A.leftSourcePoint := by
  change A.trimActive.position
    (Classical.choose (private_decl% (A.exists_trimActive_vertex 0))) = A.leftSourcePoint
  exact (Classical.choose_spec (A.exists_trimActive_vertex 0)).2.trans A.trimMark_zero

/--
@isnad1 id=eq.2h6v.s7.140e9027e2a3 from=translated src=- shape=4aafab36 vocab=92c93f60
-/
theorem rightTrimVertex_sourcePosition :
    A.trimActive.position A.rightTrimVertex = A.rightSourcePoint := by
  change A.trimActive.position
    (Classical.choose (private_decl% (A.exists_trimActive_vertex 1))) = A.rightSourcePoint
  exact (Classical.choose_spec (A.exists_trimActive_vertex 1)).2.trans A.trimMark_one

/--
@isnad1 id=eq.2h6v.s7.4f4109446235 from=translated src=- shape=a143bb1c vocab=82277f3a
-/
theorem map_leftSourcePoint :
    A.parameterization.map A.leftSourcePoint = A.leftEndpoint := by
  rw [leftEndpoint, A.parameterization.curve_eq]
  rfl

/--
@isnad1 id=eq.2h6v.s7.d3fe56c04255 from=translated src=- shape=a143bb1c vocab=49c0fd0a
-/
theorem map_rightSourcePoint :
    A.parameterization.map A.rightSourcePoint = A.rightEndpoint := by
  rw [rightEndpoint, A.parameterization.curve_eq]
  rfl

/--
@isnad1 id=eq.2h6v.s7.b8d771b93991 from=translated src=- shape=4aafab36 vocab=715793f9
-/
theorem trimTarget_position_left :
    A.trimTarget.position A.leftTrimVertex = A.leftEndpoint := by
  change A.parameterization.map (A.trimActive.position A.leftTrimVertex) = _
  rw [A.leftTrimVertex_sourcePosition, A.map_leftSourcePoint]

/--
@isnad1 id=eq.2h6v.s7.091f2b93f5f7 from=translated src=- shape=4aafab36 vocab=445f510e
-/
theorem trimTarget_position_right :
    A.trimTarget.position A.rightTrimVertex = A.rightEndpoint := by
  change A.parameterization.map (A.trimActive.position A.rightTrimVertex) = _
  rw [A.rightTrimVertex_sourcePosition, A.map_rightSourcePoint]

/--
@isnad1 id=isprecon.2h6v.s7.e6df0681bc3d from=translated src=- shape=5983ece9 vocab=3586fdbd
-/
theorem isPreconnected_trimTarget_support : IsPreconnected A.trimTarget.support := by
  rw [A.trimTarget_support, trimmedCarrier]
  apply IsPreconnected.image (convex_Icc _ _).isPreconnected
  exact A.parameterization.continuousOn.mono fun _ ht =>
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩

/-- A simple finite graph path traversing the trimmed target arc. -/
noncomputable def middleVertexPath : A.trimTarget.vertexGraph.Path
    A.leftTrimVertex A.rightTrimVertex := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := (A.trimTarget.vertexGraph_reachable_of_isPreconnected
    A.isPreconnected_trimTarget_support A.leftTrimVertex_face
      A.rightTrimVertex_face).exists_isPath
  exact ⟨⟨p, hp⟩⟩

/-- An auxiliary broken line which lists the two spokes and every edge and vertex of the trimmed
target.  Connector segments between listed pieces are harmless: `completeTarget` below retains
only arrangement faces contained in the actual replacement carrier. -/
noncomputable def completeChain : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let B := A.trimTarget.edgeChain
  let vertex : Fin (B.n + 5) → Plane := fun k =>
    if k.val = 0 then h (K.edgeFirstPoint e)
    else if k.val = 1 then A.leftEndpoint
    else if hk : k.val < B.n + 3 then B.vertex ⟨k.val - 2, by omega⟩
    else if k.val = B.n + 3 then A.rightEndpoint
    else h (K.edgeSecondPoint e)
  exact {
    n := B.n + 4
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

/--
@isnad1 id=eq.2h6v.s7.1b2138a9dcb5 from=translated src=- shape=5e6f8fc6 vocab=feadf1b0
-/
@[simp] theorem completeChain_vertex_zero :
    A.completeChain.vertex 0 = h (K.edgeFirstPoint e) := by
  simp [completeChain]

/--
@isnad1 id=eq.2h6v.s7.22f976eaaa5a from=translated src=- shape=ea4dedb3 vocab=8b24023b
-/
@[simp] theorem completeChain_vertex_one :
    A.completeChain.vertex ⟨1, by simp [completeChain]⟩ = A.leftEndpoint := by
  simp [completeChain]

/--
@isnad1 id=eq.2h7v.s7.9e420eb0a02c from=translated src=- shape=0d783253 vocab=9ec9045a
-/
theorem completeChain_vertex_middle
    (i : Fin (A.trimTarget.edgeChain.n + 1)) :
    A.completeChain.vertex ⟨i.val + 2, by simp [completeChain]; omega⟩ =
      A.trimTarget.edgeChain.vertex i := by
  simp only [completeChain]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2

/--
@isnad1 id=eq.2h6v.s7.64afa8ec7282 from=translated src=- shape=40a7a214 vocab=86b87218
-/
theorem completeChain_vertex_rightEndpoint :
    A.completeChain.vertex
        ⟨A.trimTarget.edgeChain.n + 3, by simp [completeChain]⟩ =
      A.rightEndpoint := by
  simp [completeChain]

/--
@isnad1 id=eq.2h6v.s7.b97e17697ed5 from=translated src=- shape=3a0c6120 vocab=e48b8872
-/
theorem completeChain_vertex_finish :
    A.completeChain.vertex (Fin.last A.completeChain.n) =
      h (K.edgeSecondPoint e) := by
  simp [completeChain]

/-- The finite plane complex carried by one complete replacement edge. -/
noncomputable def completeTarget : PlaneComplex :=
  A.completeChain.arrangementMesh.toPlaneComplex.restrictedTo A.completeCarrier

/-- Every point of a complete replacement edge lies in a one-dimensional arrangement face
subordinate to that edge.  The cardinality conclusion is what permits several replacement edges
to be resolved in one common line arrangement.
@isnad1 id=ex.3h7v.s8.cfd969e861e5 from=translated src=- shape=a703dfc9 vocab=aad7a1b1
-/
theorem exists_completeTarget_face {x : Plane} (hx : x ∈ A.completeCarrier) :
    ∃ s ∈ A.completeChain.arrangementMesh.toPlaneComplex.simplexes,
      x ∈ A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ∧
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
          A.completeCarrier ∧ s.card ≤ 2 := by
  classical
  rcases hx with (hxLeft | hxMiddle) | hxRight
  · let i : Fin A.completeChain.n := ⟨0, by simp [completeChain]⟩
    have hsegment : segment ℝ
        (A.completeChain.vertex i.castSucc) (A.completeChain.vertex i.succ) =
        A.leftSpoke := by
      simp [i, completeChain, leftSpoke]
    obtain ⟨s, hs, hxs, hsSegment⟩ :=
      A.completeChain.exists_face_on_segment i (hsegment.symm ▸ hxLeft)
    refine ⟨s, hs, hxs, ?_,
      A.completeChain.arrangementMesh.toPlaneComplex.card_le_two_of_vertices_mem_segment
        hs hsSegment⟩
    have hsub : A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        A.leftSpoke := by
      rw [← hsegment]
      apply convexHull_min _ (convex_segment _ _)
      rintro y ⟨v, hv, rfl⟩
      exact hsSegment v hv
    exact hsub.trans (Set.subset_union_left.trans Set.subset_union_left)
  · have hxSupport : x ∈ A.trimTarget.support := by
      rwa [A.trimTarget_support]
    rw [PlaneComplex.support] at hxSupport
    simp only [Set.mem_iUnion] at hxSupport
    obtain ⟨s, hs, hxs⟩ := hxSupport
    have hsPos : 0 < s.card := Finset.card_pos.mpr
      (A.trimTarget.nonempty_of_mem s hs)
    have hsLe : s.card ≤ 2 := A.trimActive_card_le_two s hs
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsOne | hsTwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsOne
      have hxv : x = A.trimTarget.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨j, hj⟩ := A.trimTarget.exists_vertexAt v
      let q : Fin (A.trimTarget.edgeChain.n + 1) :=
        ⟨2 * Fintype.card A.trimTarget.EdgeFace + j.val, by
          simp [PlaneComplex.edgeChain]
          ⟩
      let k : Fin (A.completeChain.n + 1) :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      have hk : A.completeChain.vertex k = A.trimTarget.position v := by
        calc
          A.completeChain.vertex k = A.trimTarget.edgeChain.vertex q := by
            simpa [k] using A.completeChain_vertex_middle q
          _ = A.trimTarget.position (A.trimTarget.vertexAt j) := by
            simpa [q] using A.trimTarget.edgeChain_vertex_original j
          _ = A.trimTarget.position v := by rw [hj]
      obtain ⟨w, hwpos, hwface⟩ :=
        A.completeChain.exists_arrangementVertex_position_eq k
      have hwcard : ({w} : Finset A.completeChain.arrangementMesh.Vertex).card ≤ 2 := by
        simp
      refine ⟨{w}, hwface, ?_, ?_, hwcard⟩
      · rw [hxv]
        apply subset_convexHull ℝ _
        exact ⟨w, Finset.mem_singleton_self _, hwpos.trans hk⟩
      · intro y hy
        have hyw : y = A.completeChain.arrangementMesh.toPlaneComplex.position w := by
          rw [PlaneComplex.cellCarrier] at hy
          have himage : A.completeChain.arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset A.completeChain.arrangementMesh.toPlaneComplex.Vertex) :
                Set A.completeChain.arrangementMesh.toPlaneComplex.Vertex) =
              {A.completeChain.arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨u, hu, rfl⟩
              rw [Finset.mem_singleton.mp hu]
              exact Set.mem_singleton _
            · intro hz
              rw [Set.mem_singleton_iff] at hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rwa [himage, convexHull_singleton] at hy
        rw [hyw, hwpos, hk]
        apply Or.inl
        apply Or.inr
        rw [← A.trimTarget_support]
        exact A.trimTarget.cellCarrier_subset_support hs
          (subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩)
    · let E : A.trimTarget.EdgeFace :=
        ⟨s, Finset.mem_filter.mpr ⟨hs, hsTwo⟩⟩
      obtain ⟨j, hj⟩ := A.trimTarget.exists_edgeAt E
      let q : Fin A.trimTarget.edgeChain.n := A.trimTarget.edgeChainIndex j
      let k : Fin A.completeChain.n :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      have hleft : A.completeChain.vertex k.castSucc =
          A.trimTarget.edgeChain.vertex q.castSucc := by
        simpa [k, q] using A.completeChain_vertex_middle q.castSucc
      have hright : A.completeChain.vertex k.succ =
          A.trimTarget.edgeChain.vertex q.succ := by
        simpa [k, q] using A.completeChain_vertex_middle q.succ
      have hsegment : segment ℝ
          (A.completeChain.vertex k.castSucc) (A.completeChain.vertex k.succ) =
          A.trimTarget.cellCarrier s := by
        rw [hleft, hright]
        calc
          segment ℝ (A.trimTarget.edgeChain.vertex q.castSucc)
              (A.trimTarget.edgeChain.vertex q.succ) =
              A.trimTarget.cellCarrier (A.trimTarget.edgeAt j).1 := by
                simpa [q] using A.trimTarget.edgeChain_segment j
          _ = A.trimTarget.cellCarrier s := by rw [hj]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        A.completeChain.exists_face_on_segment k (hsegment.symm ▸ hxs)
      refine ⟨u, hu, hxu, ?_,
        A.completeChain.arrangementMesh.toPlaneComplex.card_le_two_of_vertices_mem_segment
          hu huSegment⟩
      have huSub : A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier u ⊆
          A.trimTarget.cellCarrier s := by
        rw [← hsegment]
        apply convexHull_min _ (convex_segment _ _)
        rintro y ⟨v, hv, rfl⟩
        exact huSegment v hv
      intro y hy
      apply Or.inl
      apply Or.inr
      rw [← A.trimTarget_support]
      exact A.trimTarget.cellCarrier_subset_support hs (huSub hy)
  · let i : Fin A.completeChain.n :=
      ⟨A.trimTarget.edgeChain.n + 3, by simp [completeChain]⟩
    have hsegment : segment ℝ
        (A.completeChain.vertex i.castSucc) (A.completeChain.vertex i.succ) =
        A.rightSpoke := by
      simp [i, completeChain, rightSpoke]
    obtain ⟨s, hs, hxs, hsSegment⟩ :=
      A.completeChain.exists_face_on_segment i (hsegment.symm ▸ hxRight)
    refine ⟨s, hs, hxs, ?_,
      A.completeChain.arrangementMesh.toPlaneComplex.card_le_two_of_vertices_mem_segment
        hs hsSegment⟩
    have hsub : A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        A.rightSpoke := by
      rw [← hsegment]
      apply convexHull_min _ (convex_segment _ _)
      rintro y ⟨v, hv, rfl⟩
      exact hsSegment v hv
    exact hsub.trans Set.subset_union_right

/-- Exact finite-complex realization of the complete replacement edge.
@isnad1 id=eq.2h6v.s7.20acc06f3347 from=translated src=- shape=328969f2 vocab=43bdbde8
-/
theorem completeTarget_support : A.completeTarget.support = A.completeCarrier := by
  unfold completeTarget
  apply A.completeChain.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsub, -⟩ := A.exists_completeTarget_face hx
  exact ⟨s, hs, hxs, hsub⟩

/-- Every point of a complete replacement edge lies on one of the finitely listed segments of
its auxiliary chain.  This is the coverage input used when the three edge chains of a face are
placed into one common line arrangement.
@isnad1 id=le.2h6v.s7.62b982dbf87b from=translated src=- shape=25a3b5ae vocab=adeaa571
-/
theorem completeCarrier_subset_segmentCarrier :
    A.completeCarrier ⊆ A.completeChain.segmentCarrier := by
  classical
  rintro x ((hxLeft | hxMiddle) | hxRight)
  · apply Set.mem_iUnion.mpr
    let i : Fin A.completeChain.n := ⟨0, by simp [completeChain]⟩
    refine ⟨i, ?_⟩
    simpa [i, completeChain, leftSpoke] using hxLeft
  · have hxSupport : x ∈ A.trimTarget.support := by
      rwa [A.trimTarget_support]
    rw [PlaneComplex.support] at hxSupport
    simp only [Set.mem_iUnion] at hxSupport
    obtain ⟨s, hs, hxs⟩ := hxSupport
    have hsPos : 0 < s.card := Finset.card_pos.mpr
      (A.trimTarget.nonempty_of_mem s hs)
    have hsLe : s.card ≤ 2 := A.trimActive_card_le_two s hs
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsOne | hsTwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsOne
      have hxv : x = A.trimTarget.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨j, hj⟩ := A.trimTarget.exists_vertexAt v
      let q : Fin A.trimTarget.edgeChain.n :=
        ⟨2 * Fintype.card A.trimTarget.EdgeFace + j.val, by
          simp [PlaneComplex.edgeChain]
          ⟩
      let k : Fin A.completeChain.n :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rw [hxv]
      have hleft : A.completeChain.vertex k.castSucc = A.trimTarget.position v := by
        calc
          A.completeChain.vertex k.castSucc = A.trimTarget.edgeChain.vertex q.castSucc := by
            simpa [k, q] using A.completeChain_vertex_middle q.castSucc
          _ = A.trimTarget.position (A.trimTarget.vertexAt j) := by
            simpa [q] using A.trimTarget.edgeChain_vertex_original j
          _ = A.trimTarget.position v := by rw [hj]
      rw [← hleft]
      exact left_mem_segment ℝ _ _
    · let E : A.trimTarget.EdgeFace :=
        ⟨s, Finset.mem_filter.mpr ⟨hs, hsTwo⟩⟩
      obtain ⟨j, hj⟩ := A.trimTarget.exists_edgeAt E
      let q : Fin A.trimTarget.edgeChain.n := A.trimTarget.edgeChainIndex j
      let k : Fin A.completeChain.n :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      have hleft : A.completeChain.vertex k.castSucc =
          A.trimTarget.edgeChain.vertex q.castSucc := by
        simpa [k, q] using A.completeChain_vertex_middle q.castSucc
      have hright : A.completeChain.vertex k.succ =
          A.trimTarget.edgeChain.vertex q.succ := by
        simpa [k, q] using A.completeChain_vertex_middle q.succ
      rw [hleft, hright]
      have hsegment := A.trimTarget.edgeChain_segment j
      rw [hj] at hsegment
      rw [hsegment]
      exact hxs
  · apply Set.mem_iUnion.mpr
    let i : Fin A.completeChain.n :=
      ⟨A.trimTarget.edgeChain.n + 3, by simp [completeChain]⟩
    refine ⟨i, ?_⟩
    simpa [i, completeChain, rightSpoke] using hxRight

/-- The first intrinsic endpoint as a vertex of the finite complete-edge complex. -/
noncomputable def completeStartVertex : A.completeTarget.Vertex :=
  A.completeChain.arrangementVertex 0

/-- The second intrinsic endpoint as a vertex of the finite complete-edge complex. -/
noncomputable def completeFinishVertex : A.completeTarget.Vertex :=
  A.completeChain.arrangementVertex (Fin.last A.completeChain.n)

/--
@isnad1 id=eq.2h6v.s7.0eaac9708488 from=translated src=- shape=d065f64f vocab=0a6bdf8b
-/
theorem completeTarget_position_start :
    A.completeTarget.position A.completeStartVertex = h (K.edgeFirstPoint e) := by
  change A.completeChain.arrangementMesh.toPlaneComplex.position
    (A.completeChain.arrangementVertex 0) = _
  rw [A.completeChain.arrangementVertex_position, A.completeChain_vertex_zero]

/--
@isnad1 id=eq.2h6v.s7.81d400ecb59c from=translated src=- shape=d065f64f vocab=a3301291
-/
theorem completeTarget_position_finish :
    A.completeTarget.position A.completeFinishVertex = h (K.edgeSecondPoint e) := by
  change A.completeChain.arrangementMesh.toPlaneComplex.position
    (A.completeChain.arrangementVertex (Fin.last A.completeChain.n)) = _
  rw [A.completeChain.arrangementVertex_position, A.completeChain_vertex_finish]

private theorem singleton_cellCarrier_subset_completeCarrier
    (v : A.completeTarget.Vertex) (p : Plane)
    (hp : A.completeTarget.position v = p) (hpmem : p ∈ A.completeCarrier) :
    A.completeTarget.cellCarrier {v} ⊆ A.completeCarrier := by
  intro x hx
  have hxv : x = A.completeTarget.position v := by
    rw [PlaneComplex.cellCarrier] at hx
    have himage : A.completeTarget.position ''
        (({v} : Finset A.completeTarget.Vertex) : Set A.completeTarget.Vertex) =
        {A.completeTarget.position v} := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_singleton.mp hw]
        exact Set.mem_singleton _
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact ⟨v, Finset.mem_singleton_self _, rfl⟩
    rwa [himage, convexHull_singleton] at hx
  rw [hxv, hp]
  exact hpmem

/--
@isnad1 id=mem.2h6v.s7.79fbc0fe0ae8 from=translated src=- shape=6c22d196 vocab=8b2fbbf9
-/
theorem completeStartVertex_face :
    ({A.completeStartVertex} : Finset A.completeTarget.Vertex) ∈
      A.completeTarget.simplexes := by
  apply (A.completeChain.arrangementMesh.toPlaneComplex
    |>.mem_restrictedTo_simplexes_iff A.completeCarrier).mpr
  refine ⟨A.completeChain.arrangementVertex_face 0, ?_⟩
  apply A.singleton_cellCarrier_subset_completeCarrier A.completeStartVertex
    (h (K.edgeFirstPoint e)) A.completeTarget_position_start
  exact Or.inl (Or.inl (left_mem_segment ℝ _ _))

/--
@isnad1 id=mem.2h6v.s7.b7db393ea7b2 from=translated src=- shape=6c22d196 vocab=f744ec86
-/
theorem completeFinishVertex_face :
    ({A.completeFinishVertex} : Finset A.completeTarget.Vertex) ∈
      A.completeTarget.simplexes := by
  apply (A.completeChain.arrangementMesh.toPlaneComplex
    |>.mem_restrictedTo_simplexes_iff A.completeCarrier).mpr
  refine ⟨A.completeChain.arrangementVertex_face (Fin.last A.completeChain.n), ?_⟩
  apply A.singleton_cellCarrier_subset_completeCarrier A.completeFinishVertex
    (h (K.edgeSecondPoint e)) A.completeTarget_position_finish
  exact Or.inr (right_mem_segment ℝ _ _)

/--
@isnad1 id=isprecon.2h6v.s7.6dedfd13be16 from=translated src=- shape=5983ece9 vocab=3e68627f
-/
theorem isPreconnected_completeTarget_support :
    IsPreconnected A.completeTarget.support := by
  rw [A.completeTarget_support, ← A.range_completePath]
  exact (isConnected_range A.completePath.continuous).isPreconnected

/-- A simple finite graph path whose geometric carrier runs from one intrinsic endpoint to the
other inside the complete replacement edge. -/
noncomputable def completeVertexPath : A.completeTarget.vertexGraph.Path
    A.completeStartVertex A.completeFinishVertex := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := (A.completeTarget.vertexGraph_reachable_of_isPreconnected
    A.isPreconnected_completeTarget_support A.completeStartVertex_face
      A.completeFinishVertex_face).exists_isPath
  exact ⟨⟨p, hp⟩⟩

end CentralPolygonalArc
end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
