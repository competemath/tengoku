import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.StructuredF0
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms structuredEquiv_sourceAdjoint_eq_sharp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0Adjoint_eq_sharp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0Cross_eq_cross` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0RecoveredProduct_eq_structuredProduct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms structuredEquiv_map_sourceProduct_to_recovery` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms StructuredSourceProductAgreesWithF0` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Canonical source product versus frozen F0 multiplication

This file opens the F0 comparison only after the source product definition was
frozen.  It packages the literal F0 trace, trace form, and cubic polarization
as recovery data, proves that their recovered adjoint/product are the frozen
`sharp`/`structuredProduct`, and only then transports the source product.
-/

namespace AlbertLean.Comparison.StructuredProductF0

open AlbertLean
open AlbertLean.CubicNorm
open AlbertLean.Generated
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Comparison.StructuredF0

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem f0TraceForm_add_right (x y z : Coord) :
    traceForm x (y + z) = traceForm x y + traceForm x z := by
  rw [traceForm_eq_gram, traceForm_eq_gram, traceForm_eq_gram]
  simp [traceFormGram, v]
  ring

theorem f0TraceForm_smul_right (a : ℚ) (x y : Coord) :
    traceForm x (a • y) = a * traceForm x y := by
  rw [traceForm_eq_gram, traceForm_eq_gram]
  simp [traceFormGram, v]
  ring

theorem f0TraceForm_add_left (x y z : Coord) :
    traceForm (x + y) z = traceForm x z + traceForm y z := by
  rw [traceForm_symmetric, f0TraceForm_add_right]
  rw [traceForm_symmetric z x, traceForm_symmetric z y]

theorem f0TraceForm_smul_left (a : ℚ) (x y : Coord) :
    traceForm (a • x) y = a * traceForm x y := by
  rw [traceForm_symmetric, f0TraceForm_smul_right, traceForm_symmetric y x]

/-- The frozen F0 trace form, packaged directly as a bilinear map.-/
def f0TraceFormLinear : Coord →ₗ[ℚ] Coord →ₗ[ℚ] ℚ where
  toFun x :=
    { toFun := traceForm x
      map_add' := f0TraceForm_add_right x
      map_smul' := by intro a y; simpa [smul_eq_mul] using f0TraceForm_smul_right a x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact f0TraceForm_add_left x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    simpa [smul_eq_mul] using f0TraceForm_smul_left a x y

@[simp] theorem f0TraceFormLinear_apply (x y : Coord) :
    f0TraceFormLinear x y = traceForm x y := rfl

/-- The frozen F0 trace, packaged directly as a linear functional.-/
def f0TraceLinear : Coord →ₗ[ℚ] ℚ where
  toFun := traceN
  map_add' := traceN_add
  map_smul' := by
    intro a x
    simpa [smul_eq_mul] using traceN_smul a x

@[simp] theorem f0TraceLinear_apply (x : Coord) : f0TraceLinear x = traceN x := rfl

set_option maxHeartbeats 20000000 in
theorem f0Polar_add_right (x y z w : Coord) :
    cubicPolar x y (z + w) = cubicPolar x y z + cubicPolar x y w := by
  rw [cubicPolar_eq_polarForm, cubicPolar_eq_polarForm, cubicPolar_eq_polarForm]
  simp [polarForm, v, q]
  ring

set_option maxHeartbeats 20000000 in
theorem f0Polar_smul_right (a : ℚ) (x y z : Coord) :
    cubicPolar x y (a • z) = a * cubicPolar x y z := by
  rw [cubicPolar_eq_polarForm, cubicPolar_eq_polarForm]
  simp [polarForm, v, q]
  ring

theorem f0Polar_swap_left (x y z : Coord) : cubicPolar x y z = cubicPolar y x z := by
  simp only [cubicPolar]
  have hxyz : y + x + z = x + y + z := by abel
  have hxy : y + x = x + y := add_comm _ _
  rw [hxyz, hxy]
  ring

theorem f0Polar_swap_right (x y z : Coord) : cubicPolar x y z = cubicPolar x z y := by
  simp only [cubicPolar]
  have hxyz : x + z + y = x + y + z := by abel
  have hzy : z + y = y + z := add_comm _ _
  rw [hxyz, hzy]
  ring

theorem f0Polar_add_middle (x y z w : Coord) :
    cubicPolar x (y + z) w = cubicPolar x y w + cubicPolar x z w := by
  rw [f0Polar_swap_right x (y + z) w, f0Polar_add_right,
    f0Polar_swap_right x w y, f0Polar_swap_right x w z]

theorem f0Polar_smul_middle (a : ℚ) (x y z : Coord) :
    cubicPolar x (a • y) z = a * cubicPolar x y z := by
  rw [f0Polar_swap_right x (a • y) z, f0Polar_smul_right,
    f0Polar_swap_right x z y]

theorem f0Polar_add_left (x y z w : Coord) :
    cubicPolar (x + y) z w = cubicPolar x z w + cubicPolar y z w := by
  rw [f0Polar_swap_left (x + y) z w, f0Polar_add_middle,
    f0Polar_swap_left z x w, f0Polar_swap_left z y w]

theorem f0Polar_smul_left (a : ℚ) (x y z : Coord) :
    cubicPolar (a • x) y z = a * cubicPolar x y z := by
  rw [f0Polar_swap_left (a • x) y z, f0Polar_smul_middle,
    f0Polar_swap_left y x z]

/-- The frozen F0 cubic polarization, packaged directly as a trilinear map.-/
def f0PolarLinear : Coord →ₗ[ℚ] Coord →ₗ[ℚ] Coord →ₗ[ℚ] ℚ where
  toFun x :=
    { toFun := fun y =>
        { toFun := cubicPolar x y
          map_add' := by
            exact f0Polar_add_right x y
          map_smul' := by
            intro a z
            simpa [smul_eq_mul] using f0Polar_smul_right a x y z }
      map_add' := by
        intro y z
        apply LinearMap.ext
        intro w
        exact f0Polar_add_middle x y z w
      map_smul' := by
        intro a y
        apply LinearMap.ext
        intro z
        simpa [smul_eq_mul] using f0Polar_smul_middle a x y z }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    exact f0Polar_add_left x y z w
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    simpa [smul_eq_mul] using f0Polar_smul_left a x y z

@[simp] theorem f0PolarLinear_apply (x y z : Coord) :
    f0PolarLinear x y z = cubicPolar x y z := rfl

/-- Recovery data whose fields are the literal frozen F0 definitions.-/
noncomputable def f0RecoveryData : RecoveryData ℚ Coord where
  traceForm := f0TraceFormLinear
  polar := f0PolarLinear
  trace := f0TraceLinear
  one := AlbertLean.one
  traceForm_nondegenerate := traceForm_nondegenerate

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/-- Mutation anchor: source adjoint coordinates land on the frozen F0 `sharp`.-/
theorem structuredEquiv_sourceAdjoint_eq_sharp (x : JCoord ℚ) :
    structuredEquiv (sourceAdjoint x) = sharp (structuredEquiv x) := by
  rw [sourceAdjoint_eq_explicit]
  funext i
  fin_cases i <;>
    simp [structuredEquiv, structuredToF0, sourceExplicitAdjoint, sourceMuS,
      sourceMuC, normalizedMuV, muV, nV, nS, nC, pf_coordinate, evalU,
      wedge2, dualWedge2, hodgeStar, sharp_coord_0, sharp_coord_1, sharp_coord_2,
      sharp_coord_3, sharp_coord_4, sharp_coord_5, sharp_coord_6, sharp_coord_7,
      sharp_coord_8, sharp_coord_9, sharp_coord_10, sharp_coord_11,
      sharp_coord_12, sharp_coord_13, sharp_coord_14, sharp_coord_15,
      sharp_coord_16, sharp_coord_17, sharp_coord_18, sharp_coord_19,
      sharp_coord_20, sharp_coord_21, sharp_coord_22, sharp_coord_23,
      sharp_coord_24, sharp_coord_25, sharp_coord_26, cubicPolar_eq_polarForm,
      polarForm, basisVec, v, q] <;> ring

/-- Recovery-data transport sends the source adjoint to the F0 adjoint.-/
theorem structuredEquiv_map_adjoint (x : JCoord ℚ) :
    structuredEquiv ((sourceRecoveryData (K := ℚ)).adjoint x) =
      f0RecoveryData.adjoint (structuredEquiv x) := by
  apply (sourceRecoveryData (K := ℚ)).map_adjoint f0RecoveryData structuredEquiv
  · intro a b
    simpa [f0RecoveryData, sourceRecoveryData] using
      (sourceTraceForm_agrees_with_f0 a b).symm
  · intro a b c
    simpa [f0RecoveryData, sourceRecoveryData] using
      (sourcePolar_agrees_with_f0 a b c).symm

/-- The F0 trace-dual recovered adjoint is exactly the frozen `sharp`.-/
theorem f0Adjoint_eq_sharp (x : Coord) : f0RecoveryData.adjoint x = sharp x := by
  obtain ⟨y, rfl⟩ := structuredEquiv.surjective x
  rw [← structuredEquiv_map_adjoint]
  change structuredEquiv (sourceAdjoint y) = sharp (structuredEquiv y)
  exact structuredEquiv_sourceAdjoint_eq_sharp y

/-- Mutation anchor: recovered cross product is the frozen F0 cross product.-/
theorem f0Cross_eq_cross (x y : Coord) : f0RecoveryData.cross x y = cross x y := by
  simp [RecoveryData.cross, cross, f0Adjoint_eq_sharp]

/-- The target-side canonical recovery product equals the frozen F0 product.-/
theorem f0RecoveredProduct_eq_structuredProduct (x y : Coord) :
    f0RecoveryData.product x y = structuredProduct x y := by
  have hSpur : f0RecoveryData.spurBilinear x y = AlbertLean.spurBilinear x y := by
    simp [f0RecoveryData, RecoveryData.spurBilinear, traceForm]
  rw [RecoveryData.product, structuredProduct, f0Cross_eq_cross]
  rw [hSpur]
  rfl

/-- Primary transport theorem before rewriting the target recovery product.-/
theorem structuredEquiv_map_sourceProduct_to_recovery (x y : JCoord ℚ) :
    structuredEquiv (sourceProduct x y) =
      f0RecoveryData.product (structuredEquiv x) (structuredEquiv y) := by
  apply (sourceRecoveryData (K := ℚ)).map_product f0RecoveryData structuredEquiv
  · simpa [sourceRecoveryData, f0RecoveryData] using structuredEquiv_sourceOne
  · intro a
    simpa [sourceRecoveryData, f0RecoveryData] using
      (sourceTrace_agrees_with_f0 a).symm
  · intro a b
    simpa [f0RecoveryData, sourceRecoveryData] using
      (sourceTraceForm_agrees_with_f0 a b).symm
  · intro a b c
    simpa [f0RecoveryData, sourceRecoveryData] using
      (sourcePolar_agrees_with_f0 a b c).symm

/-- The source product agrees with F0.-/
theorem StructuredSourceProductAgreesWithF0 :
    StructuredProductAgreesWithF0Statement
      (sourceProduct : JCoord ℚ → JCoord ℚ → JCoord ℚ) := by
  intro x y
  rw [structuredEquiv_map_sourceProduct_to_recovery,
    f0RecoveredProduct_eq_structuredProduct]

end AlbertLean.Comparison.StructuredProductF0
