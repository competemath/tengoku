import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CubicAutomorphism
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cubic-and-unit automorphisms of the field-generic source model

This module identifies the established source `RecoveryData` with the literal
source cubic.  It turns preservation of `sourceNorm` and `sourceOne` into
preservation of the recovered adjoint, cross product, and Springer product
over every characteristic-zero field.
-/

noncomputable section

namespace AlbertLean.Generic.CubicAutomorphism

open AlbertLean.CubicNorm
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct

variable {K : Type*} [Field K] [CharZero K]

/-- The established source recovery data presented by its literal cubic norm.-/
def sourceRecoveryPresentation :
    RecoveryPresentation (sourceRecoveryData (K := K)) where
  cubic := sourceNorm
  polar_formula := by
    intro x y z
    simp only [sourceRecoveryData, sourcePolarLinear_apply]
    have hzero : sourceNorm (0 : JCoord K) = 0 := by
      have h := sourceNorm_smul (K := K) 0 (sourceOne : JCoord K)
      simpa using h
    rw [sourcePolar, polar, hzero]
    ring
  trace_formula := by
    intro x
    simp only [sourceRecoveryData, sourceTraceLinear_apply,
      sourcePolarLinear_apply]
    rw [sourcePolar_one, sourceSpurPolar_formula]
    simp [sourceOne, sourceTrace]
    ring
  traceForm_formula := by
    intro x y
    simp only [sourceRecoveryData, sourceTraceFormLinear_apply,
      sourceTraceLinear_apply, sourcePolarLinear_apply]
    rw [sourcePolar_one]
    rfl

/-- A source-linear bijection preserving the literal cubic and unit preserves
the recovered adjoint.-/
theorem sourceAdjoint_invariant_of_cubic_unit
    (g : JCoord K ≃ₗ[K] JCoord K)
    (hOne : g sourceOne = sourceOne)
    (hCubic : ∀ x, sourceNorm (g x) = sourceNorm x) (x : JCoord K) :
    g (sourceAdjoint x) = sourceAdjoint (g x) := by
  exact sourceRecoveryPresentation.map_adjoint g hOne hCubic x

/-- A source-linear bijection preserving the literal cubic and unit preserves
the source cross product.-/
theorem sourceCross_invariant_of_cubic_unit
    (g : JCoord K ≃ₗ[K] JCoord K)
    (hOne : g sourceOne = sourceOne)
    (hCubic : ∀ x, sourceNorm (g x) = sourceNorm x) (x y : JCoord K) :
    g (sourceCross x y) = sourceCross (g x) (g y) := by
  exact sourceRecoveryPresentation.map_cross g hOne hCubic x y

/-- Field-generic compression theorem for the source model.-/
theorem sourceProduct_invariant_of_cubic_unit
    (g : JCoord K ≃ₗ[K] JCoord K)
    (hOne : g sourceOne = sourceOne)
    (hCubic : ∀ x, sourceNorm (g x) = sourceNorm x) (x y : JCoord K) :
    g (sourceProduct x y) = sourceProduct (g x) (g y) := by
  exact sourceRecoveryPresentation.map_product g hOne hCubic x y

/-- Package cubic-and-unit preservation as an actual automorphism of the
field-generic source Springer product.-/
def sourceAutOfCubicUnit
    (g : JCoord K ≃ₗ[K] JCoord K)
    (hOne : g sourceOne = sourceOne)
    (hCubic : ∀ x, sourceNorm (g x) = sourceNorm x) :
    RecoveryPresentation.Aut (sourceRecoveryData (K := K)) :=
  sourceRecoveryPresentation.automorphismOfCubicUnit g hOne hCubic

end AlbertLean.Generic.CubicAutomorphism
