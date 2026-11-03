import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorReflectionTransport
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms BV_reflectV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms BV_orthogonalRemainder` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nV_orthogonalRemainder_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nV_orthogonalRemainder_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Linear and bilinear interfaces for source Householder reflections, followed by
the explicit orthogonal remainder of a nondegenerate Gram pair.  This module
does not package reflection words or parity corrections.
-/

noncomputable section
namespace AlbertLean.Triality.SourceVectorPairReflection

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceEvenReflections SourceVectorReflectionTransport

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem reflectV_add (a v w : VCoord K) :
    reflectV a (v + w) = reflectV a v + reflectV a w := by
  rw [reflectV, reflectV, reflectV, BV_add_right, add_div]
  module

theorem reflectV_smul (a v : VCoord K) (k : K) :
    reflectV a (k • v) = k • reflectV a v := by
  rw [reflectV, reflectV, BV_smul_right, mul_div_assoc]
  module

def reflectVLinear (a : VCoord K) : VCoord K →ₗ[K] VCoord K where
  toFun := reflectV a
  map_add' := reflectV_add a
  map_smul' := fun k v => reflectV_smul a v k

@[simp] theorem reflectVLinear_apply (a v : VCoord K) :
    reflectVLinear a v = reflectV a v := rfl

/-- Polarization of norm preservation gives the full bilinear isometry law.-/
theorem BV_reflectV (a v w : VCoord K) (ha : nV a ≠ 0) :
    BV (reflectV a v) (reflectV a w) = BV v w := by
  have hvw := nV_reflectV a (v + w) ha
  rw [reflectV_add, nV_add, nV_add,
    nV_reflectV a v ha, nV_reflectV a w ha] at hvw
  linear_combination hvw

/-- A reflection vector orthogonal to `v` fixes `v` pointwise.-/
theorem reflectV_eq_of_orthogonal (a v : VCoord K)
    (horth : BV a v = 0) : reflectV a v = v := by
  rw [reflectV, horth, zero_div, zero_smul, sub_zero]

/-- The scalar of the projection onto an anisotropic first Gram vector.-/
def projectionCoeff (y₁ y₂ : VCoord K) : K :=
  BV y₁ y₂ / (2 * nV y₁)

/-- The second vector after subtracting its component along the first.-/
def orthogonalRemainder (y₁ y₂ : VCoord K) : VCoord K :=
  y₂ - projectionCoeff y₁ y₂ • y₁

theorem BV_orthogonalRemainder (y₁ y₂ : VCoord K)
    (hy₁ : nV y₁ ≠ 0) :
    BV y₁ (orthogonalRemainder y₁ y₂) = 0 := by
  rw [orthogonalRemainder, sub_eq_add_neg, ← neg_smul, BV_add_right,
    BV_smul_right, projectionCoeff, BV_self_eq_two_nV]
  field_simp [hy₁]
  ring

/-- Clearing the projection denominator gives the binary Gram determinant.-/
theorem nV_orthogonalRemainder_identity (y₁ y₂ : VCoord K)
    (hy₁ : nV y₁ ≠ 0) :
    4 * nV y₁ * nV (orthogonalRemainder y₁ y₂) =
      4 * nV y₁ * nV y₂ - (BV y₁ y₂) ^ 2 := by
  rw [orthogonalRemainder, nV_sub, nV_smul, BV_smul_right,
    BV_symmetric y₂ y₁, projectionCoeff]
  field_simp [hy₁]
  ring

/-- On the nondegenerate Gram open, the orthogonal remainder is anisotropic.-/
theorem nV_orthogonalRemainder_ne_zero (y₁ y₂ : VCoord K)
    (hy₁ : nV y₁ ≠ 0)
    (hGram : 4 * nV y₁ * nV y₂ - (BV y₁ y₂) ^ 2 ≠ 0) :
    nV (orthogonalRemainder y₁ y₂) ≠ 0 := by
  intro hu
  apply hGram
  rw [← nV_orthogonalRemainder_identity y₁ y₂ hy₁, hu]
  ring

end AlbertLean.Triality.SourceVectorPairReflection
