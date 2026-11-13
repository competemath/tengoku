import Tengoku.Nlalib.NLAlib.Matrix.Functions.KTransformCongruence
import Tengoku.Nlalib.NLAlib.Matrix.Functions.PositiveConeRayleigh
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Cone positivity and Frobenius symmetry of the actual K operator -/
noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real Frobenius pairing, bundled in its second argument.-/
def frobInnerCLM (A : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  (show Matrix n n ℂ →ₗ[ℝ] ℝ from
    { toFun := frobInner A
      map_add' := frobInner_add_right A
      map_smul' := fun r B => frobInner_smul_right r A B }).toContinuousLinearMap

/-- The actual stability map preserves the PSD cone. Coefficients may be
indefinite; each sandwich still preserves the cone. Source (F22).
@isnad1 id=possemid.5h5v.s10.bc9042f7e2d8 from=translated src=- shape=2c7a0b80 vocab=dfc2a3af
-/
theorem posSemidef_matrixKStabilityMap
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    (matrixKStabilityMap ν α S P).PosSemidef := by
  rw [matrixKStabilityMap_apply ν hν α S hS hgap P]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply smul_nonneg hα
  apply integral_nonneg_of_ae
  filter_upwards [ν.support_mem_ae] with T hT
  have hC := isHermitian_matrixKCoefficient S T.val hS T.property (hgap T hT)
  change (matrixKCoefficient S T.val * P * matrixKCoefficient S T.val - (0 : Matrix n n ℂ)).PosSemidef
  rw [sub_zero]
  simpa only [hC.eq] using hP.mul_mul_conjTranspose_same (matrixKCoefficient S T.val)

/-- The actual stability operator preserves the real Hermitian vector space.
@isnad1 id=ishermit.5h5v.s10.a8efcb024cee from=translated src=- shape=3b61eaac vocab=7af1f7a1
-/
theorem isHermitian_matrixKStabilityMap
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (matrixKStabilityMap ν α S H).IsHermitian := by
  obtain ⟨P,N,hP,hN,hH',_,_⟩ := exists_posSemidef_parts hH
  rw [hH',map_sub]
  exact (posSemidef_matrixKStabilityMap ν hν α hα S hS hgap hP).isHermitian.sub
    (posSemidef_matrixKStabilityMap ν hν α hα S hS hgap hN).isHermitian

/-- The actual averaged stability operator is symmetric for the real
Frobenius pairing, including for indefinite rational coefficients. Source (F22).
atlas: matrix-k-transform-stability (partial)
@isnad1 id=eq.3h6v.s10.2a915d2caecf from=translated src=- shape=a83e8400 vocab=72450eeb
-/
theorem frobInner_matrixKStabilityMap_comm
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (A B : Matrix n n ℂ) :
    frobInner A (matrixKStabilityMap ν α S B) =
      frobInner (matrixKStabilityMap ν α S A) B := by
  have hi0 := (integrable_matrixK_kernels ν hν S hS hgap).2
  have hi (H : Matrix n n ℂ) : Integrable
      (fun T => matrixKCoefficient S T.val * H * matrixKCoefficient S T.val) ν := by
    simpa only [ContinuousLinearMap.mulLeftRight_apply] using hi0.apply_continuousLinearMap H
  rw [matrixKStabilityMap_apply ν hν α S hS hgap B,
    matrixKStabilityMap_apply ν hν α S hS hgap A,
    frobInner_smul_right,frobInner_smul_left]
  congr 1
  have hleft := (frobInnerCLM A).integral_comp_comm (hi B)
  have hright := (frobInnerCLM B).integral_comp_comm (hi A)
  change (∫ T, frobInner A (matrixKCoefficient S T.val * B * matrixKCoefficient S T.val) ∂ν) =
    frobInner A (∫ T, matrixKCoefficient S T.val * B * matrixKCoefficient S T.val ∂ν) at hleft
  change (∫ T, frobInner B (matrixKCoefficient S T.val * A * matrixKCoefficient S T.val) ∂ν) =
    frobInner B (∫ T, matrixKCoefficient S T.val * A * matrixKCoefficient S T.val ∂ν) at hright
  rw [← hleft,frobInner_comm _ B,← hright]
  apply integral_congr_ae
  filter_upwards [ν.support_mem_ae] with T hT
  rw [frobInner_hermitian_congruence _ A B
    (isHermitian_matrixKCoefficient S T.val hS T.property (hgap T hT)),frobInner_comm]

end NLAlib
