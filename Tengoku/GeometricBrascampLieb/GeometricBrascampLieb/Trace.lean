import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Geometry
import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  (D : Datum ι E F)

/-- Coisometries preserve the trace of a lifted endomorphism. This is the
second-derivative identity used when composing a heat solution with a BL map.
@isnad1 id=eq.0h6v.s12.584e37187f8f from=translated src=- shape=4aa89557 vocab=01320ddd
-/
theorem trace_lift (i : ι) (A : F i →L[ℝ] F i) :
    LinearMap.trace ℝ E ((D.map i).adjoint.comp (A.comp (D.map i))).toLinearMap =
      LinearMap.trace ℝ (F i) A.toLinearMap := by
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
  congr 1
  ext y
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, D.coisometry_apply]

/--
@isnad1 id=eq.0h5v.s12.2742ef772c17 from=translated src=- shape=465c0d6c vocab=7e683263
-/
theorem trace_adjoint_comp (i : ι) :
    LinearMap.trace ℝ E ((D.map i).adjoint.comp (D.map i)).toLinearMap =
      (Module.finrank ℝ (F i) : ℝ) := by
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.coe_id,
    LinearMap.trace_id] using D.trace_lift i (ContinuousLinearMap.id ℝ (F i))

/-- The scaling identity follows from the two geometric identities.
@isnad1 id=eq.0h4v.s8.1f8fbd0bb02f from=translated src=- shape=4929a8c1 vocab=0e728131
-/
theorem dimension_identity :
    ∑ i, D.weight i * (Module.finrank ℝ (F i) : ℝ) = (Module.finrank ℝ E : ℝ) := by
  have h := congrArg (fun A : E →L[ℝ] E => LinearMap.trace ℝ E A.toLinearMap) D.resolution
  simpa only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    map_sum, map_smul, smul_eq_mul, D.trace_adjoint_comp,
    ContinuousLinearMap.coe_id, LinearMap.trace_id] using h

end GeometricBrascampLieb.Datum
