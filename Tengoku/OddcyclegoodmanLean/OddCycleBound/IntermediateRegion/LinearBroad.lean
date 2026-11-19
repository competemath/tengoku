import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.LinearCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/--
@isnad1 id=le.1h1v.s6.15e580f60ce6 from=translated src=- shape=f624ebc9 vocab=23d532ce
-/
theorem sqrt_le_tangent {v : ℝ} (hv : 0 ≤ v) : Real.sqrt v ≤ 2 * v / 3 + 3 / 8 := by
  have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  nlinarith [sq_nonneg (4 * Real.sqrt v - 3), Real.sqrt_nonneg v, hsq]

namespace AdmissibleParams

variable (P : AdmissibleParams)

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
