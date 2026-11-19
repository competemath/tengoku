import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.ParameterFacts
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

/--
@isnad1 id=lt.0h1v.s3.d95e494ae656 from=translated src=- shape=b9369acb vocab=b8fbcb0d
-/
theorem e_pos : 0 < P.e := by
  dsimp [e]
  linarith [P.alpha_lt_half]

/--
@isnad1 id=lt.0h1v.s3.b78a8e564c81 from=translated src=- shape=b9369acb vocab=5485a101
-/
theorem d_pos : 0 < P.d := by
  dsimp [d]
  exact sub_pos.mpr P.alpha_gt_q

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
