import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.ParameterFacts
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem e_pos : 0 < P.e := by
  dsimp [e]
  linarith [P.alpha_lt_half]

theorem d_pos : 0 < P.d := by
  dsimp [d]
  exact sub_pos.mpr P.alpha_gt_q

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
