import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.QuadraticBranch
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.EnvelopeEstimates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

noncomputable def chartCxi : Real :=
  Real.sqrt (2 * P.alpha) * (1 + 4 * P.xi) / (2 + 4 * P.xi)

theorem chartCxi_pos : 0 < P.chartCxi := by
  unfold chartCxi
  apply div_pos
  · exact mul_pos (Real.sqrt_pos.2 (mul_pos (by norm_num) P.alpha_pos)) (by linarith [P.xi_pos])
  · linarith [P.xi_pos]

theorem f_eq_alpha_mul : P.f = P.alpha * (1 - P.ell) := by
  unfold f; rw [mul_sub, mul_one, P.alpha_mul_ell]

theorem d_eq_alpha_mul : P.d = P.alpha * P.chartU := by
  unfold d chartU; rw [mul_sub, mul_one, P.alpha_mul_tau]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
