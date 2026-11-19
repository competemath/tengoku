import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.QuadraticBranch
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.EnvelopeEstimates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

noncomputable def chartCxi : Real :=
  Real.sqrt (2 * P.alpha) * (1 + 4 * P.xi) / (2 + 4 * P.xi)

/--
@isnad1 id=lt.0h1v.s3.293a6e6fd62d from=translated src=- shape=b9369acb vocab=374a0a3b
-/
theorem chartCxi_pos : 0 < P.chartCxi := by
  unfold chartCxi
  apply div_pos
  · exact mul_pos (Real.sqrt_pos.2 (mul_pos (by norm_num) P.alpha_pos)) (by linarith [P.xi_pos])
  · linarith [P.xi_pos]

/--
@isnad1 id=eq.0h1v.s4.a755e5219ed6 from=translated src=- shape=7e34bfcc vocab=7dd4206a
-/
theorem f_eq_alpha_mul : P.f = P.alpha * (1 - P.ell) := by
  unfold f; rw [mul_sub, mul_one, P.alpha_mul_ell]

/--
@isnad1 id=eq.0h1v.s4.aedcf1394570 from=translated src=- shape=c45662b3 vocab=e7bab405
-/
theorem d_eq_alpha_mul : P.d = P.alpha * P.chartU := by
  unfold d chartU; rw [mul_sub, mul_one, P.alpha_mul_tau]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
