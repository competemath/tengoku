import Tengoku.NavierStokesEuler.Euler.TimeLp

/-! Exact bounded-map compatibility for the actual continuous-path to Bochner L² inclusion. -/

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution
open scoped Topology ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Applying a bounded spatial map commutes exactly with the genuine L² time embedding. -/
theorem pathLp_map (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F) (f : C(Icc (0 : ℝ) T, E)) :
    A.compLpL 2 (timeMeasure T) (pathLp T hT f) =
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (pathLp T hT f), pathLp_ae T hT f,
    pathLp_ae T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)] with t h1 h2 h3
  rw [h1, h2, h3]
  rfl

end EulerTimeLp
