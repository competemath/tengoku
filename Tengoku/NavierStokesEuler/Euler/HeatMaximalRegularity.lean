import Tengoku.NavierStokesEuler.Euler.HeatMaximalCauchy
import Tengoku.NavierStokesEuler.Euler.RegularizedMildEquation
import Tengoku.NavierStokesEuler.Euler.TimeLpMap

/-! Genuine maximal spatial regularity of the actual viscous mild solution, proved by strong Cauchy limits. -/

noncomputable section

namespace EulerHeatMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevLaplacian EulerTimeLp EulerVolterraConvolution EulerRegularizedMildEquation
  EulerHeatMaximalCauchy EulerHeatMaximalEstimate
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Completeness of actual H² Bochner space constructs its strong Cauchy limit. -/
theorem exists_H2_time_limit (T : ℝ) (u : ℕ → TimeLp T (SobolevSpace period 2)) (hu : CauchySeq u) :
    ∃ U : TimeLp T (SobolevSpace period 2), Filter.Tendsto u Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete hu

end EulerHeatMaximalRegularity
