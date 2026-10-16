import Tengoku.NavierStokesEuler.Euler.MeanSourceVariationalInverse
import Tengoku.NavierStokesEuler.Euler.MeanStrongInverse
import Tengoku.NavierStokesEuler.Euler.MeanBoundaryPhysicalSupport

/-! The actual strong mean inverse under the manuscript's spatial hypotheses. -/

noncomputable section

namespace EulerMeanSourceInverse

open MeasureTheory Set InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanHarmonic EulerMeanBoundary EulerLiftedPressure EulerTimeLp
  EulerMeanVariationalInverse EulerVolterraConvolution
open scoped NNReal

end EulerMeanSourceInverse
