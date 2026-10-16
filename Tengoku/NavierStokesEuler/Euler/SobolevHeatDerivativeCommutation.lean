import Tengoku.NavierStokesEuler.Euler.SobolevLaplacian

/-! Exact heat commutation with the genuine Sobolev derivatives and Laplacian. -/

noncomputable section

namespace EulerSobolevLaplacian

open EulerCylinderSobolevSpace EulerSobolevHeat
open scoped NNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevLaplacian
