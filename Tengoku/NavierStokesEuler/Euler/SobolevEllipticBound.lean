import Tengoku.NavierStokesEuler.Euler.HeatHessianEnergy

/-! A genuine H² bound by H¹ and the cylinder Laplacian, used in strong maximal-regularity limits. -/

noncomputable section

namespace EulerSobolevEllipticBound

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator EulerHeatGradientEnergy

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevEllipticBound
