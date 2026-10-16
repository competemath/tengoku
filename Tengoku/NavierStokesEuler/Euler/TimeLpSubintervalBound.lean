import Tengoku.NavierStokesEuler.Euler.TimeLpSubinterval
import Tengoku.NavierStokesEuler.Euler.PDESubintervalEnergyLimit

/-! Actual L² forcing bounds imply continuous scalar integral majorants on every time subinterval. -/

noncomputable section

namespace EulerTimeLpSubintervalBound

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution EulerTimeLpSubinterval
  EulerPDESubintervalEnergyLimit

/-- The actual continuous scalar right-hand side after an almost-everywhere forcing estimate. -/
def scalarEnergyRhs (T : ℝ) (a b k X Y F : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  a*X+b*Y+k*F

end EulerTimeLpSubintervalBound
