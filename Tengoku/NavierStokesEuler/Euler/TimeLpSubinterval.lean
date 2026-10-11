import Tengoku.NavierStokesEuler.Euler.TimeLpPairing

/-! Strong Bochner energy passage on every genuine subinterval of the original time interval. -/

noncomputable section

namespace EulerTimeLpSubinterval

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution EulerTimeLpPairing
open scoped Topology

/-- Restrict a genuine scalar L² coefficient to a measurable closed time subinterval. -/
def subintervalWeight (T s t : ℝ) (c : TimeLp T ℝ) : TimeLp T ℝ :=
  (MemLp.indicator measurableSet_Icc (Lp.memLp c)).toLp ((Icc s t).indicator c)

end EulerTimeLpSubinterval
