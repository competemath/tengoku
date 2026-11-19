import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.Chart
import Tengoku.Seed.Algebra.Ring.GeomSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

/--
@isnad1 id=eq.0h1v.s4.55d9e475003d from=translated src=- shape=9fc36aa0 vocab=c37d47b3
-/
theorem chartSigma_eq_one_add (P : AdmissibleParams) : P.chartSigma = 1 + P.chartV := by
  unfold chartV chartSigma; ring

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
